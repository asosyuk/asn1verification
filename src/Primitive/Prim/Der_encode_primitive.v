Require Import Core.Core Lib.Lib Core.StructNormalizer 
        VstLib Prim.Exec Lib.Callback.Dummy Lib.DWT.Vst.
Require Import VST.floyd.proofauto.
Require Import Clight.dummy Clight.asn_codecs_prim.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

(* DWT compspecs *)
Instance Change1 : change_composite_env CompSpecs Vst.CompSpecs.
Proof. make_cs_preserve CompSpecs Vst.CompSpecs. Defined.

Instance Change2 : change_composite_env Vst.CompSpecs CompSpecs.
Proof. make_cs_preserve Vst.CompSpecs CompSpecs. Defined.

(* Callback compspecs *)
Instance Change3 : change_composite_env Dummy.CompSpecs CompSpecs.
Proof. make_cs_preserve Dummy.CompSpecs CompSpecs. Defined.

Instance Change4 : change_composite_env CompSpecs Dummy.CompSpecs.
Proof. make_cs_preserve CompSpecs Dummy.CompSpecs. Defined.

Section Der_encode_primitive.

Definition prim_enc_rval size td li td_p sptr_p := 
  if size <? 0
  then mk_enc_rval (-1) td_p sptr_p
  else match evalErrW (primitive_encoder td li) [] with
       | Some v => mk_enc_rval (encoded v) Vzero Vzero
       | None => mk_enc_rval (-1) td_p sptr_p
       end.

Definition dwt_res td :=
  match execErrW (Exec.der_write_tags td) [] with
  | Some v => v
  | None => []
  end.

Definition prim_enc_res td li := 
  match execErrW (primitive_encoder td li) [] with
  | Some v => v
  | None => []
  end.

Definition prim_type_s := (Tstruct _ASN__PRIMITIVE_TYPE_s noattr).
Definition mk_prim_type_s (buf_p : val) size := (buf_p, Vint (Int.repr size)).

Definition der_primitive_encoder_spec : ident * funspec :=
  DECLARE _der_encode_primitive
    WITH res_p : val,  
         sptr_p : val, buf_p : val,
         size : Z, data : list byte,
         td_p : val, td : TYPE_descriptor,
         tag_mode : Z, tag : Z, cb_encoded : Z,
         cb_p : val, app_key_p : val
    PRE [tptr enc_rval_s, tptr type_descriptor_s, tptr tvoid, tint, tuint, 
          tptr cb_type, tptr tvoid]
      PROP (is_pointer_or_null buf_p;
            is_pointer_or_null cb_p;
            Zlength data = size;
            0 <= size <= Int.max_unsigned;
            Int.min_signed <=
            Int.signed (Int.repr (match evalErrW (Exec.der_write_tags td) [] with
                                  | Some v => encoded v
                                  | None => -1 end)) +
            Int.signed (Int.repr size) <= Int.max_signed;
            Int.min_signed <= 
            Int.signed (Int.repr (match evalErrW (primitive_encoder td data) [] with
                                  | Some v => encoded v
                                  | None => -1 end)) + 
            Int.signed (Int.repr size) <= Int.max_signed)
      PARAMS (res_p; td_p; sptr_p; Vint (Int.repr tag_mode);
              Vint (Int.repr tag); cb_p; app_key_p)
      GLOBALS ()
      SEP (data_at_ Tsh enc_rval_s res_p;
           data_at_ Tsh type_descriptor_s td_p; 
           (* sptr *)
           valid_pointer buf_p;
           data_at Tsh (tarray tuchar size) (map Vubyte data) buf_p;
           field_at Tsh prim_type_s (DOT _buf) buf_p sptr_p;
           field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p;
           (* Callback *)
           data_at_ Tsh tvoid app_key_p;
           valid_pointer cb_p)
    POST [tvoid]
      PROP ()
      LOCAL ()
      SEP (data_at_ Tsh type_descriptor_s td_p;
           (* sptr *)
           valid_pointer buf_p;
           data_at Tsh (tarray tuchar size) (map Vubyte data) buf_p;
           field_at Tsh prim_type_s (DOT _buf) buf_p sptr_p;
           field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p;
           (* Result *)
           data_at Tsh enc_rval_s (prim_enc_rval size td data td_p sptr_p) res_p;
           (* Callback *)
           valid_pointer cb_p;
           data_at_ Tsh tvoid app_key_p;
           func_ptr' dummy_callback_spec cb_p).

Definition Gprog := ltac:(with_library prog [der_primitive_encoder_spec; 
                                             der_write_tags_spec]).

Ltac forward_empty_loop :=
      match goal with
      | [ _ : _ |- semax _ ?Pre (Ssequence (Sloop Sskip Sbreak) _) _ ] =>
          forward_loop Pre break: Pre; try forward ; try entailer! 
      end. 

Lemma eval_dwt_prim_enc_none : forall td d,
    evalErrW (Exec.der_write_tags td) [] = None ->
    evalErrW (primitive_encoder td d) [] = None.
Proof.
  intros.
  unfold primitive_encoder, Exec.der_write_tags in *.
  break_match_hyp; unfold evalErrW in *; cbn in *.
  all: try reflexivity.
  discriminate.
Qed.

Lemma eval_dwt_prim_enc_some : forall td d a,
    evalErrW (Exec.der_write_tags td) [] = Some a ->
    evalErrW (primitive_encoder td d) [] = Some (encode (Zlength d + encoded a)).
Proof.
  intros.
  unfold primitive_encoder, Exec.der_write_tags in *.
  break_match_hyp; unfold evalErrW in *; cbn in *.
  all: try discriminate.
  inversion H.
  cbn.
  reflexivity.
Qed.

Theorem der_encode_primitive : semax_body Vprog Gprog 
                                          (normalize_function f_der_encode_primitive 
                                                              composites) 
                                          der_primitive_encoder_spec.
Proof.
  start_function. 
  rename H into IspnBuf; rename H0 into IspnCb.
  forward.
  forward_empty_loop.
  forward_call (td_p, td, size, tag_mode, 0, tag, app_key_p, cb_p).
  forward.
  forward_empty_loop.
  forward_if.
  * (* erval.encoded = -1 (encoding error) *)
    repeat forward.
    rewrite H.
    entailer!.
    assert (T : evalErrW (Exec.der_write_tags td) [] = None).
    { break_match_hyp.
      unfold Exec.der_write_tags in Heqo.
      break_match_hyp; cbn in Heqo; try congruence.
      inversion Heqo.
      subst; cbn in H.
      discriminate.
      reflexivity. }
    unfold prim_enc_rval.
    rewrite eval_dwt_prim_enc_none by assumption.
    break_if; entailer!.
  * (* erval.encoded <> -1 *)
    destruct (evalErrW (Exec.der_write_tags td) []) eqn:T.
    2 : { unfold Int.neg in H.
          replace (Int.repr 1) with (Int.one) in H by reflexivity. 
          rewrite Int.unsigned_one in H.
          replace (- (1)) with (-1) in H by lia.
          assert (Int.repr (-1) = Int.repr (-1)) by f_equal.
          congruence. }
    forward_if (
      PROP () 
      LOCAL (temp _t'4 (if Val.eq cb_p nullval 
                        then Vzero 
                        else force_val (sem_cast (tptr tuchar) tbool buf_p));
             temp _t'11 buf_p; temp _st sptr_p; temp _td td_p; temp _sptr sptr_p;
             lvar _erval (Tstruct _asn_enc_rval_s noattr) v_erval; 
             temp __res res_p; temp _cb cb_p; temp _app_key app_key_p)
      SEP (data_at_ Tsh type_descriptor_s td_p; data_at_ Tsh tvoid app_key_p;
           func_ptr' dummy_callback_spec cb_p;
           data_at Tsh (Tstruct _asn_enc_rval_s noattr)
                   (Vint (Int.repr (encoded a)), (Vundef, Vundef)) v_erval;
           data_at_ Tsh enc_rval_s res_p; valid_pointer buf_p;
           data_at Tsh (tarray tuchar size) (map Vubyte data) buf_p;
           field_at Tsh prim_type_s (DOT _buf) buf_p sptr_p;
           field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p; 
           valid_pointer cb_p)).
    - (* if cb_p <> nullval *)
      repeat forward.
      unfold isptr in H0.
      destruct cb_p; try lia.
      destruct (Val.eq (Vptr b i) nullval).
      unfold nullval in e; cbn in e; congruence.
      entailer!.
    - (* if cb_p = nullval *)
      forward.
      destruct (Val.eq cb_p nullval); [| congruence].
      entailer!.
    - (* after (if cb_p) *)
      forward_if (
          (PROP () 
          LOCAL (temp _t'4 (if Val.eq cb_p nullval
                            then Vzero
                            else force_val (sem_cast (tptr tuchar) tbool buf_p)); 
                 temp _t'11 buf_p; temp _st sptr_p; 
                 lvar _erval (Tstruct _asn_enc_rval_s noattr) v_erval; 
                 temp __res res_p; temp _cb cb_p; temp _app_key app_key_p)
          SEP (data_at_ Tsh type_descriptor_s td_p; data_at_ Tsh tvoid app_key_p;
               func_ptr' dummy_callback_spec cb_p;
               data_at Tsh (Tstruct _asn_enc_rval_s noattr)
                       (Vint (Int.repr (encoded a)), (Vundef, Vundef)) v_erval;
               data_at_ Tsh enc_rval_s res_p; valid_pointer buf_p;
               data_at Tsh (tarray tuchar size) (map Vubyte data) buf_p;
               field_at Tsh prim_type_s (DOT _buf) buf_p sptr_p;
               field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p; 
               valid_pointer cb_p)))%assert.
      + (* buf_p <> nullval *)
        destruct (Val.eq cb_p nullval).
        unfold typed_true, strict_bool_val in H0; cbn in H0; 
          rewrite Int.eq_true in H0; discriminate.
        repeat forward.
        forward_call (buf_p, size, app_key_p).
        forward_if.
        repeat forward.
        unfold prim_enc_rval.
        destruct (Zlength data =? 0) eqn:q.
        entailer!.
        unfold typed_true, Val.of_bool, Int.lt, zlt in H5.
        cbn in H5.
        destruct Z_lt_dec in H5; 
          [|cbn in H5; rewrite Int.eq_true in H5; cbn in H5; congruence].
        assert (F : Zlength data < 0).
        rewrite Int.signed_repr in l by admit.
        rewrite Int.signed_repr in l by rep_omega.
        assumption; lia.
        lia.
        forward.
        entailer!.
        entailer!.
      + (* buf_p = nullval *)
        forward.
        forward_if (
            PROP ( )
            LOCAL (temp _t'3 (if Val.eq buf_p nullval
                              then (force_val 
                                      (sem_cast tint tbool 
                                                (eval_binop Oeq tuint tint 
                                                            (Vint (Int.repr size)) 
                                                            (Vint (Int.repr 0)))))
                              else Vint Int.one);
                   temp _t'4 (if Val.eq cb_p nullval
                              then Vzero
                              else force_val (sem_cast (tptr tuchar) tbool buf_p));
                   temp _t'7 buf_p; temp _t'4 Vzero; 
                   temp _t'11 buf_p; temp _st sptr_p; temp _td td_p; temp _sptr sptr_p;
                   lvar _erval (Tstruct _asn_enc_rval_s noattr) v_erval; temp __res res_p; 
                   temp _cb cb_p; temp _app_key app_key_p)
            SEP (data_at_ Tsh type_descriptor_s td_p; data_at_ Tsh tvoid app_key_p;
                 func_ptr' dummy_callback_spec cb_p;
                 data_at Tsh (Tstruct _asn_enc_rval_s noattr)
                         (Vint (Int.repr (encoded a)), (Vundef, Vundef)) v_erval; 
                 data_at_ Tsh enc_rval_s res_p;
                 valid_pointer buf_p; data_at Tsh (tarray tuchar size) 
                                              (map Vubyte data) buf_p;
                 field_at Tsh prim_type_s (DOT _buf) buf_p sptr_p;
                 field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p; 
                 valid_pointer cb_p)).
        ++ (* buf_p <> nullval *)
          forward.
          destruct (Val.eq buf_p nullval).
          unfold isptr in H5; unfold nullval in e; cbn in e; rewrite e in H5; 
            exfalso; assumption.
          destruct (Val.eq cb_p nullval); entailer!.
          unfold typed_false, strict_bool_val in H0.
          cbn in H0.
          break_match_hyp; try congruence.
          destruct (Int.eq i Int.zero) eqn:z in H0.
          apply int_eq_e in z.
          rewrite z; reflexivity.
          cbn in H0; congruence.
        ++ (* buf_p = nullval *)
          repeat forward.
          destruct (Val.eq buf_p nullval); [|congruence].
          destruct (Val.eq cb_p nullval); entailer!.
        ++ (* after *)
          admit.
      + (* after *)
        repeat forward.
        forward_loop (
            PROP ( )
            LOCAL (temp _t'6 (Vint (Int.repr size)); 
                   temp _t'5 (Vint (Int.repr (encoded a)));
                   temp _t'4
                        (if Val.eq cb_p nullval
                         then Vzero
                         else force_val (sem_cast (tptr tuchar) tbool buf_p)); 
                   temp _t'11 buf_p;
                   temp _st sptr_p; lvar _erval (Tstruct _asn_enc_rval_s noattr) v_erval;
                   temp __res res_p; temp _cb cb_p; temp _app_key app_key_p)
            SEP (data_at_ Tsh type_descriptor_s td_p; data_at_ Tsh tvoid app_key_p;
                 func_ptr' dummy_callback_spec cb_p;
                 data_at Tsh (Tstruct _asn_enc_rval_s noattr)
                         (Vint (Int.add (Int.repr (encoded a)) (Int.repr size)), 
                          (Vundef, Vundef)) v_erval;
                 data_at_ Tsh enc_rval_s res_p; valid_pointer buf_p;
                 data_at Tsh (tarray tuchar size) (map Vubyte data) buf_p;
                 field_at Tsh prim_type_s (DOT _buf) buf_p sptr_p;
                 field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p; 
                 valid_pointer cb_p)).
        entailer!.
        repeat forward.
        unfold prim_enc_rval.
        entailer!.
        admit.
Admitted.

End Der_encode_primitive.

