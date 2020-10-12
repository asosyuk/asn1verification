Require Import Core.Core Core.Tactics Core.VstTactics Core.StructNormalizer
        (* Core.SepLemmas *)
        VstLib ErrorWithWriter BCT.Exec.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_decoder.
Require Import VST.ASN__STACK_OVERFLOW_CHECK
    BFT.Vst BFL.Vst   
 (* ber_fetch_tag ber_fetch_length *) Lib.Forward. 
Require Import Core.VstTactics Core.Notations.
Require Import  Clight.ber_decoder.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section Ber_check_tags.

Instance Change1 : change_composite_env CompSpecs BFT.Vst.CompSpecs.
Proof. make_cs_preserve CompSpecs BFT.Vst.CompSpecs. Defined.

Instance Change2 : change_composite_env  BFT.Vst.CompSpecs CompSpecs.
Proof. make_cs_preserve  BFT.Vst.CompSpecs CompSpecs. Defined.

Instance Change3 : change_composite_env CompSpecs BFL.Vst.CompSpecs.
Proof. make_cs_preserve CompSpecs BFL.Vst.CompSpecs. Defined.

Instance Change4 : change_composite_env BFL.Vst.CompSpecs CompSpecs.
Proof. make_cs_preserve BFL.Vst.CompSpecs CompSpecs. Defined.

Definition ber_check_tags_spec : ident * funspec :=
  DECLARE _ber_check_tags
    WITH opt_codec_ctx_p : val, opt_codec_ctx : val,
         td_p : val, td : TYPE_descriptor, 
         tags_p : val,
         opt_ctx_p : val,
         ptr_p : val, ptr : list Z,
         res_p : val,
         size : Z, tag_mode : Z, last_tag_form : Z,
         last_length_p : val,
         opt_tlv_form_p : val,
         max_stack_size : Z
    PRE [tptr asn_dec_rval_s, tptr (Tstruct _asn_codec_ctx_s noattr),
         tptr (Tstruct _asn_TYPE_descriptor_s noattr),
         tptr (Tstruct _asn_struct_ctx_s noattr), 
         tptr tvoid, tuint, tint, tint, tptr tint, tptr tint]
      PROP (tag_mode = 0;
            last_tag_form = 0;
            0 < len ptr;
            (Znth 0 ptr) & 32 = 0;
            nullval = opt_ctx_p;
            nullval = opt_tlv_form_p;
            1 = len (tags td);
            isptr ptr_p)
      PARAMS (res_p; opt_codec_ctx_p; td_p; opt_ctx_p; ptr_p; 
                Vint (Int.repr size);
                Vint (Int.repr tag_mode); Vint (Int.repr last_tag_form);
                  last_length_p; opt_tlv_form_p)
      GLOBALS ()
      SEP (data_at Tsh (tarray tuchar (len ptr)) 
                   (map Vubyte (map Byte.repr ptr)) ptr_p;
           field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) 
                         [StructField _tags] 
                         tags_p td_p;
           field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) 
                         [StructField _tags_count] 
                         (Vint (Int.repr (Zlength (tags td)))) td_p;
           data_at Tsh (tarray tuint (Zlength (tags td))) 
                   (map Vint (map Int.repr (tags td))) tags_p;
           data_at_ Tsh asn_dec_rval_s res_p;
           data_at_ Tsh tint last_length_p;
           data_at Tsh (Tstruct _asn_codec_ctx_s noattr) 
                   (Vint (Int.repr (max_stack_size))) opt_codec_ctx_p)
    POST [tvoid]
      PROP ()
      LOCAL ()
      SEP (data_at Tsh (tarray tuchar (len ptr)) (map Vubyte (map Byte.repr ptr)) ptr_p;
           field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) 
                         [StructField _tags] 
                         tags_p td_p;
           field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) 
                         [StructField _tags_count] 
                         (Vint (Int.repr (Zlength (tags td)))) td_p;
           data_at Tsh (tarray tuint (Zlength (tags td))) 
                   (map Vint (map Int.repr (tags td))) tags_p;
           data_at Tsh (Tstruct _asn_codec_ctx_s noattr) 
                  (Vint (Int.repr (max_stack_size))) opt_codec_ctx_p;
        match ber_check_tags_primitive ptr td max_stack_size
                              size (sizeof tuint) Int.modulus with
           | Some v => 
             data_at Tsh asn_dec_rval_s 
                     (mk_dec_rval 0 (snd v)) res_p *
             data_at Tsh tint (Vint (Int.repr (fst v))) last_length_p
           | None => 
             data_at Tsh asn_dec_rval_s (mk_dec_rval 2 0) res_p *
             data_at_ Tsh tint last_length_p
        end).

Definition Gprog := ltac:(with_library prog 
                                       [ber_check_tags_spec;
                                        ber_fetch_tag_spec;
                                        ber_fetch_len_spec;
                                        ASN__STACK_OVERFLOW_CHECK_spec]).

Theorem bool_der_encode : 
  semax_body Vprog Gprog
             (normalize_function f_ber_check_tags composites) 
             ber_check_tags_spec.
Proof.
  start_function.
  subst.
  repeat forward.
  forward_if (temp _t'1 Vzero).
  contradiction.
  - forward.
    entailer!.
  - forward.
    forward_call (opt_codec_ctx_p, max_stack_size).
      assert (-1 <= ASN__STACK_OVERFLOW_CHECK 0 max_stack_size <= 0) as A.
    { unfold ASN__STACK_OVERFLOW_CHECK.
      repeat break_if; lia. }
    forward_if [opt_codec_ctx_p <> nullval;
                (if eq_dec opt_codec_ctx_p nullval
                 then 0
                 else ASN__STACK_OVERFLOW_CHECK 0 max_stack_size) = 0].
             (*  [opt_codec_ctx_p <> nullval (* \/ 
                ASN__STACK_OVERFLOW_CHECK 0 max_stack_size =? 0 = false *)]. *)
  + forward_empty_while.
  assert (opt_codec_ctx_p <> nullval) as ON.
  { break_if; try nia.
    eassumption. }
  rewrite_if_b. 
  forward_if True; try contradiction.
  * forward.
    entailer!.
  * forward_if (temp _t'2 Vzero);
      try forward; try entailer!.
    forward_if_add_sep (data_at Tsh (Tstruct _asn_dec_rval_s noattr)
       (Vint (Int.repr 2), Vint (Int.repr 0)) v_rval) v_rval; 
      try forward; try entailer!.
    repeat forward. 
    assert (ber_check_tags_primitive ptr td max_stack_size
                            size (sizeof tuint) Int.modulus = None) as N.
       { unfold ber_check_tags_primitive.
         assert (ASN__STACK_OVERFLOW_CHECK 0 max_stack_size =? 0 = false) 
           as AS by (Zbool_to_Prop;
                    eassumption).
         erewrite AS.
         auto. }
    erewrite N.
    entailer!. 
  + forward.    
    entailer!.
    apply repr_inj_signed.
    repeat break_if; try rep_omega.
    rep_omega.
    eassumption.
  + forward_if
      (temp _t'4 Vzero); try congruence.
  -- forward.
     entailer!.
  -- forward.
     forward_if (temp _t'10 
                  ((force_val
                  (sem_cast tint tbool
                  (eval_binop Oeq tint tint
                    (Vint
                       (Int.repr 0))
                    (eval_cast tuint tint (Vint (Int.repr (len (tags td))))))))
                   )); try discriminate.
     --- forward.
         forward.
         entailer!. 
     ---
       Arguments eq_dec : simpl never.
       forward_if True.
       cbn in H3.
       unfold sem_cast_i2bool in H3.
       unfold Val.of_bool in H3.
       destruct (Int.repr 0 == Int.repr (len (tags td)))%int eqn : S.
       cbn in H3.
       eapply int_eq_e in S.
       erewrite <- H5 in *.
       discriminate.
       cbn in H3.
       setoid_rewrite if_true in H3.
       discriminate.
       auto.
       forward.
       forward_if True.
       forward.
       entailer!.
       admit. (* assert_fail *)
       entailer!.
     (* MAIN LOOP *)       
     (* match goal with
       | [ _ : _ |-  semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) ?C ?Post ] =>
         let Q' := remove_LOCAL _tagno Q in
         replace Q with Q'
        end. *)
       rewrite H0.

       match goal with
       | [ _ : _ |-  semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) ?C ?Post ] =>
       (*  let Q' := remove_LOCAL _tagno Q in
         let Q'' := remove_LOCAL _step Q' in *)
         forward_loop (
     EX z : Z,
     let (tag_len, tlv_tag) := Exec.ber_fetch_tags ptr size 0 (sizeof tuint) in
     let (len_len, tlv_len) := Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 
                                                  (size - tag_len) (sizeof tuint) Int.modulus in
     let ll := if z =? 0 then -1 else (tlv_len + tag_len + len_len)%Z in
     let cm := if z =? 0 then 0 else (tag_len + len_len)%Z in 
     PROP ((* 0 < tag_len;
           0 < len_len;
           0 < tlv_len;
           tag_len <> 0;
           len_len <> -1;
           len_len <> 0;
           tlv_tag = nth O (tags td) 0 *))
     LOCAL (temp _t'10
              (force_val
                 (sem_cast tint tbool
                    (eval_binop Oeq tint tint (Vint (Int.repr 0))
                       (eval_cast tuint tint (Vint (Int.repr (len (tags td))))))));
     temp _tagno (Vint (Int.repr z));
     temp _t'4 Vzero;
     temp _t'3 (Vint (Int.repr 0));
     temp _step (Vint (Int.repr z)); 
     temp _t'1 Vzero; 
     temp _tlv_constr (Vint (Int.repr (if z =? 0 then -1 else 0)));
     temp _expect_00_terminators (Vint (Int.repr 0));
     temp _limit_len (Vint (Int.repr ll)); 
     temp _consumed_myself (Vint (Int.repr cm));
     lvar _rval__12 (Tstruct _asn_dec_rval_s noattr) v_rval__12;
     lvar _rval__11 (Tstruct _asn_dec_rval_s noattr) v_rval__11;
     lvar _rval__10 (Tstruct _asn_dec_rval_s noattr) v_rval__10;
     lvar _rval__9 (Tstruct _asn_dec_rval_s noattr) v_rval__9;
     lvar _rval__8 (Tstruct _asn_dec_rval_s noattr) v_rval__8;
     lvar _rval__7 (Tstruct _asn_dec_rval_s noattr) v_rval__7;
     lvar _rval__6 (Tstruct _asn_dec_rval_s noattr) v_rval__6;
     lvar _rval__5 (Tstruct _asn_dec_rval_s noattr) v_rval__5;
     lvar _rval__4 (Tstruct _asn_dec_rval_s noattr) v_rval__4;
     lvar _rval__3 (Tstruct _asn_dec_rval_s noattr) v_rval__3;
     lvar _rval__2 (Tstruct _asn_dec_rval_s noattr) v_rval__2;
     lvar _rval__1 (Tstruct _asn_dec_rval_s noattr) v_rval__1;
     lvar _rval (Tstruct _asn_dec_rval_s noattr) v_rval; 
     lvar _tlv_len tint v_tlv_len;
     lvar _tlv_tag tuint v_tlv_tag; 
     temp __res res_p; temp _opt_codec_ctx opt_codec_ctx_p;
     temp _td td_p; temp _opt_ctx nullval;
     temp _ptr (offset_val cm  ptr_p);
     temp _size (Vint (Int.repr (size - cm)));
     temp _tag_mode (Vint (Int.repr 0));
     temp _last_tag_form (Vint (Int.repr 0));
     temp _last_length last_length_p;
     temp _opt_tlv_form nullval)
     SEP (data_at Tsh (Tstruct _asn_codec_ctx_s noattr)
                  (Vint (Int.repr max_stack_size))
            opt_codec_ctx_p;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__12;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__11;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__10;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__9;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__8;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__7;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__6;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__5;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__4;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__3;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__2;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__1;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval;
     if z =? 0 then (data_at_ Tsh tint v_tlv_len *
                     data_at_ Tsh tuint v_tlv_tag)
     else (data_at Tsh tint (Vint (Int.repr tlv_len)) v_tlv_len *
                     data_at Tsh tuint (Vint (Int.repr tlv_tag)) v_tlv_tag);
     data_at Tsh (tarray tuchar (len ptr)) 
             (map Vubyte (map Byte.repr ptr)) ptr_p;
     field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p;
     field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
       (Vint (Int.repr (len (tags td)))) td_p;
     data_at Tsh (tarray tuint (len (tags td))) 
             (map Vint (map Int.repr (tags td))) tags_p;
     data_at_ Tsh asn_dec_rval_s res_p; 
     data_at_ Tsh tint last_length_p))%assert
                      (* CONTINUE *)
                      continue:
           (let (tag_len, tlv_tag) := Exec.ber_fetch_tags ptr size 0 (sizeof tuint) in
       let (len_len, tlv_len) :=
         Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 (size - tag_len) 
           (sizeof tuint) Int.modulus in
       PROP ( )
       LOCAL (temp _t'10
                (force_val
                   (sem_cast tint tbool
                      (eval_binop Oeq tint tint (Vint (Int.repr 0))
                         (eval_cast tuint tint (Vint (Int.repr (len (tags td))))))));
       temp _tagno (Vint (Int.repr 1)); temp _t'4 Vzero; temp _t'3 (Vint (Int.repr 0));
       temp _step (Vint (Int.repr 1)); temp _t'1 Vzero;
       temp _tlv_constr (Vint (Int.repr (0)));
       temp _expect_00_terminators (Vint (Int.repr 0));
       temp _limit_len (Vint (Int.repr ((tlv_len + tag_len + len_len)%Z)));
       temp _consumed_myself (Vint (Int.repr ((tag_len + len_len)%Z)));
       lvar _rval__12 (Tstruct _asn_dec_rval_s noattr) v_rval__12;
       lvar _rval__11 (Tstruct _asn_dec_rval_s noattr) v_rval__11;
       lvar _rval__10 (Tstruct _asn_dec_rval_s noattr) v_rval__10;
       lvar _rval__9 (Tstruct _asn_dec_rval_s noattr) v_rval__9;
       lvar _rval__8 (Tstruct _asn_dec_rval_s noattr) v_rval__8;
       lvar _rval__7 (Tstruct _asn_dec_rval_s noattr) v_rval__7;
       lvar _rval__6 (Tstruct _asn_dec_rval_s noattr) v_rval__6;
       lvar _rval__5 (Tstruct _asn_dec_rval_s noattr) v_rval__5;
       lvar _rval__4 (Tstruct _asn_dec_rval_s noattr) v_rval__4;
       lvar _rval__3 (Tstruct _asn_dec_rval_s noattr) v_rval__3;
       lvar _rval__2 (Tstruct _asn_dec_rval_s noattr) v_rval__2;
       lvar _rval__1 (Tstruct _asn_dec_rval_s noattr) v_rval__1;
       lvar _rval (Tstruct _asn_dec_rval_s noattr) v_rval; lvar _tlv_len tint v_tlv_len;
       lvar _tlv_tag tuint v_tlv_tag; temp __res res_p; temp _opt_codec_ctx opt_codec_ctx_p;
       temp _td td_p; temp _opt_ctx nullval;
       temp _ptr (offset_val ((tag_len + len_len)%Z) ptr_p);
       temp _size (Vint (Int.repr (size - ((tag_len + len_len)%Z))));
       temp _tag_mode (Vint (Int.repr 0)); temp _last_tag_form (Vint (Int.repr 0));
       temp _last_length last_length_p; temp _opt_tlv_form nullval)
       SEP (data_at Tsh (Tstruct _asn_codec_ctx_s noattr) (Vint (Int.repr max_stack_size))
              opt_codec_ctx_p; data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__12;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__11;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__10;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__9;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__8;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__7;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__6;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__5;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__4;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__3;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__2;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__1;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval;
        data_at Tsh tint (Vint (Int.repr tlv_len)) v_tlv_len ;
        data_at Tsh tuint (Vint (Int.repr tlv_tag)) v_tlv_tag;
       data_at Tsh (tarray tuchar (len ptr)) (map Vubyte (map Byte.repr ptr)) ptr_p;
       field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p;
       field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
         (Vint (Int.repr (len (tags td)))) td_p;
       data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
       data_at_ Tsh asn_dec_rval_s res_p; data_at_ Tsh tint last_length_p))
                             break: (
     let (tag_len, tlv_tag) := Exec.ber_fetch_tags ptr size 0 (sizeof tuint) in
     let (len_len, tlv_len) := Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 
                                                  (size - tag_len) (sizeof tuint) Int.modulus in
     PROP (0 < tag_len;
           0 < len_len;
           0 < tlv_len;
           tag_len <> 0;
           len_len <> -1;
           len_len <> 0;
           tlv_tag = nth O (tags td) 0)
     LOCAL (temp _t'10
              (force_val
                 (sem_cast tint tbool
                    (eval_binop Oeq tint tint (Vint (Int.repr 0))
                       (eval_cast tuint tint (Vint (Int.repr (len (tags td))))))));
     temp _tagno (Vint (Int.repr 1));
     temp _t'4 Vzero;
     temp _t'3 (Vint (Int.repr (if eq_dec opt_codec_ctx_p nullval 
                                then 0 else -1)));
     temp _step (Vint (Int.repr 1)); 
     temp _t'1 Vzero; 
     temp _tlv_constr (Vint (Int.repr 0));
     temp _expect_00_terminators (Vint (Int.repr 0));
     temp _limit_len (Vint (Int.neg (Int.repr (tlv_len + tag_len + len_len)))); 
     temp _consumed_myself (Vint (Int.repr (tag_len + len_len)));
     lvar _rval__12 (Tstruct _asn_dec_rval_s noattr) v_rval__12;
     lvar _rval__11 (Tstruct _asn_dec_rval_s noattr) v_rval__11;
     lvar _rval__10 (Tstruct _asn_dec_rval_s noattr) v_rval__10;
     lvar _rval__9 (Tstruct _asn_dec_rval_s noattr) v_rval__9;
     lvar _rval__8 (Tstruct _asn_dec_rval_s noattr) v_rval__8;
     lvar _rval__7 (Tstruct _asn_dec_rval_s noattr) v_rval__7;
     lvar _rval__6 (Tstruct _asn_dec_rval_s noattr) v_rval__6;
     lvar _rval__5 (Tstruct _asn_dec_rval_s noattr) v_rval__5;
     lvar _rval__4 (Tstruct _asn_dec_rval_s noattr) v_rval__4;
     lvar _rval__3 (Tstruct _asn_dec_rval_s noattr) v_rval__3;
     lvar _rval__2 (Tstruct _asn_dec_rval_s noattr) v_rval__2;
     lvar _rval__1 (Tstruct _asn_dec_rval_s noattr) v_rval__1;
     lvar _rval (Tstruct _asn_dec_rval_s noattr) v_rval; 
     lvar _tlv_len tint v_tlv_len;
     lvar _tlv_tag tuint v_tlv_tag; 
     temp __res res_p; temp _opt_codec_ctx opt_codec_ctx_p;
     temp _td td_p; temp _opt_ctx nullval;
     temp _ptr (offset_val (tag_len + len_len) ptr_p);
     temp _size (Vint (Int.repr (size - tag_len - len_len)));
     temp _tag_mode (Vint (Int.repr 0));
     temp _last_tag_form (Vint (Int.repr 0));
     temp _last_length last_length_p;
     temp _opt_tlv_form nullval)
     SEP (data_at Tsh (Tstruct _asn_codec_ctx_s noattr)
                  (Vint (Int.repr max_stack_size))
            opt_codec_ctx_p;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__12;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__11;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__10;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__9;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__8;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__7;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__6;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__5;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__4;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__3;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__2;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__1;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval;
     data_at Tsh tint (Vint (Int.repr tlv_len)) v_tlv_len;
     data_at Tsh tuint (Vint (Int.repr tlv_tag)) v_tlv_tag;
     data_at Tsh (tarray tuchar (len ptr)) 
             (map Vubyte (map Byte.repr ptr)) ptr_p;
     field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p;
     field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
       (Vint (Int.repr (len (tags td)))) td_p;
     data_at Tsh (tarray tuint (len (tags td))) 
             (map Vint (map Int.repr (tags td))) tags_p;
     data_at_ Tsh asn_dec_rval_s res_p; 
     data_at_ Tsh tint last_length_p))
       end.
       +++ (* Pre -> LI *)
         Exists 0.
         repeat rewrite_if_b.
         repeat break_let.
         entailer!.
         apply derives_refl.
       +++ Intros z.
           repeat break_let.
           break_if.
           * simpl.
             Intros.
             Zbool_to_Prop.
             forward.
           forward_if.
           2: (* LI -> break *) lia. 
           destruct ptr_p; try contradiction.
           forward_call (b, i, ptr, size, v_tlv_tag). 
           admit. (* BFT PRE  - add to the BCT PRE *)           
           replace (fst (Exec.ber_fetch_tags ptr size 0 (sizeof tuint)))
             with 65. (* FIXME : forward switch doesn't work with complex terms *)
           (* in VST 2.6 forward_switch needs change and can fail here *)
           match goal with
           | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
             forward_switch Pre
           end. 
           *** (* RC_FAIL  *)             
             admit.
           ***  (* RC_FAIL *)
             admit.
           *** forward.
               entailer!. 
           *** remember (map Vubyte (map Byte.repr ptr)) as ptr'.
               normalize.
               assert_PROP ((Vptr b i) = 
                            field_address (tarray tuchar (len ptr)) [ArraySubsc 0] (Vptr b i)).
               { entailer!.
                 rewrite field_address_offset.
                 cbn.
                 normalize.
                 econstructor.
                 auto.
                 repeat split; auto; try nia.
                 cbn.
                 admit.
                 constructor.
                 admit. }                 
               Intros.
               normalize.
               forward.
               entailer!.
               repeat erewrite Znth_map; auto.
               cbn.
               strip_repr.
               nia.
               forward_if (temp _t'13 Vzero).
             ** admit. (* contradiction *)
             ** forward. entailer!.
             ** forward.
                forward_if
                  (temp _t'15 Vzero); try contradiction;
                  try forward; try entailer!; rewrite_if_b; try entailer!.
                forward_if True; try nia. (* TODO *)
                forward_if True.
                forward.
                entailer!.
                nia.
                forward.
                forward. 
                normalize.
                assert_PROP (force_val (sem_add_ptr_int tuint Signed tags_p (Vint 0%int))
                             = field_address (tarray tuint (len (tags td)))
                                             [ArraySubsc 0] tags_p).
                { entailer!.
                  rewrite field_address_offset.
                  unfold sem_add_ptr_int.
                  unfold complete_type.
                  unfold tuint.
                  admit.
                  econstructor.
                  auto.
                  cbn.
                  repeat split; auto; cbn; try nia.
                  unfold size_compatible.
                  break_match; auto.
                  admit.
                  admit. }  
                forward.
                forward_if.
             ++ (* RC_FAIL case *) 
               forward_empty_while.
               admit. (* as before *)
             ++ forward.
                entailer!.
             ++  forward.
                 forward_if True.
                 ++++
               forward_if; try congruence.
               **** (* RC_FAIL case *)
                 forward_empty_while.
                 admit.
               ****
                 forward.
                 entailer!.
             ++++ forward_if (temp _t'18 Vzero); try congruence.
                  forward.
                  entailer!.
                  forward_if.
                  (* RC_FAIL *)
                  admit.
                  forward; entailer!.
             ++++ remember 65 as tag_len.
              (* size : Z, data : list Z,
                 isc : Z, buf_b : block, buf_ofs : ptrofs,      
                 res_v : Z, res_ptr : val *)   
                erewrite   Heqptr'.
               replace (data_at Tsh (tarray tuchar (len ptr))
                       (map Vubyte (map Byte.repr ptr)) (Vptr b i))
                       with
                        (data_at Tsh tuchar (Vubyte (Byte.repr (Znth 0 ptr)))
                                   (Vptr b i) * 
                         data_at Tsh (tarray tuchar (len ptr - 1)) 
                                 (map Vubyte (map Byte.repr (sublist 1 (len ptr) ptr)))
                                   (Vptr b (i + Ptrofs.repr tag_len)%ptrofs))%logic.             
                forward_call (0, Vptr b (i + Ptrofs.repr tag_len)%ptrofs, size - tag_len, 
                             sublist 1 (len ptr) ptr, v_tlv_len).
                unfold Frame.
                instantiate (1 := 
  [data_at Tsh tuchar (Vubyte (Byte.repr (Znth 0 ptr))) (Vptr b i) *
   data_at Tsh tuint (Vubyte (Byte.repr 
                 (snd (Exec.ber_fetch_tags ptr size 0 (sizeof tuint)))))
     v_tlv_tag *
   data_at Tsh (Tstruct _asn_codec_ctx_s noattr) (Vint (Int.repr max_stack_size)) 
           opt_codec_ctx_p *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__12 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__11 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__10 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__9 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__8 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__7 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__6 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__5 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__4 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__3 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__2 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__1 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval *
   field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p *
   field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
     (Vint (Int.repr (len (tags td)))) td_p *
   data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p *
   data_at_ Tsh asn_dec_rval_s res_p * data_at_ Tsh tint last_length_p]%logic).
                simpl.
                entailer!.
                autorewrite with sublist.
                entailer!.
                repeat split.
                admit. 
                admit. (* add size restriction *)
                Intros v.
                erewrite H7.
                replace (fst
                       (Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 
                          (size - tag_len) (sizeof tuint) Int.modulus))
                  with 99.
                 match goal with
                 | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                   forward_switch Pre
                 end.
                 admit. (* RC_FAIL *)
                 admit. (* RC_FAIL *)
                 forward.
                 entailer!.
                 forward.
                 forward_if.
                 admit. (* no indefinite length - see ber_fetch_length spec *)
                 forward_if True; try contradiction.
                 forward.
                 entailer!.
                 forward_if (temp _limit_len
           (Vint
              (Int.repr
                 (Byte.unsigned
                    (Byte.repr
                       (snd
                          (Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 
                             (size - tag_len) (sizeof tuint) Int.modulus)))) + 
               Int.repr tag_len + Int.repr 99)%int)); try contradiction.
                 forward.
                 forward.
                 forward_if (temp _limit_len
           (Vint
              (Int.repr
                 (Byte.unsigned
                    (Byte.repr
                       (snd
                          (Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 
                             (size - tag_len) (sizeof tuint) Int.modulus)))) + 
               Int.repr tag_len + Int.repr 99)%int)); try contradiction.
                 (* RC_FAIL *)
                 admit. (* as before *)
                 forward.
                 entailer!.
                 entailer!.
                 discriminate.
                 (* ADVANCE *)
                 match goal with
                 | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                   forward_empty_while_break Pre
                 end.
                 unfold POSTCONDITION.
                 unfold abbreviate.
                 repeat forward.
                 entailer!.
                 admit. (* ??? *)
                 forward_if.
                 forward.
                 entailer!.
                 admit. (* ??? *)
                 (* true  *)
                  admit.
                 forward.
                 entailer!.
                 admit.
                 (* true  *)
                 admit.
                 admit.
                 admit.
                 *** admit.
           * Zbool_to_Prop.
             (* z <> 0 *)
             admit.
      +++  (* CONTINUE  to LI *)
          repeat break_let.
          forward.
          forward.
          Exists 2.
          repeat rewrite_if_b.
          repeat break_let.
          entailer!.
          break_if; Zbool_to_Prop; try lia.
          entailer!.         
      +++ repeat break_let.
          forward_if True; try contradiction.
          forward.
          entailer!.
          
          forward_if_add_sep (data_at Tsh tint (Vint (Int.repr z2)) last_length_p) 
                             last_length_p; try contradiction.
          forward.
          forward.
          entailer!.
          (* RETURN OK *)
          forward_empty_while.
          forward_if True; try contradiction.
          forward.
          entailer!.
          forward_if (temp _t'25 Vone); try contradiction.
          forward.
          entailer!.
          discriminate.
          forward_if_add_sep
            (data_at Tsh (Tstruct _asn_dec_rval_s noattr)
                     (Vint (Int.repr 0), (Vint (Int.repr (z + z1))))
                     v_rval__12) v_rval__12. 
          forward.
          entailer!. 
          discriminate.
          repeat forward.
          assert (ber_check_tags_primitive
                    ptr td max_stack_size size (sizeof tuint)
                    Int.modulus = Some (z2, z + z1)) as B.
          {  unfold ber_check_tags_primitive.             
             erewrite Heqp.
             erewrite Heqp0.
             repeat rewrite_if_b.            
             repeat break_if;
               try destruct_orb_hyp;
               repeat rewrite_if_b; symmetry; repeat Zbool_to_Prop;
                 try lia; auto. }
          erewrite B.
          entailer!.
Admitted.

End Ber_check_tags.
