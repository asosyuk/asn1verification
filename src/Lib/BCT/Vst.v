Require Import Core.Core Core.Tactics Core.VstTactics Core.StructNormalizer
        (* Core.SepLemmas *)
        VstLib ErrorWithWriter BCT.Exec.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_decoder.
Require Import VST.ASN__STACK_OVERFLOW_CHECK
    BFT.Vst BFL.Vst   
 (* ber_fetch_tag ber_fetch_length *) Lib.Forward. 
Require Import Core.VstTactics Core.Notations.

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

(*
Instance Change1 : change_composite_env CompSpecs ber_fetch_tag.CompSpecs.
Proof. make_cs_preserve CompSpecs ber_fetch_tag.CompSpecs. Defined.

Instance Change2 : change_composite_env ber_fetch_tag.CompSpecs CompSpecs.
Proof. make_cs_preserve ber_fetch_tag.CompSpecs CompSpecs. Defined.

Instance Change3 : change_composite_env CompSpecs ber_fetch_length.CompSpecs.
Proof. make_cs_preserve CompSpecs ber_fetch_length.CompSpecs. Defined.

Instance Change4 : change_composite_env ber_fetch_length.CompSpecs CompSpecs.
Proof. make_cs_preserve ber_fetch_length.CompSpecs CompSpecs. Defined.
*)
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
                             tag_mode size Int.modulus with
           | Some v => 
             data_at Tsh asn_dec_rval_s 
                     (mk_dec_rval 0 v) res_p *
             data_at Tsh tint (Vint (Int.repr v)) last_length_p
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
    forward_if (opt_codec_ctx_p <> nullval).
  + forward_empty_while.
  assert (opt_codec_ctx_p <> nullval) as ON.
  { break_if; try nia.
    eassumption. }
  rewrite_if_b. clear H H'.
  remember (Int.sign_ext 16 (Int.repr 0)) as st. 
  forward_if True; try contradiction.
  * forward.
    entailer!.
  * forward_if (temp _t'2 Vzero);
      try forward; try entailer!.
    forward_if_add_sep (data_at Tsh (Tstruct _asn_dec_rval_s noattr)
       (Vint (Int.repr 2), Vint (Int.repr 0)) v_rval) v_rval; 
      try forward; try entailer!.
    repeat forward. 
    (* failing asn_overflow check *)
    assert (ber_check_tags_primitive ptr td max_stack_size
                           0 size 0 = None) as N.
       { admit. }
    erewrite N.
    entailer!. 
  + forward.
    entailer!. 
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
       cbn in H0.
       unfold sem_cast_i2bool in H0.
       unfold Val.of_bool in H0.
       destruct (Int.repr 0 == Int.repr (len (tags td)))%int eqn : S.
       cbn in H0.
       eapply int_eq_e in S.
       erewrite <- H5 in *.
       discriminate.
       cbn in H0.
       setoid_rewrite if_true in H0.
       discriminate.
       auto.
       forward.
       forward_if True.
       forward.
       entailer!.
       admit. (* assert_fail *)
       entailer!.
     (* MAIN LOOP *)
       
  (*      match goal with
       | [ _ : _ |-  semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) ?C ?Post ] =>
         let Q' := remove_LOCAL _tagno Q in
         replace Q with Q'
        end. *)
        
       match goal with
       | [ _ : _ |-  semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) ?C ?Post ] =>
       (*  let Q' := remove_LOCAL _tagno Q in
         let Q'' := remove_LOCAL _step Q' in *)
         forward_loop (PROPx P (LOCALx Q (SEPx R)))
                      continue: 
                                (PROPx P (LOCALx Q (SEPx R)))
                             break: (
     let (tag_len, tlv_tag) := Exec.ber_fetch_tags ptr size 0 (sizeof tuint) in
     let (len_len, tlv_len) := Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 
                                                  (size - 1) (sizeof tuint) Int.modulus in
     PROP (True)
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
         entailer!.
       +++ (* forward.
           forward_if.
           2:
             { forward.
               repeat break_let.
               entailer!.
               (* LI -> break *)
               admit.
               admit.
           } 
           (* ptr_b : block, ptr_ofs : ptrofs, ptr_v : list Z, size : Z, 
         tag_p : val, tag_v : Z *)
           destruct ptr_p; try contradiction.
           forward_call (b, i, ptr, size, v_tlv_tag). 
           admit. (* BFT PRE  - add to the BCT PRE *)
           replace (fst (Exec.ber_fetch_tags ptr 0 size 0 (sizeof tuint)))
             with 1. (* FIXME : forward switch doesn't work with complex terms *)
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
               remember (Vptr b i) as ptr_p.
               assert_PROP (ptr_p = field_address (tarray tuchar (len ptr)) [ArraySubsc 0] ptr_p).
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
        *** forward_if True.
            forward.
            entailer!.
            discriminate.
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
               admit.  }  
             forward.
             forward_if.
             ++ (* RC_FAIL case *) 
               forward_empty_while.
               admit. (* as before *)
             ++ forward.
                entailer!.
         *** forward.
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
             ++++ 
              (* size : Z, data : list Z,
         isc : Z, buf_b : block, buf_ofs : ptrofs, res_v : Z, res_ptr : val *)
                forward_call (0, offset_val 1 ptr_p, size - 1, 
                             sublist 1 (len ptr) ptr, v_tlv_len).
                entailer!.
                replace (data_at Tsh (tarray tuchar (len ptr)) (map Vubyte (map Byte.repr ptr)) 
                                 (Vptr b i))
                        with
                          (data_at Tsh tuchar 
                                   (Znth 0 (map Vubyte (map Byte.repr ptr)) ) (Vptr b i)).
                unfold Frame.
                match goal with
                | [ _ : _ |- ?S |-- _ ] => instantiate (1 := [S])
                end.
                simpl.
                entailer!.
                admit. (* FIXME *) 
                admit.
                admit.
                Intros v.
                erewrite H4.
                replace (fst
                       (Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 
                          (size - 1) (sizeof tuint) 1))
                  with 1.
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
                 (* no indefinite length; contradiction *)
                 admit.
                 forward_if True; try contradiction.
                 forward.
                 entailer!.
                 forward_if True; try contradiction.
                 forward.
                 forward.
                 forward_if.
                 (* RC_FAIL *)
                 admit.
                 forward.
                 entailer!.
                 admit. (* FIXME *)
                 discriminate.
                 (* ADVANCE *)
                 match goal with
                 | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                   forward_empty_while_break Pre
                 end.
                 repeat forward.
                 entailer!.
                 admit.
                 forward_if.
                 forward.
                 entailer!.
                 admit.
                 admit.
                 forward.
                 entailer!.
                 admit.
                 admit.
                 admit.
    * admit. *) admit.
       +++  (* CONTINUE  to LI *)
        (* forward.
          forward.
          entailer!.
          admit. *)
         admit.
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
                    Int.modulus = Some (z + z1)) as B.
          {  unfold ber_check_tags_primitive.
             erewrite Heqp.
             replace z with 1.
             erewrite Heqp0.
             break_if.
             cbn.
             assert (negb (z0 =? nth 0 (tags td) 0) = false) as F.
             (* add to forward_if *)
             admit.
             erewrite F.
             break_if.
             admit.
             (* add to forward_if or loop *)
             break_if.
             admit.
             auto. 
             admit. 
             admit. }
          erewrite B.
          entailer!.
          admit. (* change POSTC *)
Admitted.

End Ber_check_tags.
