Require Import Core.Core Core.Tactics Core.VstTactics Core.StructNormalizer
        (* Core.SepLemmas *)
        VstLib ErrorWithWriter BCT.Exec.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_decoder.
Require Import VST.ASN__STACK_OVERFLOW_CHECK ber_fetch_tag ber_fetch_length Lib.Forward. 
Require Import Core.VstTactics Core.Notations.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section Ber_check_tags.

Instance Change1 : change_composite_env CompSpecs ber_fetch_tag.CompSpecs.
Proof. make_cs_preserve CompSpecs ber_fetch_tag.CompSpecs. Defined.

Instance Change2 : change_composite_env ber_fetch_tag.CompSpecs CompSpecs.
Proof. make_cs_preserve ber_fetch_tag.CompSpecs CompSpecs. Defined.

Instance Change3 : change_composite_env CompSpecs ber_fetch_length.CompSpecs.
Proof. make_cs_preserve CompSpecs ber_fetch_length.CompSpecs. Defined.

Instance Change4 : change_composite_env ber_fetch_length.CompSpecs CompSpecs.
Proof. make_cs_preserve ber_fetch_length.CompSpecs CompSpecs. Defined.

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
            len ptr = 1;
            (Znth 0 ptr) & 32 = 0;
            nullval = opt_ctx_p;
            nullval = opt_tlv_form_p;
            1 = len (tags td))
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
           data_at Tsh (tarray tint (Zlength (tags td))) 
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
           data_at Tsh (tarray tint (Zlength (tags td))) 
                   (map Vint (map Int.repr (tags td))) tags_p;
           data_at Tsh (Tstruct _asn_codec_ctx_s noattr) 
                  (Vint (Int.repr (max_stack_size))) opt_codec_ctx_p;
        match ber_check_tags ptr td max_stack_size
                             tag_mode size 0 with
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
                                        ber_fetch_length_spec;
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
    assert (ber_check_tags ptr td max_stack_size
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
       (* contradiction *)
       admit.
       cbn in H0.
       setoid_rewrite if_true in H0.
       discriminate.
       auto.
       forward.
       forward_if True.
       forward.
       entailer!.
       admit.
       entailer!.
     (* MAIN LOOP *)
       match goal with
       | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
         forward_loop Pre
                      continue: Pre
                             break: Pre
       end.
       +++ (* Pre -> LI *) 
         entailer!.
       +++ forward.
           forward_if.
           2:
             { forward.
               entailer!. } 
           forward_call (ptr_p, size, v_tlv_tag).             
           match goal with
           | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
             forward_switch Pre
           end.
    * (* RC_FAIL *)
      admit.
    *  (* RC_FAIL *)
      admit.
    * forward.
      entailer!. (* break *)
    * remember (map Vubyte (map Byte.repr ptr)) as ptr'.
      assert_PROP (ptr_p = field_address (tarray tuchar (len ptr)) [ArraySubsc 0] ptr_p).
      { entailer!.
        rewrite field_address_offset.
        cbn.
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
             pose (t := Vzero).
             replace (data_at_ Tsh tuint v_tlv_tag) 
               with (data_at Tsh tuint Vzero v_tlv_tag).
             (* FIXME: ber_fetch_tag modifies v_tlv_tag *)
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
             replace (data_at Tsh (tarray tint (len (tags td))) 
                              (map Vint (map Int.repr (tags td))) tags_p)
             with (data_at Tsh (tarray tuint (len (tags td))) 
                              (map Vint (map Int.repr (tags td))) tags_p).
               
             forward.
             forward_if.
             ++ (* RC_FAIL case *) 
               forward_empty_while.
               admit. (* as before *)
             ++ forward.
                entailer!.
                admit. (* fix tags_p type to tuint in PRE *)
             ++ admit.
             ++ admit.
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
                forward_call (0, offset_val 1 ptr_p, size - 1, v_tlv_len).
                entailer!.
                Intros v.
                erewrite H4.
                 match goal with
                 | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                   forward_switch Pre
                 end.
                 admit. (* RC_FAIL *)
                 admit. (* RC_FAIL *)
                 forward.
                 entailer!.
                  replace (@data_at_ ber_fetch_length.CompSpecs Tsh tuint v_tlv_len) 
                    with (data_at Tsh tuint Vzero v_tlv_len).
             (* FIXME: ber_fetch_len modifies v_tlv_tag *)
                 forward.
                 admit.
                 forward_if.
             admit. 
             forward.
             forward.
             entailer!.
             Intros.
             forward.
             admit.
             forward_if (temp _t'16 Vzero).
    * forward. admit.
    * forward. admit.
    * forward.
      forward_if (temp _t'18 Vone).
      ** forward. admit.
      ** forward. admit.
      ** forward_if True.
         *** forward.
             admit.
         *** 
           forward_if True.
           forward.
           admit.
           admit.
           forward.
           forward.
           assert ((force_val
                      (both_int (fun n1 n2 : int => Some (Vint (Int.add n1 n2))) sem_cast_pointer
                                sem_cast_pointer
                                (if Memory.EqDec_val ctx_s_p nullval
                                 then Vint (Int.repr 0)
                                 else Vint (Int.repr step)) (Vint (Int.repr (-1))))) = Vzero) as V. admit.
           rewrite V.
           assert ((let (x, _) := let (_, y) := let (_, y) := let (_, y) := t in y in y in y in x) = buf_p) as VV. admit.
           setoid_rewrite VV.
           forward.
           
           forward.
           forward.
           
           admit.
           forward.
           entailer!. (* break *)
  + forward.
    admit.
    destruct (eq_dec ctx_s_p nullval).
    forward.
    admit.
    deadvars!.
    forward.
    admit.
    Time entailer!. 
    admit.
  + deadvars!.
    
    
    
    forward_if True.
    admit.
    admit.
    forward.
    entailer!.
    admit.
    
    (* forward_if_add_sep (data_at Tsh (Tstruct _asn_struct_ctx_s noattr) c ctx_s_p) 
                                     ctx_s_p. *)
    forward_if True.
    forward.
    nia.
    forward.
    admit.
    forward.
    entailer!.
    (* RETURN(RC_OK) *)
    forward_empty_while.
    forward_if True.
    forward.
    entailer!.
    admit.
    forward.
    entailer!.
    forward_if (temp _t'29 Vone).
    forward.
    entailer!.
    discriminate.
    forward_if True. (* change rval_16 - why 16??? *)
    forward.
    entailer!.
    discriminate.
    forward.
    repeat forward.
    (* postcondition *)
    entailer!.
    assert (ber_check_tags buf td ctx_Z tag_mode size step = Some 0) as S.
    admit.
    erewrite S.
    entailer!.
    
    (*
                    data_at Tsh (Tstruct _asn_dec_rval_s noattr) 
                    (Vint (Int.repr 0), Vint (Int.repr 0)) v_rval__16 *)
    
    list_solve.
    list_simplify
      
      admit.
  + admit.
  + 
Admitted.

End Ber_check_tags.
