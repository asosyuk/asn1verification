Require Import Core.Core Core.Tactics Core.VstTactics Core.StructNormalizer
        Core.SepLemmas 
        VstLib ErrorWithWriter BCT.Exec.
Require Import VST.floyd.proofauto.
Require Import VST.ASN__STACK_OVERFLOW_CHECK (* BFT.Vst BFL.Vst *) Lib.Forward. 
Require Import Core.VstTactics Core.Notations.
Require Import ber_fetch_tag  Clight.ber_decoder.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section Ber_check_tags.

Record asn_struct_ctx_type_abstract := 
  {  phase : Z;		
     step : Z;
     step_short : -32768 <= step <= 32767;
     context : Z;
     pt : block * ptrofs;
     left : Z }. 

Definition asn_struct_ctx_composites :=
  ((_phase, tshort) :: (_step, tshort) :: (_context, tint) ::
    (_ptr, (tptr tvoid)) :: (_left, tint) :: nil).

Fixpoint mk_struct_repr (ls : list (ident * type))  :=
  match ls with
    | [] => val
    | [h] => let (_, t) := h in reptype t
    | h :: tl => let (_, t) := h in
                (reptype t * mk_struct_repr tl)%type
  end.  

Definition asn_struct_ctx_type := mk_struct_repr asn_struct_ctx_composites.

Instance Change1 : change_composite_env CompSpecs ber_fetch_tag.CompSpecs.
Proof. make_cs_preserve CompSpecs ber_fetch_tag.CompSpecs. Defined.

Instance Change2 : change_composite_env ber_fetch_tag.CompSpecs CompSpecs.
Proof. make_cs_preserve ber_fetch_tag.CompSpecs CompSpecs. Defined.

(*
Instance Change1 : change_composite_env CompSpecs BFT.Vst.CompSpecs.
Proof. make_cs_preserve CompSpecs BFT.Vst.CompSpecs. Defined.

Instance Change2 : change_composite_env BFT.Vst.CompSpecs CompSpecs.
Proof. make_cs_preserve BFT.Vst.CompSpecs CompSpecs. Defined.

Instance Change3 : change_composite_env CompSpecs BFL.Vst.CompSpecs.
Proof. make_cs_preserve CompSpecs BFL.Vst.CompSpecs. Defined.

Instance Change4 : change_composite_env BFL.Vst.CompSpecs CompSpecs.
Proof. make_cs_preserve BFL.Vst.CompSpecs CompSpecs. Defined.  *)

Definition ber_check_tags_spec : ident * funspec :=
  DECLARE _ber_check_tags
    WITH opt_codec_ctx_p : val, opt_codec_ctx : val,
         td_p : val, td : TYPE_descriptor, 
         tags_p : val,
         opt_ctx_p : val,
         opt_ctx : asn_struct_ctx_type_abstract,                         
         ptr_p : val, ptr : list Z,
         res_p : val,
         size : Z, tag_mode : Z, last_tag_from : Z,
         last_length_p : val,
         opt_tlv_form_p : val,
         max_stack_size : Z
    PRE [tptr asn_dec_rval_s, tptr (Tstruct _asn_codec_ctx_s noattr),
         tptr (Tstruct _asn_TYPE_descriptor_s noattr),
         tptr (Tstruct _asn_struct_ctx_s noattr), 
         tptr tvoid, tuint, tint, tint, tptr tint, tptr tint]
      PROP ()
      PARAMS (res_p; opt_codec_ctx_p; td_p; opt_ctx_p; ptr_p; 
                Vint (Int.repr size);
                Vint (Int.repr tag_mode); Vint (Int.repr last_tag_from);
                  last_length_p; opt_tlv_form_p)
      GLOBALS ()
      SEP (data_at Tsh (tarray tuchar (len ptr)) (map Vubyte (map Byte.repr ptr)) ptr_p;
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
           data_at Tsh (Tstruct _asn_struct_ctx_s noattr) 
                   (Vint (Int.repr (phase opt_ctx)), 
                    (Vint (Int.repr (step opt_ctx)),
                     (Vint (Int.repr (context opt_ctx)), 
                      (Vptr (fst (pt opt_ctx)) (snd (pt opt_ctx)),
                       Vint (Int.repr (left opt_ctx))))))
                   opt_ctx_p;
           data_at Tsh (Tstruct _asn_codec_ctx_s noattr) 
                   (Vint (Int.repr (max_stack_size))) opt_codec_ctx_p)
    POST [tvoid]
    EX st : int,
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
           data_at Tsh (Tstruct _asn_struct_ctx_s noattr) 
                   (Vint (Int.repr (phase opt_ctx)), 
                    (Vint st, (* saving context *)
                     (Vint (Int.repr (context opt_ctx)), 
                      (Vptr (fst (pt opt_ctx)) (snd (pt opt_ctx)),
                       Vint (Int.repr (left opt_ctx))))))
                   opt_ctx_p;
        match ber_check_tags ptr td max_stack_size
                             tag_mode size (step opt_ctx) with
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
                                        (* ber_fetch_len_spec; *)
                                        ASN__STACK_OVERFLOW_CHECK_spec]).

Theorem bool_der_encode : 
  semax_body Vprog Gprog
             (normalize_function f_ber_check_tags composites) 
             ber_check_tags_spec.
Proof.
  start_function.
  repeat forward.
  pose proof (step_short opt_ctx) as S.
  forward_if (temp _t'1 (Vint (Int.repr (if eq_dec opt_ctx_p nullval 
                         then 0
                         else step opt_ctx)))); try forward; try entailer!.
  - 
 (* forward.
  rewrite if_false.                                     
  entailer!.
  { destruct opt_ctx_p; cbn in H; try (contradiction || discriminate). } *)
  admit.
  -
  forward_call (opt_codec_ctx_p, max_stack_size).
  forward_if (opt_codec_ctx_p <> nullval).
  + 
 (* forward_empty_while.
  assert (opt_codec_ctx_p <> nullval) as ON.
  { break_if; try nia.
    eassumption. }
  rewrite_if_b. clear H H'.
    remember (Int.sign_ext 16
           (Int.repr (if Memory.EqDec_val opt_ctx_p nullval 
                      then 0 
                      else step opt_ctx))) as st. 
  
  forward_if_add_sep (data_at Tsh (Tstruct _asn_struct_ctx_s noattr)
       (Vint (Int.repr (phase opt_ctx)),
       (Vint (if eq_dec opt_ctx_p nullval 
              then Int.repr (step opt_ctx) else st),
       (Vint (Int.repr (context opt_ctx)),
       (Vptr (fst (pt opt_ctx)) (snd (pt opt_ctx)), Vint (Int.repr (left opt_ctx))))))
       opt_ctx_p) opt_ctx_p. 
  * forward.
    entailer!.
    destruct opt_ctx_p; try contradiction.
    repeat rewrite if_false by discriminate.
    entailer!.
  * forward.
    repeat rewrite_if_b.
    entailer!.
  * forward_if (temp _t'2 (force_val (sem_cast_i2bool opt_ctx_p)));
      try forward; try entailer!.
    forward_if_add_sep (data_at Tsh (Tstruct _asn_dec_rval_s noattr)
       (Vint (Int.repr 2), Vint (Int.repr 0)) v_rval) v_rval; 
      try forward; try entailer!.
    repeat forward. 
    (* failing asn_overflow check *)
    assert (ber_check_tags ptr td max_stack_size tag_mode size (step opt_ctx) = None) as N.
       { admit. }
    erewrite N.
    Exists (if eq_dec opt_ctx_p nullval
            then Int.repr (step opt_ctx)
            else
              Int.sign_ext 16
                           (Int.repr (if Memory.EqDec_val opt_ctx_p nullval 
                                      then 0
                                      else step opt_ctx))).
    entailer!. *) admit.
  + 
   (* forward.
   entailer!.   *) admit.
  + forward_if
      (temp _t'4 (Vint (Int.repr (if eq_dec (Int.repr tag_mode) (Int.repr 1)
                                  then -1 else 0)))).
  -- (* forward.
     entailer!.
     rewrite_if_b.
     auto.  *) admit.
  -- (* forward.
     entailer!.
     rewrite_if_b.
     auto. *) admit.
  -- forward.
    (* entailer!. 
     { repeat break_if; strip_repr. } *) admit.
     forward_if (temp _t'10 
                  (if eq_dec (Int.repr tag_mode) Int.zero 
                   then
                  (force_val
                  (sem_cast tint tbool
                  (eval_binop Oeq tint tint
                    (Vint
                       (Int.repr (if eq_dec opt_ctx_p nullval
                                  then 0 
                                  else step opt_ctx) +
                        Int.repr (if eq_dec (Int.repr tag_mode) (Int.repr 1)
                                  then -1 
                                  else 0))%int)
                    (eval_cast tuint tint (Vint (Int.repr (len (tags td))))))))
                   else (Vint (Int.repr 0)))).
     --- (* forward.
         forward.
         rewrite H0.
         entailer!.  *) admit.
     --- (* forward.
         entailer!.
         rewrite_if_b.
         auto. *) admit.
     ---
       Arguments eq_dec : simpl never.
       remember (if eq_dec (Int.repr tag_mode) 0%int
               then
                force_val
                  (sem_cast tint tbool
                     (eval_binop Oeq tint tint
                        (Vint
                           (Int.repr (if eq_dec opt_ctx_p nullval 
                                      then 0 else step opt_ctx) +
                            Int.repr (if eq_dec (Int.repr tag_mode) (Int.repr 1) 
                                      then -1 else 0))%int)
                        (eval_cast tuint tint (Vint (Int.repr (len (tags td)))))))
               else Vint (Int.repr 0)) as t12.  
       remember (if eq_dec 
                            (Vint (Int.repr (Byte.unsigned (Byte.repr (Znth 0 ptr)) & 32)))
                            (Vint 0%int)
                       then Vzero
                       else Vone) as tlv_constr.
         (* TODO: exec specs for ber_fetch_tags 
     and ber_fetch_length *)
         pose (tag_len := 1).
         pose (len_len := 1).
         pose (num := tag_len + len_len).
         forward_if [temp _tag_len (Vint (Int.repr tag_len));
                     temp _len_len (Vint (Int.repr len_len));
                     temp _tlv_constr tlv_constr;
                     temp _ptr (offset_val num ptr_p);
                     temp _size (Vint (Int.repr (size - num)));
                     temp _consumed_myself (Vint (Int.repr num))].
         ++ 
         (* ptr_b : block, ptr_ofs : ptrofs, ptr_v : list Z, size : Z, 
            tag_p : val, tag_v : Z *)
            forward_call (ptr_p, size, v_tlv_tag).
            change_compspecs ber_fetch_tag.CompSpecs.
            match goal with
            | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                forward_switch Pre
              end. 

            forward_call (ptr_p, ptr, size, v_tlv_tag, 0).
            
(*            Ltac forward_switch' := 
 match goal with
| |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Sswitch ?e _) _ => 
  fail 1 "BLA"
(*  let sign := constr:(signof e) in let sign := eval hnf in sign in
   let HRE := fresh "H" in let v := fresh "v" in
    evar (v: val);
    do_compute_expr1 Delta P Q R e v HRE;
    simpl in v;
    let n := fresh "n" in evar (n: int); 
    let H := fresh in assert (H: v=Vint n) by (unfold v,n; reflexivity);
    let A := fresh in 
    match goal with |- ?AA => set (A:=AA) end;
    revert n H; normalize; intros n H; subst A;
    let n' := fresh "n" in pose (n' := Int.unsigned n); 
    let H' := fresh in assert (H': n = Int.repr n');
    [try (symmetry; apply Int.repr_unsigned) 
       | rewrite H,H' in HRE; clear H H';
         subst n' n v; 
         rewrite (Int.repr_unsigned (Int.repr _)) in HRE;
          eapply semax_switch_PQR ; 
           [reflexivity | check_typecheck | exact HRE 
           | clear HRE; unfold select_switch at 1; unfold select_switch_default at 1;
             try match goal with H := @abbreviate statement _ |- _ => clear H end;
             process_cases sign ] 
] *)

| _ => fail 1 "Not found"

end. *)

Ltac forward_switch' := match goal with 
                        | _ : _ |- _ => idtac
                        end.

            Ltac forward_switch post :=
              check_Delta; check_POSTCONDITION;
              repeat (apply -> seq_assoc; abbreviate_semax);
              repeat apply -> semax_seq_skip;
              first [ignore (post: environ->mpred)
                    | fail 1 
                           "Invariant (first argument to forward_if) 
                           must have type (environ->mpred)"];
              match goal with
              | |- semax _ _ (Ssequence (Sswitch _ _) _) _ => 
                apply semax_seq with post; 
                forward_switch'
(*
                [forward_switch' 
                | abbreviate_semax; 
                  simpl_ret_assert (*autorewrite with ret_assert*)] *)
                idtac
              | |- semax _ _ (Sswitch _ _) _ =>
                forward_switch'   
end.
            Forward.forward_switch (PROP()LOCAL()SEP()).
            match goal with
            | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                forward_switch Pre
              end. 
         * (* Case 0 *)
           (* clear E.
            abbreviate_semax.
            match goal with
            | [ _ : _ |- semax _ ?Pre (Sloop _ Sbreak) ?Post ]  => 
              forward_loop Pre break: Pre; try forward ; try entailer! 
            | [ _ : _ |- semax _ ?Pre (Ssequence (Sloop _ Sbreak) _) ?Post ] =>
              forward_loop Pre break: Pre; try forward ; try entailer! 
            end. 
            repeat rewrite_if_b. 
            remember (Int.sign_ext 16
           (Int.repr (if Memory.EqDec_val opt_ctx_p nullval 
                      then 0 
                      else step opt_ctx))) as st. 
  
            forward_if_add_sep (data_at Tsh (Tstruct _asn_struct_ctx_s noattr)
                                        (Vint (Int.repr (phase opt_ctx)),
                                         (Vint (if eq_dec opt_ctx_p nullval 
                                                then Int.repr (step opt_ctx) else st),
                                          (Vint (Int.repr (context opt_ctx)),
                                           (Vptr (fst (pt opt_ctx)) (snd (pt opt_ctx)), 
                                            Vint (Int.repr (left opt_ctx))))))
                                        opt_ctx_p) opt_ctx_p.
        ** forward.
           entailer!.
           destruct opt_ctx_p; try contradiction.
           repeat rewrite if_false by discriminate.
           entailer!.
        ** forward.
           repeat rewrite_if_b.
           entailer!.
        ** (*forward_if (temp _t'6 (force_val (sem_cast_i2bool opt_ctx_p)));
             try forward; try entailer!.
           forward_if_add_sep (data_at Tsh (Tstruct _asn_dec_rval_s noattr)
                                       (Vint (Int.repr 2), 
                                        Vint (Int.repr 0)) v_rval__1) v_rval__1; 
           try forward; try entailer!.
           repeat forward. 
           (* failing asn_overflow check *)
           assert (ber_check_tags ptr td max_stack_size tag_mode size (step opt_ctx) = None) as N.
           { admit. }
           erewrite N.
           Exists (if eq_dec opt_ctx_p nullval
                   then Int.repr (step opt_ctx)
                   else
                     Int.sign_ext 16
                                  (Int.repr (if Memory.EqDec_val opt_ctx_p nullval 
                                             then 0
                                             else step opt_ctx))).
           entailer!. *) *) admit.
         * (* same as before *) admit.
         * (* forward.
              entailer!. *) admit.
         * 
           remember (map Vubyte (map Byte.repr ptr)) as ptr'.
           assert (0 < len ptr) as T by admit.
           replace (data_at Tsh (tarray tuchar (len ptr)) ptr' ptr_p) with
               (data_at Tsh tuchar (Znth 0 ptr') ptr_p *
                       data_at Tsh (tarray tuchar (len ptr - 1))
                               (sublist 1 (len ptr) ptr') 
                               (offset_val 1 ptr_p))%logic.
              Intros.
              forward.
              entailer!.
              repeat erewrite Znth_map. 
              cbn. autorewrite with norm.
              rep_omega.
              (* ptr is not empty: implicit contract - also in fetch_tags *)
              admit. 
              forward_if 
                [temp _t'7 tlv_constr].
           ** forward.
              entailer!.
              eapply typed_true_e in H1.
              generalize H1.
              unfold force_val.
              unfold sem_and.
              unfold sem_binarith.
              cbn -[Znth].
              repeat erewrite Znth_map.
              simpl.
              strip_repr.
              normalize.
              rewrite_if_b.
              auto.
              1-2 : admit. (* 0 < len ptr *)
           ** forward.
              entailer!.
              eapply typed_false_tint_e in H1.
              generalize H1.
              unfold force_val.
              unfold sem_and.
              unfold sem_binarith.
              cbn -[Znth].
              repeat erewrite Znth_map.
              simpl.
              strip_repr.
              intro.
              rewrite_if_b.
              auto.
              1-2: admit. (* 0 < len ptr *)
           ** forward.
              remember (if eq_dec 
                            (Vint (Int.repr (Byte.unsigned (Byte.repr (Znth 0 ptr)) & 32)))
                            (Vint 0%int)
                       then 0
                       else 1) as tlv_constr_Z.
              forward_call (tlv_constr_Z, offset_val tag_len ptr_p,
                            size - tag_len, v_tlv_len). 
              entailer!.
              break_if; auto.
               match goal with
               | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                 forward_switch Pre
               end. 
               match goal with
               | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                 forward_empty_while_break Pre
               end. 
          *** (* RC_FAIL *) 
              admit.
          *** match goal with
               | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                 forward_empty_while_break Pre
               end. 
              (* RC_FAIL *) 
              admit.
          *** forward.
              entailer!.
          ***
             (* forward_empty_while. (* ADVANCE *)
              repeat forward.
              entailer!.
              assert (isptr ptr_p) as P by admit.
              unfold isptr in P.
              destruct ptr_p; try contradiction.
              erewrite <- split_non_empty_list.
              entailer!.
              erewrite <- Znth_map.
              erewrite Znth_cons_sublist.
              autorewrite with sublist.
              auto.
              list_solve.
              list_solve.
              autorewrite with sublist.
              admit. (* add precondition ptr_p + len ptr < Ptrofs.modulus *)
              1-2: (list_solve || autorewrite with subslist; auto).  *)
            admit.
          ** (* subst.
             assert (isptr ptr_p) as P by admit.
             unfold isptr in P.
             destruct ptr_p; try contradiction.
             erewrite <- split_non_empty_list.
             reflexivity.
             erewrite Znth_cons_sublist.
             all: (list_solve || autorewrite with sublist; auto). *)
            admit.
              (* add precondition ptr_p + len ptr < Ptrofs.modulus *)
          ++ forward.
              admit. (* assert fail case *)
          ++ (* MAIN LOOP *)
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
              forward_call ((offset_val num ptr_p), (size - num), v_tlv_tag).
              forward_empty_loop.
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
               assert (0 < len ptr) as T by admit.
               assert_PROP (offset_val num ptr_p 
                            = field_address (tarray tuchar (len ptr)) [ArraySubsc num] ptr_p).
               { entailer!.
                 rewrite field_address_offset.
                 auto.
                 econstructor.
                 auto.
                 cbn.
                 repeat split; auto; cbn; try nia.
                 unfold size_compatible.
                 break_match; auto.
                 admit.
                 admit.
                 admit. }                 
               forward.
               entailer!.
               repeat erewrite Znth_map; auto.
               cbn.
               strip_repr.
               1-2: admit.
               forward_if (temp _t'13 tlv_constr).
               ** forward. entailer!.
                  admit. (* as before *)
               ** forward. entailer!.
                  admit. (* as before *)
               ** forward.
                  forward_if
                    (temp _t'15
                          (if eq_dec (Int.repr tag_mode) Int.zero
                           then Vzero
                           else force_val
                                  (sem_cast_i2bool
                                     (Val.of_bool
                                        (Int.repr (if eq_dec opt_ctx_p (Vint 0) 
                                                   then 0
                                                   else step opt_ctx) == Int.repr 0)%int))));
                    try forward; try entailer!; rewrite_if_b; try entailer!.
                 all:  auto.
                 forward_if True. (* TODO *)
             *** forward. entailer!.
             *** forward_if True.
                 forward.
                 entailer!.
                 admit. (* assert_fail *)
                 forward.
                 admit. (* FIXME *)
                 
                 entailer!.
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
