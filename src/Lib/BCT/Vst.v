Require Import Core.Core Core.Tactics Core.VstTactics Core.StructNormalizer
        VstLib ErrorWithWriter BCT.Exec.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_decoder.
Require Import VST.ASN__STACK_OVERFLOW_CHECK ber_fetch_tag ber_fetch_length Lib.Forward. 

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section Ber_check_tags.

(* ts td ctx tag_mode size step *)

(* typedef struct asn_struct_ctx_s {
	short phase;		/* Decoding phase */
	short step;		/* Elementary step of a phase */
	int context;		/* Other context information */
	void *ptr;		/* Decoder-specific stuff (stack elements) */
	ber_tlv_len_t left;	/* Number of bytes left, -1 for indefinite */
} asn_struct_ctx_t;
*)

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

Instance Change3 : change_composite_env CompSpecs ber_fetch_length.CompSpecs.
Proof. make_cs_preserve CompSpecs ber_fetch_length.CompSpecs. Defined.

Instance Change4 : change_composite_env ber_fetch_length.CompSpecs CompSpecs.
Proof. make_cs_preserve ber_fetch_length.CompSpecs CompSpecs. Defined.

Definition ber_check_tags_spec : ident * funspec :=
  DECLARE _ber_check_tags
    WITH opt_codec_ctx_p : val, opt_codec_ctx : val,
         td_p : val, td : TYPE_descriptor, 
         t : reptype (Tstruct _asn_TYPE_descriptor_s noattr),
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
      SEP (data_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) t td_p;
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
      SEP (data_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) t td_p;          
           data_at Tsh (Tstruct _asn_codec_ctx_s noattr) 
                  (Vint (Int.repr (max_stack_size))) opt_codec_ctx_p;
        match ber_check_tags ptr td max_stack_size
                             tag_mode size (step opt_ctx) with
           | Some v => 
             data_at Tsh asn_dec_rval_s 
                     (mk_dec_rval 0 v) res_p *
             data_at Tsh (Tstruct _asn_struct_ctx_s noattr) 
                   (Vint (Int.repr (phase opt_ctx)), 
                    (Vint st, (* saving context *)
                     (Vint (Int.repr (context opt_ctx)), 
                      (Vptr (fst (pt opt_ctx)) (snd (pt opt_ctx)),
                       Vint (Int.repr (left opt_ctx))))))
                   opt_ctx_p *
             data_at Tsh tint (Vint (Int.repr v)) last_length_p
           | None => 
             data_at Tsh asn_dec_rval_s (mk_dec_rval 2 0) res_p *
             data_at Tsh (Tstruct _asn_struct_ctx_s noattr) 
                   (Vint (Int.repr (phase opt_ctx)), 
                    (Vint st, (* saving context *)
                     (Vint (Int.repr (context opt_ctx)), 
                      (Vptr (fst (pt opt_ctx)) (snd (pt opt_ctx)),
                       Vint (Int.repr (left opt_ctx))))))
                   opt_ctx_p *
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
  repeat forward.
  pose proof (step_short opt_ctx) as S.
  forward_if (temp _t'1 (Vint (Int.repr (if eq_dec opt_ctx_p nullval 
                         then 0
                         else step opt_ctx)))); try forward; try entailer!.
  - 
  forward.
  rewrite if_false.                                     
  entailer!.
  { destruct opt_ctx_p; cbn in H; try (contradiction || discriminate). }
  -
  forward_call (opt_codec_ctx_p, max_stack_size).
  forward_if (opt_codec_ctx_p <> nullval).
  + 
  forward_empty_while.
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
    entailer!. 
  - forward.
    admit.
  - (* forward_if
      (temp _t'4 (Vint (Int.repr (if eq_dec (Int.repr tag_mode) (Int.repr 1)
                                  then -1 else 0)))). *)
    forward_if (temp _t'4 (Vint (Int.repr (-1)))).
    -- (* forward.
       Require Import Core.VstTactics.
       repeat rewrite_if_b.
       entailer!.
       rewrite_if_b.
       auto. *) admit.
    -- (* forward.
       entailer!.
       rewrite_if_b.
       auto. *) admit.
    -- forward.
       (* entailer!. *)
       admit.
       Ltac strip_repr :=
         autorewrite with norm;
         unfold Int.add; unfold Int.mul; unfold Int.neg;
         unfold Int.sub;
         try erewrite Int.unsigned_one in *;
         try erewrite Int.unsigned_zero in *;
         repeat rewrite Int.unsigned_repr;  
         repeat rewrite Int.signed_repr;     
         try rep_omega; auto. 
     (*  { repeat break_if; strip_repr.
         all: admit. (* step within int bounds *) } *)
       (* forward_if (temp _t'12 (Vint (Int.repr (if eq_dec (Int.repr tag_mode)
                                                         (Int.repr 0)
                                               then 1
                                               else 0)))). *)
       forward_if (temp _t'12 Vone).
       --- forward.
           admit.
           forward.
           admit.
       --- forward.
           entailer!.
           rewrite_if_b.
           admit.
       ---         
         forward_if True. (* TODO *)
          + forward_call (buf_p, size, v_tlv_tag).
            rewrite_if_b.
            match goal with
            | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                forward_switch Pre
              end. 
            clear E.
            abbreviate_semax.
            
            Ltac forward_empty_while_break :=
              match goal with
              | [ _ : _ |- semax _ ?Pre (Ssequence (Sloop _ Sbreak) _) _ ] =>
                forward_loop Pre break: Pre; try forward ; try entailer! 
              end. 
            * forward_empty_while_break.
              forward_if True.
              forward.
              entailer!.
              admit.
              forward.
              entailer!.
              forward_if True.
              forward.
              entailer!.
              admit.
              admit.
              admit.
            * forward_empty_while_break.
              admit. 
            * forward.
              admit.
            * 
              Ltac add_sep Q p
                := match goal with
                   | [ _ : _ |- semax _ (@PROPx environ ?ps 
                                               (LOCALx ?lcs 
                                                       (@SEPx environ ?ls))) 
                                     ?C ?Post ] =>
                     let ls' := replace_sep ls Q p in
                     replace (@PROPx environ ps 
                                     (LOCALx lcs 
                                             (@SEPx environ ls)))
                       with
                         (@PROPx environ ps
                                 (LOCALx lcs
                                         (@SEPx environ (ls'))))
                   end.
              add_sep (data_at_ Tsh tuchar buf_p) buf_p.
              forward.
              admit.
              forward_if (temp _t'8 Vzero).
              forward.
              admit.
              forward.
              admit.
              forward.
              forward_call (0, offset_val 1 buf_p, (size - 1), v_tlv_len). 
               match goal with
            | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                forward_switch Pre
              end. 
               forward_empty_while_break.
               admit.
               forward_empty_while_break.
               admit.
               forward_empty_while_break.
               admit.
               forward.
               admit.
               forward_empty_while.
               forward.
               forward.
               forward.
               forward.
               admit.
               admit.
           + forward.
             admit. 
             forward_if.
             forward.
             admit.
             admit.
           + (* MAIN LOOP *)
           ---- 
              match goal with
            | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                forward_loop Pre
                             continue: Pre
                             break: Pre
              end.
                ++ entailer!.
                ++ forward.
                   admit.
                   forward_if.
                   forward_call (buf_p, size, v_tlv_tag).
                   forward_empty_loop.
                    match goal with
                    | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                      forward_switch Pre
                    end.
                    admit.
                    admit.
                    forward.
                    admit.
                    add_sep (data_at_ Tsh tuchar buf_p) buf_p.
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
