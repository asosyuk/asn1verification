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
     context : Z;		
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

(*  
Definition ctx_rep c : reptype (Tstruct _asn_struct_ctx_s noattr) :=
  (Vint (Int.repr (phase c)), Vint (Int.repr (step c)),
   Vint (Int.repr (context c)), Vzero, Vint (Int.repr (left c))). 

Eval cbn in reptype (Tstruct _asn_struct_ctx_s noattr). *)

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
    WITH (* Codec context pointer *) 
         ctx_p : val, ctx : val,
         (* Type Descriptor pointer *)
         td_p : val, td : TYPE_descriptor,
         (* Struct context pointer *) 
         ctx_s_p : val, ctx_s : val,
         (* Buffer pointer *)
         buf_p : val, buf : list Z,
         (* pointer to the return struct dec_rval *)                        
         res_p : val,
         size : Z, tag_mode : Z, last_tag_from : Z,
         ll_p : val, opt_tlv_form_p : val, opt_tlv_form : Z,
         step : Z, c : asn_struct_ctx_type, ctx_Z : asn_codec_ctx,
         t : reptype (Tstruct _asn_TYPE_descriptor_s noattr)
    PRE [tptr asn_dec_rval_s, tptr (Tstruct _asn_codec_ctx_s noattr),
         tptr (Tstruct _asn_TYPE_descriptor_s noattr),
         tptr (Tstruct _asn_struct_ctx_s noattr), 
         tptr tvoid, tuint, tint, tint, tptr tint, tptr tint]
      PROP (let (x, _) := let (_, y) := c in y in x
            = Vint (Int.repr (if eq_dec ctx_s_p nullval then 0 else step)))
      PARAMS (res_p; ctx_p; td_p; ctx_s_p; buf_p; Vint (Int.repr size);
              Vint (Int.repr tag_mode); Vint (Int.repr last_tag_from);
              ll_p; opt_tlv_form_p)
      GLOBALS ()
      SEP (data_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) t td_p;
           data_at_ Tsh asn_dec_rval_s res_p;
           data_at_ Tsh tint ll_p;
           data_at Tsh (Tstruct _asn_struct_ctx_s noattr) c ctx_s_p;
           data_at Tsh (Tstruct _asn_codec_ctx_s noattr) 
                   (Vint (Int.repr (max_stack_size ctx_Z))) ctx_p)
    POST [tvoid]
      PROP ()
      LOCAL ()
      SEP ( data_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) t td_p;
        match ber_check_tags buf td ctx_Z tag_mode size step with
           | Some v => 
             data_at Tsh asn_dec_rval_s 
                     (mk_dec_rval 0 v) res_p *
             data_at Tsh tint (Vint (Int.repr v)) ll_p
           | None => 
             data_at Tsh asn_dec_rval_s (mk_dec_rval 2 0) res_p *
             data_at_ Tsh tint ll_p
           end;
          data_at Tsh (Tstruct _asn_struct_ctx_s noattr) c ctx_s_p;
          data_at Tsh (Tstruct _asn_codec_ctx_s noattr) 
                  (Vint (Int.repr (max_stack_size ctx_Z))) ctx_p).

Definition Gprog := ltac:(with_library prog [ber_check_tags_spec;
                                             ber_fetch_tag_spec;
                                             ber_fetch_length_spec;
                                             ASN__STACK_OVERFLOW_CHECK_spec]).

(* tactics *)

Ltac replace_sep ls Q p := 
  let rec replace_sep ls Q p :=
      match ls with 
      | [] => constr:([Q])
      | ?h :: ?tl => match h with 
                   | data_at _ _ _ p => constr: (Q :: tl)
                   | _ =>
                     let r := replace_sep tl Q p in
                     constr: (h :: r)
                   end
      end in
  replace_sep ls Q p. 

Ltac forward_if_add_sep Q p
  := match goal with
     | [ _ : _ |- semax _ (@PROPx environ ?ps 
                                 (LOCALx ?lcs 
                                         (@SEPx environ ?ls))) 
                       (Ssequence (Sifthenelse _ _ _) _) _ ] =>
       let ls' := replace_sep ls Q p in
       forward_if (@PROPx environ ps
                          (LOCALx lcs
                                  (@SEPx environ (ls'))))
     end.

Ltac forward_empty_while :=
  match goal with
  | [ _ : _ |- semax _ ?Pre (Sloop _ Sbreak) _ ] =>
    forward_loop Pre; try forward ; try entailer! 
  end. 

Theorem bool_der_encode : 
  semax_body Vprog Gprog
             (normalize_function f_ber_check_tags composites) 
             ber_check_tags_spec.
Proof.
  start_function.
  repeat forward.
  forward_if (temp _t'1 
                    (if eq_dec ctx_s_p nullval 
                                    then (Vint (Int.repr 0)) 
                                    else (Vint (Int.repr step)))).
  forward.    
  entailer!.
  repeat break_let.
  subst.
  inversion Heqp.
  cbn.
  (* add short bounds *)
  admit.
  forward.
  entailer!.
  admit.
  forward.
  entailer!.
  forward.
  forward_call (ctx_p, max_stack_size ctx_Z).
  unfold MORE_COMMANDS.
  unfold abbreviate.
  (* forward_if ((if eq_dec ctx_p nullval
               then 0
               else ASN__STACK_OVERFLOW_CHECK 0 (max_stack_size ctx_Z)) = 0). *)
  forward_if True.
  deadvars!.  
  forward_empty_while.
  -
    forward_if (c = (let (x, _) := c in x,
    (Vint (Int.sign_ext 16 (Int.repr (if Memory.EqDec_val ctx_s_p nullval then 0 else step))),
    let (_, y) := let (_, y) := c in y in y))).
    -- (* forward.
       entailer!.
       break_let.
       generalize H.
       break_let.
       subst.
       admit.
       admit. *)
      admit.
    -- (* forward.
       entailer!. *) admit.
    -- forward_if (temp _t'2 (force_val (sem_cast_i2bool ctx_s_p))).
       (*nia.
       forward.
       admit.
       forward_if_add_sep (data_at Tsh (Tstruct _asn_dec_rval_s noattr)
       (Vint (Int.repr 2), Vint (Int.repr 0)) v_rval) v_rval.
       forward.
       entailer!.
       forward.
       entailer!.
       repeat forward. *)
       admit.
       (* assert (ber_check_tags buf td ctx_Z tag_mode size step = None) as N.
       { admit. }
       erewrite N.
       entailer!. *)
       all: admit.
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
           + forward.
                admit. 
                forward_if.
                forward.
                entailer!.
                (* assert fail *)
                admit.
           ---- forward_loop ... 
                + entailer!.
                + forward.
                  admit.
                  forward_if.
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
