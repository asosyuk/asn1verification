Require Import Core.Core Core.StructNormalizer
        VstLib ErrorWithWriter BCT.Exec.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_decoder.

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
         step : Z, c : asn_struct_ctx_type, ctx_Z : asn_codec_ctx
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
      SEP (data_at_ Tsh asn_dec_rval_s res_p;
           data_at_ Tsh tint ll_p;
           data_at Tsh (Tstruct _asn_struct_ctx_s noattr) c ctx_s_p)
    POST [tvoid]
      PROP ()
      LOCAL ()
      SEP (match ber_check_tags buf td ctx_Z tag_mode size step with
           | Some v => 
             data_at Tsh asn_dec_rval_s 
                     (mk_dec_rval 0 v) res_p *
             data_at Tsh tint (Vint (Int.repr v)) ll_p
           | None => 
             data_at Tsh asn_dec_rval_s (mk_dec_rval 2 0) res_p *
             data_at_ Tsh tint ll_p
           end).

Definition Gprog := ltac:(with_library prog [ber_check_tags_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog (normalize_function f_ber_check_tags composites) ber_check_tags_spec.
Proof.
  start_function.
  repeat forward.
  forward_if (temp _t'1 
                   (Vint (Int.repr (if eq_dec ctx_s_p nullval 
                                    then 0 
                                    else step)))).
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
Admitted.

End Ber_check_tags.
