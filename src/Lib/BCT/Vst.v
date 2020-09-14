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
           data_at Tsh (Tstruct _asn_struct_ctx_s noattr) c ctx_s_p;
           data_at Tsh (Tstruct _asn_codec_ctx_s noattr) 
                   (Vint (Int.repr (max_stack_size ctx_Z))) ctx_p)
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

Require Import VST.ASN__STACK_OVERFLOW_CHECK.

Definition Gprog := ltac:(with_library prog [ber_check_tags_spec;
                         ASN__STACK_OVERFLOW_CHECK_spec]).

Theorem bool_der_encode : 
  semax_body Vprog Gprog
             (normalize_function f_ber_check_tags composites) 
             ber_check_tags_spec.
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
  forward_call (ctx_p, max_stack_size ctx_Z).
  forward_if True. (* TODO *)
  deadvars!.
  forward_loop  (PROP ( )
     LOCAL (temp _step (Vint (Int.repr (if eq_dec ctx_s_p nullval then 0 else step)));
     temp _consumed_myself (Vint (Int.repr 0));
     lvar _rval__16 (Tstruct _asn_dec_rval_s noattr) v_rval__16;
     lvar _rval__15 (Tstruct _asn_dec_rval_s noattr) v_rval__15;
     lvar _rval__14 (Tstruct _asn_dec_rval_s noattr) v_rval__14;
     lvar _rval__13 (Tstruct _asn_dec_rval_s noattr) v_rval__13;
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
     lvar _tlv_tag tuint v_tlv_tag; temp __res res_p; temp _opt_ctx ctx_s_p)
     SEP (data_at Tsh (Tstruct _asn_codec_ctx_s noattr) (Vint (Int.repr (max_stack_size ctx_Z)))
            ctx_p; data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__16;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__15;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__14;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__13;
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
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval; data_at_ Tsh tint v_tlv_len;
     data_at_ Tsh tuint v_tlv_tag; data_at_ Tsh asn_dec_rval_s res_p; 
     data_at_ Tsh tint ll_p; data_at Tsh (Tstruct _asn_struct_ctx_s noattr) c ctx_s_p)).
  - entailer!.
  - forward.
    forward_if (c = (let (x, _) := c in x,
    (Vint (Int.sign_ext 16 (Int.repr (if Memory.EqDec_val ctx_s_p nullval then 0 else step))),
    let (_, y) := let (_, y) := c in y in y))).
    -- forward.
       entailer!.
       break_let.
       generalize H.
       break_let.
       subst.
       admit.
       admit.
    -- forward.
       entailer!.
    -- admit.
 - admit.
 - admit.
Admitted.

End Ber_check_tags.
