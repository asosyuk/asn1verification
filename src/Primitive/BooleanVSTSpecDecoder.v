Require Import ASN1V.Core.Core Core.StructNormalizer VstLib Stdlib
        BooleanExecSpec ErrorWithWriter BCTVSTSpec.
Require Import VST.floyd.proofauto Psatz.
Require Import Clight.BOOLEAN.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Instance Change1 : change_composite_env CompSpecs BCTVSTSpec.CompSpecs.
Proof. make_cs_preserve CompSpecs BCTVSTSpec.CompSpecs. Defined.

Instance Change2 : change_composite_env BCTVSTSpec.CompSpecs CompSpecs.
Proof. make_cs_preserve BCTVSTSpec.CompSpecs CompSpecs. Defined.

Open Scope Z.

Section Boolean_ber_decode.

Definition bool_ber_decode_spec : ident * funspec :=
  DECLARE _BOOLEAN_decode_ber
    WITH sh_ctx : share, ctx_b : block, ctx_ofs : ptrofs, ctx : val,
         sh_td : share, td_b : block, td_ofs : ptrofs, td : TYPE_descriptor,
         sh_val: share, bool_value : val, 
         sh_buf : share, buf_b : block, buf_ofs : ptrofs, buf : list byte,
         sh_res : share, res_b : block, res_ofs : ptrofs,
         size : Z, tag_mode : Z,
         bv : val, res : val
    PRE  [ tptr asn_dec_rval_s,
          tptr asn_codec_ctx_s,
          tptr type_descriptor_s,
          tptr (tptr tvoid), tptr tvoid, tuint, tint ] 
    PROP (writable_share sh_val;
         writable_share sh_res; is_pointer_or_null bv)
    PARAMS (res; ctx; Vptr td_b td_ofs; bool_value;
            Vptr buf_b buf_ofs; Vint (Int.repr size);
              Vint (Int.repr tag_mode))
    GLOBALS()
    SEP (
         valid_pointer bv;
         data_at sh_ctx (tptr asn_codec_ctx_s)
                   (Vptr ctx_b ctx_ofs) ctx;
         data_at sh_td type_descriptor_s
                   (TYPE_descriptor_rep td) (Vptr td_b td_ofs);
         data_at sh_buf (tarray tschar (Zlength buf)) (map Vbyte buf) 
                   (Vptr buf_b buf_ofs);
        data_at sh_val (tptr tvoid) bv bool_value;
        data_at_ sh_res asn_dec_rval_s res)
    POST [tvoid]
      PROP()
      LOCAL ()
      SEP( (* Unchanged by the execution : *)
           valid_pointer bv;
           data_at sh_ctx (tptr asn_codec_ctx_s) (Vptr ctx_b ctx_ofs) ctx;
           data_at sh_td type_descriptor_s (TYPE_descriptor_rep td) 
                   (Vptr td_b td_ofs);
           data_at sh_buf (tarray tschar (Zlength buf)) (map Vbyte buf) 
                   (Vptr buf_b buf_ofs);
           (* Changes according to the exec spec *)
           let RC_FAIL := data_at sh_res asn_dec_rval_s 
                                  (construct_dec_rval 2 0) res in
           if Val.eq bool_value Vnullptr 
           then RC_FAIL
           else match bool_decoder td buf with
                | Some (r, c) => 
                  data_at sh_res asn_dec_rval_s (construct_dec_rval 0 c) res *
                  data_at sh_val (tptr tuchar) (Vbyte (bool_to_byte r)) bool_value
                | None => RC_FAIL *
                         data_at sh_val (tptr tuchar)
                                 (default_val (tptr tuchar)) bool_value
                end).

Definition Gprog := ltac:(with_library prog [(_calloc, calloc_spec); 
                                              ber_check_tags_spec; 
                                              bool_ber_decode_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog 
           (normalize_function f_BOOLEAN_decode_ber composites) bool_ber_decode_spec.
Proof.
  start_function.
  repeat forward.
  forward_if (is_pointer_or_null bv).
  - Time forward_call (1, sizeof(tint)).
    cbn; nia.
    Intros p.
    forward.
    forward.
    break_if.
    break_let.
    simpl in e; subst.
    forward_if.
    repeat forward.
    (* entailer!.
    break_if/
    + entailer! *)
Admitted.

End Boolean_ber_decode.
