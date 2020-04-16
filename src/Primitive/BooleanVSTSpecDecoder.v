Require Import ASN1V.Core.Core Core.StructNormalizer VstLib Stdlib
        BooleanExecSpec ErrorWithWriter BCTVSTSpec.
Require Import VST.floyd.proofauto VST.floyd.library Psatz.
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
    WITH sh_ctx : share, ctx_p : val, ctx : val,
         sh_td : share, td_p : val, td : TYPE_descriptor,
         sh_bv_pp :share, sh_bv_p : share, bv_pp : val, 
         sh_buf : share, buf_p : val, buf : list byte,
         sh_res : share, res_p : val,
         size : Z, tag_mode : Z,
         bv_p : val 
   PRE  [tptr asn_dec_rval_s, tptr asn_codec_ctx_s, tptr type_descriptor_s,
          tptr (tptr tvoid), tptr tvoid, tuint, tint] 
    PROP (writable_share sh_bv_pp; writable_share sh_res; 
          writable_share sh_bv_p; is_pointer_or_null bv_p)
    PARAMS (res_p; ctx_p; td_p; bv_pp; buf_p; Vint (Int.repr size);
              Vint (Int.repr tag_mode))
    GLOBALS ()
    SEP (valid_pointer bv_p;
         data_at sh_ctx asn_codec_ctx_s ctx ctx_p;
         data_at sh_td type_descriptor_s (TYPE_descriptor_rep td) td_p;
         data_at sh_buf (tarray tschar (Zlength buf)) (map Vbyte buf) buf_p;
         data_at sh_bv_pp (tptr tvoid) bv_p bv_pp;
         data_at_ sh_res asn_dec_rval_s res_p)
    POST [tvoid]
      PROP()
      LOCAL ()
      SEP( (* Unchanged by the execution : *)
           valid_pointer bv_p;
           data_at sh_ctx asn_codec_ctx_s ctx ctx_p;
           data_at sh_td type_descriptor_s (TYPE_descriptor_rep td) td_p;
           data_at sh_buf (tarray tschar (Zlength buf)) (map Vbyte buf) buf_p;
           data_at sh_bv_pp (tptr tvoid) bv_p bv_pp;
           (* Changes according to the exec spec *)
           let RC_FAIL := 
               data_at sh_res asn_dec_rval_s (construct_dec_rval 2 0) res_p in
           if Val.eq bv_p Vnullptr 
           then RC_FAIL 
           else match bool_decoder td buf with
                | Some (r, c) => 
                  data_at sh_res asn_dec_rval_s (construct_dec_rval 0 c) res_p *
                  data_at sh_bv_p tuchar (Val.of_bool r) bv_p 
                | None => RC_FAIL                          
                end).

Definition Gprog := ltac:(with_library prog [(_calloc, calloc_spec); 
                                              ber_check_tags_spec; 
                                              bool_ber_decode_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog 
           (normalize_function f_BOOLEAN_decode_ber composites) bool_ber_decode_spec.
Proof.
  start_function.
  repeat forward.
  forward_if (True).
  - forward_call (1, sizeof tint).
    cbn; nia.
    Intros p.
    forward.
    forward.
    forward_if.
    break_if; break_let.
    -- entailer!.
       simpl in e; subst.
       entailer!.
    -- eapply denote_tc_test_eq_split; entailer!.
    -- Intros.
       repeat forward.
       entailer!.
       repeat break_if; entailer!.
    -- forward.
       break_if; entailer!.
       admit.
       admit.
  - forward.
    entailer!.
  - admit.   
Admitted.

End Boolean_ber_decode.
