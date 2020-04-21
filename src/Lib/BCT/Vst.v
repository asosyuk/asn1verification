Require Import Core.Core Core.StructNormalizer
        VstLib ErrorWithWriter BCT.Exec.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_decoder.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section Ber_check_tags.

Definition ber_check_tags_spec : ident * funspec :=
  DECLARE _ber_check_tags
    WITH (* Codec context pointer *) 
         ctx_p : val, ctx : val,
         (* Type Descriptor pointer *)
         td_p : val, td : TYPE_descriptor,
         (* Struct context pointer *) 
         ctx_s_p : val, ctx_s : val,
         (* Buffer pointer *)
         buf_p : val, buf : list byte,
         (* pointer to the return struct dec_rval *)                        
         res_p : val,
         size : Z, tag_mode : Z, last_tag_from : Z,
         ll_p : val, ll : Z, opt_tlv_form_p : val, opt_tlv_form : Z
    PRE [tptr asn_dec_rval_s, tptr (Tstruct _asn_codec_ctx_s noattr),
         tptr (Tstruct _asn_TYPE_descriptor_s noattr),
         tptr (Tstruct _asn_struct_ctx_s noattr), 
         tptr tvoid, tuint, tint, tint, tptr tint, tptr tint]
      PROP ()
      PARAMS (res_p; ctx_p; td_p; ctx_s_p; buf_p; Vint (Int.repr size);
              Vint (Int.repr tag_mode); Vint (Int.repr last_tag_from);
              ll_p; opt_tlv_form_p)
      GLOBALS ()
      SEP (data_at_ Tsh asn_dec_rval_s res_p)
    POST [tvoid]
      PROP ()
      LOCAL ()
      SEP (data_at Tsh asn_dec_rval_s 
                   (match ber_check_tags td buf with
                    | Some v => construct_dec_rval (tag_consumed v) (tag_expected v)
                    | None => construct_dec_rval 0 0 
                    (* TODO set appropriate values for failure *)
                    end) res_p).

Definition Gprog := ltac:(with_library prog [ber_check_tags_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog (normalize_function f_ber_check_tags composites) ber_check_tags_spec.
Admitted.

End Ber_check_tags.
