Require Import Core.Core Core.StructNormalizer
 VstLib DWTExecSpec ErrorWithWriter BCTExecSpec.
Require Import VST.floyd.proofauto Psatz.
Require Import Clight.ber_decoder.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section Ber_check_tags.

Definition ber_check_tags_spec : ident * funspec :=
  DECLARE _ber_check_tags
    WITH (* Codec context pointer *) 
         sh_ctx : share, ctx_b : block, ctx_ofs : ptrofs, ctx : val,
         (* Type Descriptor pointer *)
         sh_td : share, td_b : block, td_ofs : ptrofs, td : TYPE_descriptor,
         (* Struct context pointer *) 
         sh_ctx_s : share, ctx_s_b : block, ctx_s_ofs : ptrofs, ctx_s : val,
         (* Buffer pointer *)
         sh_ptr : share, ptr_b : block, ptr_ofs : ptrofs, ptr : list byte,
         (* pointer to the return struct dec_rval *)                        
         sh_res : share, res_b : block, res_ofs : ptrofs,
         size : Z, tag_mode : Z, last_tag_from : Z
         (* sh_ll : share, ll_b : block, ll_ofs : ptrofs, ll : val,
         sh_opt : share, opt_b : block, opt_ofs : ptrofs, opt : val *)

    PRE [ __res OF (tptr (Tstruct _asn_dec_rval_s noattr)),
         _opt_codec_ctx OF (tptr (Tstruct _asn_codec_ctx_s noattr)),
         _td OF (tptr (Tstruct _asn_TYPE_descriptor_s noattr)),
         _opt_ctx OF (tptr (Tstruct _asn_struct_ctx_s noattr)),
         _ptr OF (tptr tvoid),
         _size OF tuint,
         _tag_mode OF tint,
         _last_tag_form OF tint,
         _last_length OF (tptr tint),
         _opt_tlv_form OF (tptr tint)]
    PROP ( )
    LOCAL ()
    SEP ()
    POST [tvoid]
      PROP ()
      LOCAL ()
      SEP ().

Definition Gprog := ltac:(with_library prog [ber_check_tags_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog (normalize_function f_ber_check_tags composites) ber_check_tags_spec.
Proof.
  start_function.
  repeat forward.
Admitted.

End Ber_check_tags.
