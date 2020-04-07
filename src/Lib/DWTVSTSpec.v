Require Import Core.Core Core.StructNormalizer VstLib DWTExecSpec ErrorWithWriter.
Require Import VST.floyd.proofauto Psatz.
Require Import Clight.der_encoder.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section Der_write_tags.

Definition der_write_tags_spec : ident * funspec :=
  DECLARE _der_write_tags
    WITH (* pointer to type descriptor structure *) 
         sd_b : block, sd_ofs : ptrofs, sd : TYPE_descriptor, sh_sd : share,
         struct_l : Z, tag_mode : Z, last_tag_form : Z, tag : Z,
         (* callback pointer *)
         cb_b : block, cb_ofs : ptrofs, cb_val : val, sh_cb : share,
         (* callback argument pointer *)
         app_key_b : block, app_key_ofs : ptrofs,
         app_key_val : val, sh_app_key : share
    PRE [ _sd OF (tptr (Tstruct _asn_TYPE_descriptor_s noattr)),
          _struct_length OF tuint, _tag_mode OF tint,
          _last_tag_form OF tint, _tag OF tuint,
          _cb OF cb_type, _app_key OF (tptr tvoid) ]
    PROP ( readable_share sh_sd;
           readable_share sh_cb;
           readable_share sh_app_key )
    LOCAL ( temp _sd (Vptr sd_b sd_ofs);
            temp _struct_length (Vint (Int.repr struct_l));
            temp _tag_mode (Vint (Int.repr tag_mode));
            temp _last_tag_form (Vint (Int.repr last_tag_form));
            temp _tag (Vint (Int.repr tag));
            temp _cb (Vptr cb_b cb_ofs);
            temp _app_key (Vptr app_key_b app_key_ofs))
    SEP ( data_at sh_sd (Tstruct _asn_TYPE_descriptor_s noattr) 
                  (TYPE_descriptor_rep sd) (Vptr sd_b sd_ofs) ; 
          data_at sh_app_key (tvoid) (tt) (Vptr app_key_b app_key_ofs) ;
          data_at sh_cb (cb_type) (tt) (Vptr cb_b cb_ofs))
    POST [tint]
      PROP ()
      LOCAL (temp ret_temp (Vint (Int.repr (
                                      match evalErrW (der_write_tags sd) [] with
                                      | Some w => encoded w
                                      | None => -1
                                      end))))
      SEP ( (* Unchanged by the execution : *)
            data_at sh_sd (Tstruct _asn_TYPE_descriptor_s noattr) 
                    (TYPE_descriptor_rep sd) (Vptr sd_b sd_ofs) ; 
            data_at sh_app_key (tvoid) (tt) 
                    (Vptr app_key_b app_key_ofs) ;
            data_at sh_cb (cb_type) (tt) (Vptr cb_b cb_ofs)).

Definition Gprog := ltac:(with_library prog [der_write_tags_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog (normalize_function f_der_write_tags composites) der_write_tags_spec.
Admitted.

End Der_write_tags.
