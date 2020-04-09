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
         td_p : val, td : TYPE_descriptor,
         struct_len: Z, tag_mode : Z, last_tag_form : Z, tag : Z,
         (* callback pointer *)
         cb_p : val, cb_val : val,
         (* callback argument pointer *)
         app_p : val, app_key_val : val
    PRE [ _sd OF (tptr (Tstruct _asn_TYPE_descriptor_s noattr)),
          _struct_length OF tuint, _tag_mode OF tint,
          _last_tag_form OF tint, _tag OF tuint,
          _cb OF tptr cb_type, _app_key OF tptr tvoid ]
    PROP ()
    LOCAL ( temp _sd td_p;
            temp _struct_length (Vint (Int.repr struct_len));
            temp _tag_mode (Vint (Int.repr tag_mode));
            temp _last_tag_form (Vint (Int.repr last_tag_form));
            temp _tag (Vint (Int.repr tag));
            temp _cb cb_p;
            temp _app_key app_p)
    SEP ( data_at_ Tsh type_descriptor_s td_p ; 
          data_at Tsh tvoid tt app_p ;
          data_at Tsh cb_type tt cb_p)
    POST [tint]
      PROP ()
      LOCAL (temp ret_temp (Vint (Int.repr (
                                      match evalErrW (der_write_tags td) [] with
                                      | Some w => encoded w
                                      | None => -1
                                      end))))
      SEP ( (* Unchanged by the execution : *)
            data_at_ Tsh type_descriptor_s td_p ; 
            data_at Tsh tvoid tt app_p ;
            data_at Tsh cb_type tt cb_p).

Definition Gprog := ltac:(with_library prog [der_write_tags_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog (normalize_function f_der_write_tags composites) der_write_tags_spec.
Proof.
  start_function.
Admitted.

End Der_write_tags.
