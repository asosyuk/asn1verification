Require Import Core.Core Core.StructNormalizer VstLib DWTExecSpec ErrorWithWriter.
Require Import VST.floyd.proofauto.
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
       cb_p : val,
       (* callback argument pointer *)
       app_p : val, app_key_val : val
  PRE[tptr type_descriptor_s, tuint, tint, tint, tuint, 
      tptr cb_type, tptr tvoid]
    PROP()
    PARAMS(td_p; Vint (Int.repr struct_len); Vint (Int.repr tag_mode);
           Vint (Int.repr last_tag_form); Vint (Int.repr tag); cb_p; app_p)
    GLOBALS()
    SEP(data_at_ Tsh type_descriptor_s td_p ; 
        data_at_ Tsh tvoid app_p ;
        func_ptr cb_spec cb_p)
    POST[tint]
      PROP()
      LOCAL(temp ret_temp 
                 (Vint (Int.repr (match evalErrW (der_write_tags td) [] with
                                  | Some w => encoded w
                                  | None => -1
                                  end))))
      SEP((* Unchanged by the execution : *)
          data_at_ Tsh type_descriptor_s td_p ; 
          data_at_ Tsh tvoid app_p ;
          func_ptr cb_spec cb_p).

Definition Gprog := ltac:(with_library prog [der_write_tags_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog f_der_write_tags 
                                     der_write_tags_spec.
Proof.
  start_function.
Admitted.

End Der_write_tags.
