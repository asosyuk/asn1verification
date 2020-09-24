Require Import Core.Core Core.StructNormalizer VstLib DWT.Exec 
        ErrorWithWriter Callback.Dummy.
Require Import VST.floyd.proofauto.
Require Import Clight.dummy Clight.der_encoder.

Definition composites := composites ++ (match find_cs 
                                            dummy._dummy
                                            dummy.composites with
                      | Some r => [r]
                      | None => []
                      end).

Definition Vprog : varspecs. 
Proof.
  set (cs := composites).
  set (gd := global_definitions).
  set (pi := public_idents).
  unfold composites in cs.
  simpl in cs.
  set (prog := Clightdefs.mkprogram cs gd pi _main Logic.I).
  mk_varspecs prog. 
Defined.

Instance CompSpecs : compspecs. 
Proof.
  set (cs := composites).
  set (gd := global_definitions).
  set (pi := public_idents).
  unfold composites in cs.
  simpl in cs.
  set (prog := Clightdefs.mkprogram cs gd pi _main Logic.I).
  make_compspecs prog.
Defined.

Open Scope Z.

Section Der_write_tags.

Definition der_write_tags_spec : ident * funspec :=
  DECLARE _der_write_tags
  WITH (* pointer to type descriptor structure *) 
       td_p : val, td : TYPE_descriptor,
       struct_len: Z, tag_mode : Z, last_tag_form : Z, tag : Z,
       (* callback argument pointer *)
       app_p : val,
       (* callback fields *)
       cb_p : val
  PRE[tptr type_descriptor_s, tuint, tint, tint, tuint, 
      tptr cb_type, tptr tvoid]
    PROP()
    PARAMS(td_p; Vint (Int.repr struct_len); Vint (Int.repr tag_mode);
           Vint (Int.repr last_tag_form); Vint (Int.repr tag); cb_p; app_p)
    GLOBALS()
    SEP(data_at_ Tsh type_descriptor_s td_p ; 
        data_at_ Tsh tvoid app_p)
    POST[tint]
      PROP()
      LOCAL(temp ret_temp 
                 (Vint (Int.repr (match evalErrW (der_write_tags td) [] with
                                  | Some w => encoded w
                                  | None => -1
                                  end))))
      SEP(data_at_ Tsh type_descriptor_s td_p; 
          data_at_ Tsh tvoid app_p;
          func_ptr' dummy_callback_spec cb_p).

Definition Gprog := ltac:(with_library prog [der_write_tags_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog f_der_write_tags 
                                     der_write_tags_spec.
Proof.
  start_function.
Admitted.

End Der_write_tags.
