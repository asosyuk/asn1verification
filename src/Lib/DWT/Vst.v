Require Import Core.Core Core.StructNormalizer VstLib DWT.Exec 
        ErrorWithWriter Callback.Overrun.
Require Import VST.floyd.proofauto.
Require Import Clight.der_encoder.

Definition composites := composites ++ (match find_cs 
                                            asn_application._overrun_encoder_key 
                                            asn_application.composites with
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

Definition cbi := asn_application._overrun_encoder_cb.

Definition der_write_tags_spec : ident * funspec :=
  DECLARE _der_write_tags
  WITH gv : globals,
       (* pointer to type descriptor structure *) 
       td_p : val, td : TYPE_descriptor,
       struct_len: Z, tag_mode : Z, last_tag_form : Z, tag : Z,
       (* callback argument pointer *)
       app_p : val,
       (* overrun_encoder_key fields *)
       buf_p : val, buf_size : Z, computed_size : Z
  PRE[tptr type_descriptor_s, tuint, tint, tint, tuint, 
      tptr cb_type, tptr tvoid]
    PROP()
    PARAMS(td_p; Vint (Int.repr struct_len); Vint (Int.repr tag_mode);
           Vint (Int.repr last_tag_form); Vint (Int.repr tag); (gv cbi); app_p)
    GLOBALS(gv)
    SEP(data_at_ Tsh type_descriptor_s td_p ; 
        data_at Tsh enc_key_s (mk_enc_key buf_p buf_size computed_size) app_p)
    POST[tint]
      PROP()
      LOCAL(temp ret_temp 
                 (Vint (Int.repr (match evalErrW (der_write_tags td) [] with
                                  | Some w => encoded w
                                  | None => -1
                                  end))))
      SEP(let res := evalErrW (der_write_tags td) [] in 
          let size := match res with    
                      | Some v => encoded v 
                      | None => 0 end in
          let res_ := execErrW (der_write_tags td) [] in
          let arr := match res_ with
                     | Some r => r
                     | None => [] end in
          (if buf_size <? computed_size + size
           then data_at Tsh enc_key_s 
                   (mk_enc_key buf_p 0 (computed_size + size)) app_p
           else 
             (data_at Tsh (tarray tuchar size) (map Vubyte arr) 
                      (offset_val computed_size buf_p) *
              data_at Tsh enc_key_s 
                      (mk_enc_key buf_p buf_size (computed_size + size)) 
                      app_p));
          data_at_ Tsh type_descriptor_s td_p; 
          func_ptr' callback (gv cbi)).

Definition Gprog := ltac:(with_library prog [der_write_tags_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog f_der_write_tags 
                                     der_write_tags_spec.
Proof.
  start_function.
Admitted.

End Der_write_tags.
