Require Import Core.Core Core.StructNormalizer VstLib Callback.Dummy
        Boolean.Exec ErrorWithWriter DWT.Vst.
Require Import VST.floyd.proofauto.
Require Import Clight.dummy Clight.BOOLEAN.
Require Import Core.Notations. 

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

(* DWT compspecs *)
Instance Change1 : change_composite_env CompSpecs Vst.CompSpecs.
Proof. make_cs_preserve CompSpecs Vst.CompSpecs. Defined.

Instance Change2 : change_composite_env Vst.CompSpecs CompSpecs.
Proof. make_cs_preserve Vst.CompSpecs CompSpecs. Defined.

(* Callback compspecs *)
Instance Change3 : change_composite_env Dummy.CompSpecs CompSpecs.
Proof. make_cs_preserve Dummy.CompSpecs CompSpecs. Defined.

Instance Change4 : change_composite_env CompSpecs Dummy.CompSpecs.
Proof. make_cs_preserve CompSpecs Dummy.CompSpecs. Defined.

Open Scope Z.

Section Boolean_der_encode.

Definition tags_enc_len td :=  
  match evalErrW (Exec.der_write_tags td) [] with 
  | Some v => encoded v
  | None => 0
  end.

Definition bool_enc_len td b := 
  match evalErrW (bool_encoder td b) [] with
  | Some v => encoded v
  | None => 0
  end.

Definition bool_der_encode_spec : ident * funspec :=
  DECLARE _BOOLEAN_encode_der
    WITH res: val,  sptr_p : val, sptr_val : int, 
         td_p : val, td : TYPE_descriptor,
         tag_mode : Z, tag : Z,
         app_key_p : val, cb_p : val
    PRE [tptr enc_rval_s, tptr type_descriptor_s, tptr tvoid, tint, 
         tuint, tptr cb_type, tptr tvoid]
      PROP (decoder_type td = BOOLEAN_t)
      PARAMS (res; td_p; sptr_p; Vint (Int.repr tag_mode);
              Vint (Int.repr tag); cb_p; app_key_p)
      GLOBALS ()
      SEP (data_at_ Tsh enc_rval_s res;
           data_at_ Tsh type_descriptor_s td_p; 
           data_at Tsh tint (Vint sptr_val) sptr_p;
           (* Callback *)
           data_at_ Tsh tvoid app_key_p;
           valid_pointer cb_p)
    POST [tvoid]
      PROP ()
      LOCAL ()
      let res_val := 
          match evalErrW (bool_encoder td (bool_of_int sptr_val)) [] with 
                     | Some v => mk_enc_rval (encoded v) Vzero Vzero 
                     | None => mk_enc_rval (-1) td_p sptr_p end in
      SEP (data_at_ Tsh type_descriptor_s td_p; 
           data_at Tsh tint (Vint sptr_val) sptr_p;
           data_at Tsh enc_rval_s res_val res;
           (* Callback *)
           data_at_ Tsh tvoid app_key_p;
           func_ptr' dummy_callback_spec cb_p;
           valid_pointer cb_p).

Definition Gprog := ltac:(with_library prog [der_write_tags_spec; 
                                             dummy_callback; 
                                             bool_der_encode_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog 
                                     (normalize_function f_BOOLEAN_encode_der
                                                         composites)
                                     bool_der_encode_spec.
Proof.
  start_function. 
  rename H into Dt.
  forward.
  forward_call (td_p, td, 1, tag_mode, 0, tag, app_key_p, cb_p).
  rewrite Exec.eval_dwt_boolean by assumption.
  unfold_data_at_ v_erval; unfold_data_at (data_at _ _ _ v_erval).
  repeat forward.
  forward_if; [contradiction|clear H].
  deadvars!.
  forward_if (
      PROP ( )
      LOCAL (temp _st sptr_p;
             lvar _bool_value tuchar v_bool_value;
             lvar _erval (Tstruct _asn_enc_rval_s noattr) v_erval; 
             temp __res res;
             temp _cb cb_p; temp _app_key app_key_p)
      SEP (data_at Tsh tuchar (Vint (Int.zero_ext 8 (Int.repr (Byte.unsigned (byte_of_bool (bool_of_int sptr_val)))))) 
                   v_bool_value;
           data_at_ Tsh type_descriptor_s td_p; 
           data_at_ Tsh tvoid app_key_p;
           func_ptr' dummy_callback_spec cb_p;
           field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _encoded) 
                    (Vint (Int.repr 2)) v_erval; 
           field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _failed_type) 
                    (default_val (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) 
                    v_erval; 
           field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _structure_ptr) 
                    (default_val (tptr tvoid)) v_erval; 
           data_at_ Tsh enc_rval_s res; 
           data_at Tsh tint (Vint sptr_val) sptr_p; 
           valid_pointer cb_p)).
  * (* if(cb) = true *)
    forward.
    (* bool_value = *st ? 0xff : 0; /* 0xff mandated by DER */ *)
    forward_if (
        PROP()
        LOCAL(temp _t'2 (match execErrW (bool_encoder td (bool_of_int sptr_val)) [] with 
                         | Some ([_; _; res]) => Vubyte res
                         | Some _ => Vint sptr_val
                         | None => Vint sptr_val end);
              temp _st sptr_p; 
              lvar _bool_value tuchar v_bool_value; 
              lvar _erval (Tstruct _asn_enc_rval_s noattr) v_erval; 
              temp __res res; temp _cb cb_p;
              temp _app_key app_key_p)
        SEP(data_at_ Tsh tuchar v_bool_value;
            data_at_ Tsh tvoid app_key_p;
            data_at_ Tsh type_descriptor_s td_p; 
            func_ptr' dummy_callback_spec cb_p;
            field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _encoded) 
                     (Vint (Int.repr 2)) v_erval; 
            field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _failed_type) 
                     (default_val (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) 
                     v_erval; 
            field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _structure_ptr) 
                     (default_val (tptr tvoid)) v_erval; 
            data_at_ Tsh enc_rval_s res; 
            data_at Tsh tint (Vint sptr_val) sptr_p; 
            valid_pointer cb_p)).
    - (* if(b) = true *)
      forward.
      entailer!.
      rewrite exec_boolean_enc by assumption.
      unfold bool_of_int, byte_of_bool, Vubyte;
        destruct Int.eq eqn:S; [apply int_eq_e in S; congruence| reflexivity].
    - (* if(b) = false *)
      forward.
      entailer!.
      rewrite exec_boolean_enc by assumption.
      unfold bool_of_int, byte_of_bool, Vubyte;
        destruct Int.eq eqn:S; [f_equal | apply int_eq_false_e in S; congruence].
    - forward.
      deadvars!.
      rewrite exec_boolean_enc by assumption.
      simpl.
      forward_call (v_bool_value, 1, app_key_p).
      rep_omega.
      forward_if; [congruence|].
      ** (* cb() >= 0 *)
        forward.
        entailer!.
  * (* post if *)
    forward.
    rewrite H; entailer!.
  * (* if(cb) = false *)
    repeat forward.
    deadvars!.
    forward_loop (
        PROP ( )
        LOCAL (lvar _bool_value tuchar v_bool_value; 
            lvar _erval (Tstruct _asn_enc_rval_s noattr) v_erval; 
            temp __res res)
        SEP (data_at Tsh tuchar 
                     (Vint 
                        (Int.zero_ext 8 
                                      (Int.repr (Byte.unsigned (byte_of_bool (bool_of_int sptr_val))))))
                     v_bool_value; 
             data_at_ Tsh type_descriptor_s td_p; data_at_ Tsh tvoid app_key_p; 
             func_ptr' dummy_callback_spec cb_p; 
             field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _encoded) 
                      (Vint (Int.repr 2 + Int.repr 1)%int) v_erval; 
             field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _failed_type) 
                      (default_val (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) v_erval; 
             field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _structure_ptr) 
                      (default_val (tptr tvoid)) v_erval; data_at_ Tsh enc_rval_s res; 
             data_at Tsh tint (Vint sptr_val) sptr_p; valid_pointer cb_p)).
    - entailer!.
    - unfold_data_at_ res; unfold_data_at (data_at _ _ _ res).
      repeat forward.
      rewrite eval_boolean_enc by assumption.
      unfold_data_at (data_at _ _ _ res); unfold_data_at_ v_erval; 
        unfold_data_at (data_at _ _ _ v_erval).
      cbn.
      entailer!.
Qed.

End Boolean_der_encode.
