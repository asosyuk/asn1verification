Require Import Core.Core Core.StructNormalizer VstLib VstCallback
        BooleanExecSpec ErrorWithWriter DWTVSTSpec.
Require Import VST.floyd.proofauto Psatz.
Require Import Clight.asn_application Clight.BOOLEAN.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Instance Change1 : change_composite_env CompSpecs DWTVSTSpec.CompSpecs.
Proof. make_cs_preserve CompSpecs DWTVSTSpec.CompSpecs. Defined.
Instance Change2 : change_composite_env DWTVSTSpec.CompSpecs CompSpecs.
Proof. make_cs_preserve DWTVSTSpec.CompSpecs CompSpecs. Defined.

Open Scope Z.

Section Boolean_der_encode_primitive.

Definition int_of_bool (b : bool) := Int.repr (if b then 255 else 0).

Definition cb := _overrun_encoder_cb.

Definition bool_der_encode_spec : ident * funspec :=
  DECLARE _BOOLEAN_encode_der
    WITH sptr_p : val, sptr_val : Z, gv : globals,
         (* pointer to the DEF table for the type decoded *)
         td_p : val, td : TYPE_descriptor,
         tag_mode : Z, tag : Z,
         (* local defs *)
         b : bool, res : val, b_val : val,
         (* callback pointer *)
         (*cb_p : val, *)
         (* callback argument pointer *)
         app_p : val, app_key_val : val
    PRE[(* added by clightgen - since returning structs is not supported *) 
        tptr enc_rval_s, tptr type_descriptor_s, tptr tvoid, tint, 
        tuint, tptr cb_type, tptr tvoid]
      PROP((* If I understood this correctly there is an implicit contract
              on this function, that is, type_descriptor equals bool type 
              if it was passed here, since there isn't any check on tags for it
              to be bool. Alternatively there may not be any implicit contract
              in which case it can lead to malformed output which needs to be
              checked somewhere. Maybe decoder checks for it... *)
           decoder_type td = BOOLEAN_t)
      PARAMS(res; td_p; sptr_p; Vint (Int.repr tag_mode);
             Vint (Int.repr tag); (gv cb); app_p)
      GLOBALS(gv)
      SEP((* td points to td with readable permission *) 
          data_at_ Tsh enc_rval_s res;
          data_at_ Tsh type_descriptor_s td_p; 
          data_at Tsh tint (Vint (int_of_bool b)) sptr_p;
          data_at_ Tsh tvoid app_p;
          valid_pointer (gv cb); func_ptr callback (gv cb))
    POST [tvoid]
      PROP()
      LOCAL()
      SEP((* Unchanged by the execution : *)
          data_at Tsh enc_rval_s 
                  (match evalErrW (bool_encoder td b) [] with
                   | Some v => construct_enc_rval (encoded v) (Vint (Int.repr 0))
                   | None => construct_enc_rval (-1) sptr_p
                   end) res;
          data_at_ Tsh type_descriptor_s td_p ; 
          data_at Tsh tint (Vint (int_of_bool b)) sptr_p ;
          data_at_ Tsh tvoid app_p ;
          valid_pointer (gv cb); func_ptr callback (gv cb)).

Definition Gprog := ltac:(with_library prog [der_write_tags_spec; callback_spec;
                                               bool_der_encode_spec]).

Definition if_post1 (gv : globals) cb sptr_p res bool_p erval_p td_p tag_mode 
           tag app_p td b cb_spec := 
  PROP(is_pointer_or_null (gv cb))
  LOCAL(temp _t'6 (Vint (Int.repr 2)); 
        temp _t'1 (Vint (Int.repr (encoded {| encoded := 2 |}))); 
        temp _st sptr_p; lvar _bool_value tuchar bool_p;
        lvar _erval (Tstruct _asn_enc_rval_s noattr) erval_p; 
        temp __res res; temp _td td_p; temp _sptr sptr_p; 
        temp _tag_mode (Vint (Int.repr tag_mode)); 
        temp _tag (Vint (Int.repr tag)); 
        temp _cb (gv cb); temp _app_key app_p) 
  SEP(data_at_ Tsh type_descriptor_s td_p; 
      data_at_ Tsh enc_rval_s res;
      data_at_ Tsh tvoid app_p; func_ptr cb_spec (gv cb); 
      (match (gv cb) with
       | Vint _ => data_at_ Tsh tuchar bool_p
       | _ => data_at Tsh tuchar 
                     (Vbyte (match execErrW (bool_encoder td b) [] with 
                             | Some v => last v (Byte.repr (-1)) 
                             | None => (Byte.repr (-1)) 
                             end)) bool_p end);
      field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _encoded) 
               (Vint (Int.repr 2)) erval_p;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _failed_type) 
               (default_val (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) 
               erval_p;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _structure_ptr) 
               (default_val (tptr tvoid)) erval_p; 
      data_at Tsh tint (Vint (int_of_bool b)) sptr_p; 
      valid_pointer (gv cb)).

Definition if_post2 (gv : globals) (b : bool) app_p (v_bool_value : val) cb_spec 
           cb v_bool_value v_erval td_p res sptr_p := 
  PROP()
  LOCAL(temp _cb (gv cb); temp _app_key app_p; 
        lvar _bool_value tuchar v_bool_value; 
        temp _t'2 (Vint (Int.repr (if b then 255 else 0))))
  SEP(data_at_ Tsh type_descriptor_s td_p;
      data_at_ Tsh tvoid app_p; func_ptr cb_spec (gv cb);
      data_at_ Tsh tuchar v_bool_value;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _encoded) 
               (Vint (Int.repr 2)) v_erval;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _failed_type) 
               (default_val (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) 
               v_erval;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _structure_ptr) 
               (default_val (tptr tvoid)) v_erval; 
      data_at_ Tsh enc_rval_s res;
      data_at Tsh tint (Vint (int_of_bool b)) sptr_p; valid_pointer (gv cb)).

Definition loop_inv (gv : globals) sptr_p v_bool_value v_erval res td_p tag_mode 
           tag cb app_p (cb_spec : funspec) b :=
  PROP()
  LOCAL(temp _t'4 (Vint (Int.repr 2)); 
        temp _t'6 (Vint (Int.repr 2)); 
        temp _t'1 (Vint (Int.repr 2)); temp _st sptr_p; 
        lvar _bool_value tuchar v_bool_value; 
        lvar _erval (Tstruct _asn_enc_rval_s noattr) v_erval; 
        temp __res res; temp _td td_p; temp _sptr sptr_p; 
        temp _tag_mode (Vint (Int.repr tag_mode)); 
        temp _tag (Vint (Int.repr tag)); temp _cb (gv cb); 
        temp _app_key app_p)
  SEP(data_at_ Tsh type_descriptor_s td_p;
      data_at_ Tsh enc_rval_s res;
      data_at_ Tsh tvoid app_p; func_ptr callback (gv cb);
      data_at Tsh tuchar (Vbyte (bool_to_byte b)) v_bool_value;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr)
        (DOT _encoded)
        (Vint (Int.add (Int.repr 2) (Int.repr 1))) v_erval;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr)
        (DOT _failed_type)
        (default_val
           (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
        v_erval;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr)
        (DOT _structure_ptr) (default_val (tptr tvoid)) v_erval;
      data_at Tsh tint (Vint (int_of_bool b)) sptr_p;
      valid_pointer (gv cb)).

Theorem bool_der_encode : semax_body Vprog Gprog 
                                     (normalize_function 
                                        f_BOOLEAN_encode_der composites) 
                                     bool_der_encode_spec.
Proof.
  start_function; rename H into DT.
  forward.
  forward_call (td_p, td, 1, tag_mode, 0, tag, (gv cb), app_p, app_key_val).
  rewrite DWTExecSpec.eval_dwt_boolean by assumption.
  unfold_data_at_ v_erval; unfold_data_at (data_at _ _ _ v_erval).
  forward.
  forward.
  forward_if; [contradiction|clear H].
  forward_if (if_post1 gv cb sptr_p res v_bool_value v_erval 
                       td_p tag_mode tag app_p td b callback).
  * (* if(cb) = true *)
    forward.
    (* bool_value = *st ? 0xff : 0; /* 0xff mandated by DER */ *)
    forward_if (if_post2 gv b app_p v_bool_value callback cb
                         v_bool_value v_erval td_p res sptr_p).
    - (* if(b) = true *)
      forward; unfold if_post2; entailer!.
      destruct b; [auto|contradiction].
    - (* if(b) = false *)
      forward; unfold if_post2; entailer!.
      destruct b; unfold int_of_bool in H2; [discriminate|auto].
    - unfold if_post2.
      Intros.
      forward.
      (* Definition cb_spec : funspec := 
         WITH buf_addr : val, buf : val, size : Z, app_addr : val, app_key : val *)
      eapply (make_func_ptr _overrun_encoder_cb).
      reflexivity.
      reflexivity.
      reflexivity.
      cbn. admit.
      instantiate (1 := (gv cb)).
      admit.
      (* make_func_ptr _overrun_encoder_cb. *)
      (* forward_call ([bool_to_byte b], v_bool_value, 1, app_p). *)
  * (* post if *)
    forward.
    unfold if_post1.
    rewrite H; entailer!.
  * (* if(cb) = false *)
    unfold if_post1.
    rewrite exec_boolean_enc by assumption.
    Intros.
    (*{
      destruct (gv cb) eqn:C; unfold last; unfold is_pointer_or_null in H; 
        intuition.
    }*)
    forward.
    forward.
    unfold construct_enc_rval, encoded, last.
    forward_loop (loop_inv gv sptr_p v_bool_value v_erval res td_p tag_mode tag
                                cb app_p callback b); unfold loop_inv.
    - entailer!.
      destruct (gv cb); intuition.
    - 
      unfold_data_at_ res.
      unfold_data_at (data_at _ _ _ res).
      repeat forward.
      rewrite eval_boolean_enc by assumption.
      unfold construct_enc_rval, encoded, last.
      unfold_data_at (data_at _ _ _ res).
      unfold_data_at_  v_erval; unfold_data_at (data_at _ _ _ v_erval).
      entailer!.
Admitted.     

End Boolean_der_encode_primitive.
