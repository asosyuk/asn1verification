Require Import Core.Core Core.StructNormalizer VstLib VstCallback
        Boolean.Exec ErrorWithWriter DWT.Vst.
Require Import VST.floyd.proofauto Psatz.
Require Import Clight.asn_application Clight.BOOLEAN.

Require Import Core.Notations. 

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Instance Change1 : change_composite_env CompSpecs DWT.Vst.CompSpecs.
Proof. make_cs_preserve CompSpecs DWT.Vst.CompSpecs. Defined.

Instance Change2 : change_composite_env DWT.Vst.CompSpecs CompSpecs.
Proof. make_cs_preserve DWT.Vst.CompSpecs CompSpecs. Defined.

Open Scope Z.

Section Boolean_der_encode_primitive.

Definition cb := _overrun_encoder_cb.

Definition bool_of_int (i : int) := 
  if (i == 0)%int then false else true.

Definition bool_der_encode_spec : ident * funspec :=
  DECLARE _BOOLEAN_encode_der
    WITH gv : globals,
         (* parameters : *)
         res: val,  sptr_p : val, sptr_val : int, 
         td_p : val, td : TYPE_descriptor,
         tag_mode : Z, tag : Z,
         (* callback pointer *)
         (*cb_p : val, *) 
         (* callback argument pointer *)                    
         app_key_p : val, app_key_val : val
    PRE [tptr enc_rval_s, tptr type_descriptor_s, tptr tvoid, tint, 
         tuint, tptr cb_type, tptr tvoid]
      PROP (decoder_type td = BOOLEAN_t) (* an implicit contract *)
      PARAMS (res; td_p; sptr_p; Vint (Int.repr tag_mode);
             Vint (Int.repr tag); gv cb; app_key_p)
      GLOBALS (gv)
      SEP (data_at_ Tsh enc_rval_s res;
           data_at_ Tsh type_descriptor_s td_p; 
           data_at Tsh tint (Vint sptr_val) sptr_p;
           data_at_ Tsh tvoid app_key_p;
           valid_pointer (gv cb);
           func_ptr callback (gv cb))
    POST [tvoid]
      PROP ()
      LOCAL ()
      SEP (let res_val := 
               match evalErrW (bool_encoder td (bool_of_int sptr_val)) [] with
               | Some v => construct_enc_rval (encoded v) Vzero
               | None => construct_enc_rval (-1) sptr_p
               end in
           data_at Tsh enc_rval_s res_val res;
           data_at_ Tsh type_descriptor_s td_p ; 
           data_at Tsh tint (Vint sptr_val) sptr_p ;
           data_at_ Tsh tvoid app_key_p ; valid_pointer (gv cb); 
           func_ptr callback (gv cb); func_ptr' callback (gv cb)).

Definition Gprog := ltac:(with_library prog [der_write_tags_spec; callback_spec;
                                               bool_der_encode_spec]).

Definition if_post1 (gv : globals) cb sptr_p res bool_p erval_p td_p tag_mode 
           tag app_key_p td sptr_val cb_spec := 
  PROP(is_pointer_or_null (gv cb))
  LOCAL(gvars gv;
        temp _t'6 (Vint (Int.repr 2)); 
        temp _t'1 (Vint (Int.repr (encoded {| encoded := 2 |}))); 
        temp _st sptr_p; lvar _bool_value tuchar bool_p;
        lvar _erval (Tstruct _asn_enc_rval_s noattr) erval_p; 
        temp __res res; temp _td td_p; temp _sptr sptr_p; 
        temp _tag_mode (Vint (Int.repr tag_mode)); 
        temp _tag (Vint (Int.repr tag)); 
        temp _cb (gv cb); temp _app_key app_key_p) 
  SEP(data_at_ Tsh type_descriptor_s td_p; 
      data_at_ Tsh enc_rval_s res; data_at_ Tsh tvoid app_key_p; 
      func_ptr cb_spec (gv cb); func_ptr' cb_spec (gv cb); 
      (match (gv cb) with
       | Vint _ => data_at_ Tsh tuchar bool_p
       | _ => data_at Tsh tuchar 
                     (Vubyte (match execErrW (bool_encoder td (bool_of_int sptr_val)) [] with 
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
      data_at Tsh tint (Vint sptr_val) sptr_p; 
      valid_pointer (gv cb)).

Definition if_post2 (gv : globals) (sptr_val : int) app_key_p (v_bool_value : val) cb_spec 
           cb v_bool_value v_erval td_p res sptr_p tag_mode tag := 
  PROP()
  LOCAL(gvars gv; temp _t'6 (Vint (Int.repr 2));
        temp _t'1 (Vint (Int.repr (encoded {| encoded := 2 |}))); 
        temp _st sptr_p; lvar _bool_value tuchar v_bool_value;
        lvar _erval (Tstruct _asn_enc_rval_s noattr) v_erval; 
        temp __res res; temp _td td_p; temp _sptr sptr_p;
        temp _tag_mode (Vint (Int.repr tag_mode)); 
        temp _tag (Vint (Int.repr tag)); 
        temp _cb (gv cb); temp _app_key app_key_p;
        temp _t'2 (Vint (Int.repr (if (bool_of_int sptr_val) then 255 else 0))))
  SEP(data_at_ Tsh type_descriptor_s td_p;
      data_at_ Tsh tvoid app_key_p; func_ptr cb_spec (gv cb);
      data_at_ Tsh tuchar v_bool_value;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _encoded) 
               (Vint (Int.repr 2)) v_erval;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _failed_type) 
               (default_val (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) 
               v_erval;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _structure_ptr) 
               (default_val (tptr tvoid)) v_erval; 
      data_at_ Tsh enc_rval_s res;
      data_at Tsh tint (Vint sptr_val) sptr_p; valid_pointer (gv cb)).

Definition loop_inv (gv : globals) sptr_p v_bool_value v_erval res td_p tag_mode 
           tag cb app_key_p (cb_spec : funspec) sptr_val :=
  PROP()
  LOCAL(gvars gv; temp _t'4 (Vint (Int.repr 2)); 
        temp _t'6 (Vint (Int.repr 2)); temp _t'1 (Vint (Int.repr 2)); 
        temp _st sptr_p; lvar _bool_value tuchar v_bool_value;
        lvar _erval (Tstruct _asn_enc_rval_s noattr) v_erval;
        temp __res res; temp _td td_p; temp _sptr sptr_p;
        temp _tag_mode (Vint (Int.repr tag_mode));
        temp _tag (Vint (Int.repr tag)); temp _cb (gv cb);
        temp _app_key app_key_p)
  SEP(data_at_ Tsh type_descriptor_s td_p;
      data_at_ Tsh enc_rval_s res; data_at_ Tsh tvoid app_key_p;
      func_ptr callback (gv cb);
func_ptr' callback (gv cb);
      data_at Tsh tuchar (Vubyte (byte_of_bool (bool_of_int sptr_val))) v_bool_value;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _encoded) 
               (Vint (Int.add (Int.repr 2) (Int.repr 1))) v_erval;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _failed_type)  
               (default_val (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
               v_erval;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _structure_ptr)
               (default_val (tptr tvoid)) v_erval;
      data_at Tsh tint (Vint sptr_val) sptr_p;
      valid_pointer (gv cb)).

Theorem bool_der_encode : semax_body Vprog Gprog 
                                     (normalize_function f_BOOLEAN_encode_der
                                                         composites)
                                     bool_der_encode_spec.
Proof.
  start_function; rename H into DT.
  forward.
  forward_call (td_p, td, 1, tag_mode, 0, tag, (gv cb), app_key_p, app_key_val).
  rewrite Exec.eval_dwt_boolean by assumption.
  unfold_data_at_ v_erval; unfold_data_at (data_at _ _ _ v_erval).
  forward.
  forward.
  forward_if; [contradiction|clear H].
  forward_if (if_post1 gv cb sptr_p res v_bool_value v_erval td_p tag_mode tag 
                       app_key_p td sptr_val callback); unfold if_post1.
  * (* if(cb) = true *)
    forward.
    (* bool_value = *st ? 0xff : 0; /* 0xff mandated by DER */ *)
    forward_if (if_post2 gv sptr_val app_key_p v_bool_value callback cb v_bool_value 
                         v_erval td_p res sptr_p tag_mode tag); unfold if_post2.
    - (* if(b) = true *)
      forward; unfold if_post2; entailer!.
      unfold bool_of_int.
      destruct (sptr_val == 0)%int eqn : S; 
        [eapply int_eq_e in S; contradiction | auto ].
    - (* if(b) = false *)
      forward; unfold if_post2; entailer!.
    - forward.
      make_func_ptr cb.
      forward_call ([sptr_val], v_bool_value, 1, app_key_p).
      forward_if; [congruence|].
      ** (* cb() >= 0 *)
        unfold if_post1; forward.
         entailer!.
         destruct (gv cb); intuition.
         rewrite exec_boolean_enc by assumption.
         unfold bool_of_int.
         destruct (sptr_val == 0)%int eqn : S; entailer!.
  * (* post if *)
    forward; unfold if_post1.
    rewrite H; entailer!.
  * (* if(cb) = false *)
    rewrite exec_boolean_enc by assumption.
    Intros.
    forward.
    forward.
    unfold construct_enc_rval, encoded, last.
    forward_loop (loop_inv gv sptr_p v_bool_value v_erval res td_p tag_mode tag
                                cb app_key_p callback sptr_val); unfold loop_inv.
    - entailer!.
      destruct (gv cb); intuition.
    - 
      unfold_data_at_ res; unfold_data_at (data_at _ _ _ res).
      repeat forward.
      rewrite eval_boolean_enc by assumption.
      unfold construct_enc_rval, encoded, last.
      unfold_data_at (data_at _ _ _ res).
      unfold_data_at_  v_erval; unfold_data_at (data_at _ _ _ v_erval).
      entailer!.
Qed.

End Boolean_der_encode_primitive.
