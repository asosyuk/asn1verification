Require Import Core.Core Core.StructNormalizer VstLib Callback.Overrun
        Boolean.Exec ErrorWithWriter DWT.Vst.
Require Import VST.floyd.proofauto Psatz.
Require Import Clight.BOOLEAN.
Require Import Core.Notations. 

Definition new_cs := composites ++ (match find_cs 
                                            asn_application._overrun_encoder_key 
                                            asn_application.composites with
                      | Some r => [r]
                      | None => []
                      end).

Definition Vprog : varspecs. 
Proof.
  set (cs := new_cs).
  set (gd := global_definitions).
  set (pi := public_idents).
  unfold new_cs in cs.
  simpl (composites ++
           match
             find_cs
               asn_application._overrun_encoder_key
               asn_application.composites
           with
           | Some r => [r]
           | None => []
           end) in cs.
  set (prog := Clightdefs.mkprogram cs gd pi _main Logic.I).
  mk_varspecs prog. 
Defined.

Instance CompSpecs : compspecs. 
Proof.
  set (cs := new_cs).
  set (gd := global_definitions).
  set (pi := public_idents).
  unfold new_cs in cs.
  simpl (composites ++
           match
             find_cs
               asn_application._overrun_encoder_key
               asn_application.composites
           with
           | Some r => [r]
           | None => []
           end) in cs.
  set (prog := Clightdefs.mkprogram cs gd pi _main Logic.I).
  make_compspecs prog.
Defined.

(* DWT compspecs *)
Instance Change1 : change_composite_env CompSpecs Vst.CompSpecs.
Proof. make_cs_preserve CompSpecs Vst.CompSpecs. Defined.

Instance Change2 : change_composite_env Vst.CompSpecs CompSpecs.
Proof. make_cs_preserve Vst.CompSpecs CompSpecs. Defined.

(* Callback compspecs *)
Instance Change3 : change_composite_env Overrun.CompSpecs CompSpecs.
Proof. make_cs_preserve Overrun.CompSpecs CompSpecs. Defined.

Instance Change4 : change_composite_env CompSpecs Overrun.CompSpecs.
Proof. make_cs_preserve CompSpecs Overrun.CompSpecs. Defined.

Open Scope Z.

Section Boolean_der_encode_primitive.

Definition bool_der_encode_spec : ident * funspec :=
  DECLARE _BOOLEAN_encode_der
    WITH res: val,  sptr_p : val, sptr_val : int, 
         td_p : val, td : TYPE_descriptor,
         tag_mode : Z, tag : Z,
         cb_p : val, 
         app_key_p : val,
         (* overrun callback destination buffer *)
         buf_p : val, buf_size : Z, computed_size : Z
    PRE [tptr enc_rval_s, tptr type_descriptor_s, tptr tvoid, tint, 
         tuint, tptr cb_type, tptr tvoid]
      PROP (decoder_type td = BOOLEAN_t;
            isptr(buf_p)) 
      PARAMS (res; td_p; sptr_p; Vint (Int.repr tag_mode);
             Vint (Int.repr tag); cb_p; app_key_p)
      GLOBALS ()
      SEP (
           (if buf_size <? computed_size + size
            then emp 
            else memory_block Tsh size (offset_val computed_size buf_p));
           data_at_ Tsh enc_rval_s res;
           data_at_ Tsh type_descriptor_s td_p; 
           data_at Tsh tint (Vint sptr_val) sptr_p;
           data_at Tsh enc_key_s (mk_enc_key buf_p buf_size computed_size) 
                   app_key_p;
           valid_pointer cb_p;          
           func_ptr' callback cb_p)
    POST [tvoid]
      PROP ()
      LOCAL ()
      SEP (let res_val := 
               match evalErrW (bool_encoder td (bool_of_int sptr_val)) [] with 
                          | Some v => mk_enc_rval (encoded v) Vzero 
                          | None => mk_enc_rval (-1) sptr_p end in
           data_at Tsh enc_rval_s res_val res;
           data_at_ Tsh type_descriptor_s td_p; 
           data_at Tsh tint (Vint sptr_val) sptr_p;
           (* In the end we're know result, so we don't need size anymore *)
           let tags_len := 
               match evalErrW (Exec.der_write_tags td) [] with
               | Some v => encoded v
               | None => 0 end in 
           (let arr := 
               match execErrW (bool_encoder td (bool_of_int sptr_val)) [] with 
               | Some res => res
               | None => [] end in
           (let size := if Zlength arr =? 0 then tags_len else Zlength arr in
           (if buf_size <? computed_size + size
            then data_at Tsh enc_key_s 
                         (mk_enc_key buf_p 0 (computed_size + size)) app_key_p
            else (data_at Tsh (tarray tuchar computed_size) (map Vubyte arr) 
                          (offset_val computed_size buf_p) * 
                  data_at Tsh enc_key_s 
                          (mk_enc_key buf_p buf_size (computed_size + size))    
                          app_key_p))));
           valid_pointer cb_p; 
           func_ptr' callback cb_p).

Definition Gprog := ltac:(with_library prog [der_write_tags_spec; 
                                             callback_overrun_spec; 
                                             bool_der_encode_spec]).

Definition if_post1 cb_p sptr_p res bool_p erval_p td_p tag_mode 
           tag app_key_p td sptr_val cb_spec buf_p buf_size computed_size := 
  PROP(is_pointer_or_null(cb_p)
       (* der_write_tags writes 2 tags(bytes) to buffer *)
       (*computed_size = (computed_size + 2)%Z*))
  LOCAL(temp _t'6 (Vint (Int.repr 2)); 
        temp _t'1 (Vint (Int.repr (encoded {| encoded := 2 |}))); 
        temp _st sptr_p; lvar _bool_value tuchar bool_p;
        lvar _erval (Tstruct _asn_enc_rval_s noattr) erval_p; 
        temp __res res; temp _td td_p; temp _sptr sptr_p; 
        temp _tag_mode (Vint (Int.repr tag_mode)); 
        temp _tag (Vint (Int.repr tag)); 
        temp _cb (cb_p); temp _app_key app_key_p) 
  SEP(data_at_ Tsh type_descriptor_s td_p; 
      data_at_ Tsh enc_rval_s res; 
      let arr := match execErrW (Exec.der_write_tags td) [] with
                 | Some r => r
                 | None => [] end in
      let size := Zlength arr in
      (if buf_size <? computed_size + size
       then data_at Tsh enc_key_s 
                    (mk_enc_key buf_p 0 (computed_size + size)) app_key_p
       else (data_at Tsh (tarray tuchar computed_size) (map Vubyte arr) 
                     (offset_val computed_size buf_p) * 
             data_at Tsh enc_key_s 
                     (mk_enc_key buf_p buf_size (computed_size + size))    
                     app_key_p));
      func_ptr' cb_spec (cb_p); 
      (match (cb_p) with
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
      valid_pointer (cb_p)).

Definition if_post2 sptr_val app_key_p v_bool_value cb_spec cb_p v_erval 
           td_p res sptr_p tag_mode tag buf_p buf_size computed_size size := 
  PROP()
  LOCAL(temp _t'6 (Vint (Int.repr 2));
        temp _t'1 (Vint (Int.repr (encoded {| encoded := 2 |}))); 
        temp _st sptr_p; lvar _bool_value tuchar v_bool_value;
        lvar _erval (Tstruct _asn_enc_rval_s noattr) v_erval; 
        temp __res res; temp _td td_p; temp _sptr sptr_p;
        temp _tag_mode (Vint (Int.repr tag_mode)); 
        temp _tag (Vint (Int.repr tag)); 
        temp _cb (cb_p); temp _app_key app_key_p;
        temp _t'2 (Vint (Int.repr (if (bool_of_int sptr_val) then 255 else 0))))
  SEP(if buf_size <? computed_size + size 
      then data_at Tsh enc_key_s (mk_enc_key buf_p 0 computed_size) app_key_p 
      else data_at Tsh (tarray tuchar 2) (map Vubyte [1%byte; 1%byte]) 
                   (offset_val computed_size buf_p) * 
           data_at Tsh enc_key_s (mk_enc_key buf_p buf_size (computed_size + 2)) 
                   app_key_p; 
      (if buf_size <? computed_size + size2
       then emp
       else memory_block Tsh size2 (offset_val computed_size buf_p));
      data_at_ Tsh type_descriptor_s td_p; func_ptr' cb_spec cb_p;
      data_at_ Tsh tuchar v_bool_value;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr)
                (DOT _encoded) (Vint (Int.repr 2)) v_erval;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr)
                (DOT _failed_type)
                 (default_val
                     (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                  v_erval;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr)
                (DOT _structure_ptr) (default_val (tptr tvoid))
                 v_erval; data_at_ Tsh enc_rval_s res;
      data_at Tsh tint (Vint sptr_val) sptr_p;
      valid_pointer cb_p).

Definition loop_inv sptr_p v_bool_value v_erval res td_p tag_mode tag cb_p 
           app_key_p cb_spec sptr_val buf_p buf_size computed_size size :=
  PROP()
  LOCAL(temp _t'4 (Vint (Int.repr 2)); 
        temp _t'6 (Vint (Int.repr 2)); temp _t'1 (Vint (Int.repr 2)); 
        temp _st sptr_p; lvar _bool_value tuchar v_bool_value;
        lvar _erval (Tstruct _asn_enc_rval_s noattr) v_erval;
        temp __res res; temp _td td_p; temp _sptr sptr_p;
        temp _tag_mode (Vint (Int.repr tag_mode));
        temp _tag (Vint (Int.repr tag)); temp _cb (cb_p);
        temp _app_key app_key_p)
  SEP(data_at_ Tsh type_descriptor_s td_p;
      data_at_ Tsh enc_rval_s res; 
      data_at Tsh enc_key_s (mk_enc_key buf_p buf_size computed_size) app_key_p;
      (if buf_size <? computed_size + size 
       then emp 
       else memory_block Tsh 1 (offset_val 2 buf_p));
      func_ptr' cb_spec (cb_p);
      data_at Tsh tuchar (Vubyte (byte_of_bool (bool_of_int sptr_val))) v_bool_value;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _encoded) 
               (Vint (Int.add (Int.repr 2) (Int.repr 1))) v_erval;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _failed_type)  
               (default_val (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
               v_erval;
      field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _structure_ptr)
               (default_val (tptr tvoid)) v_erval;
      data_at Tsh tint (Vint sptr_val) sptr_p;
      valid_pointer (cb_p)).

Theorem bool_der_encode : semax_body Vprog Gprog 
                                     (normalize_function f_BOOLEAN_encode_der
                                                         composites)
                                     bool_der_encode_spec.
Proof.
  start_function; rename H into DT; rename H0 into Bf_ptr.
  forward.
  (* TODO specify data array with der_write_tags output *)
  forward_call (td_p, td, 1, tag_mode, 0, tag, cb_p, app_key_p, buf_p, buf_size, 
                computed_size).
  
  rewrite Exec.eval_dwt_boolean by assumption; 
    rewrite Exec.exec_dwt_boolean by assumption; unfold encoded.
  unfold_data_at_ v_erval; unfold_data_at (data_at _ _ _ v_erval).
  forward.
  forward.
  forward_if; [contradiction|clear H].
  forward_if (if_post1 cb_p sptr_p res v_bool_value v_erval td_p tag_mode tag 
                       app_key_p td sptr_val callback buf_p buf_size computed_size); 
    unfold if_post1.
  * (* if(cb) = true *)
    forward.
    (* bool_value = *st ? 0xff : 0; /* 0xff mandated by DER */ *)
    forward_if (if_post2 sptr_val app_key_p v_bool_value callback cb_p v_erval 
                         td_p res sptr_p tag_mode tag buf_p buf_size 
                         computed_size 2 size); unfold if_post2.
    - (* if(b) = true *)
      Intros size.
      forward; unfold if_post2; Exists size; entailer!.
      unfold bool_of_int.
      destruct (sptr_val == 0)%int eqn : S; 
        [eapply int_eq_e in S; contradiction | auto ].
    - (* if(b) = false *)
      Intros size.
      forward; unfold if_post2; Exists size; entailer!.
    - 
      Intros size.
      forward.
      rewrite <-data_at_tuchar_singleton_array_eq.
      forward_call ([(Int.zero_ext 8 (Int.repr (if bool_of_int sptr_val 
                                                then 255 
                                                else 0)))], 
                    v_bool_value, 1, app_key_p, buf_p, buf_size, computed_size).
      entailer!.
      cbn.
      forward_if; [congruence|].
      ** (* cb() >= 0 *)
        unfold if_post1; forward.
         entailer!.
         destruct cb_p; intuition.
         rewrite exec_boolean_enc by assumption.
         unfold bool_of_int.
         destruct (sptr_val == 0)%int eqn : S; entailer!.
       (*    try (erewrite <- data_at_tuchar_singleton_array_eq; 
                entailer!).
         unfold len; simpl.
         unfold byte_of_bool.
         entailer!.
         normalize.
         unfold Vubyte.
         entailer!.
         erewrite <- data_at_tuchar_singleton_array_eq.
         entailer!. *)
  * (* post if *)
    forward; unfold if_post1.
    rewrite H; entailer!.
  * (* if(cb) = false *)
    rewrite exec_boolean_enc by assumption.
    Intros.
    forward.
    forward.
    unfold mk_enc_rval, encoded, last.
    forward_loop (loop_inv sptr_p v_bool_value v_erval res td_p tag_mode tag
                                cb_p app_key_p dummy_callback sptr_val); unfold loop_inv.
    - entailer!.
      destruct cb_p; intuition.
    - 
      unfold_data_at_ res; unfold_data_at (data_at _ _ _ res).
      repeat forward.
      rewrite eval_boolean_enc by assumption.
      unfold mk_enc_rval, encoded, last.
      unfold_data_at (data_at _ _ _ res).
      unfold_data_at_  v_erval; unfold_data_at (data_at _ _ _ v_erval).
      entailer!.
Qed.

End Boolean_der_encode_primitive.
