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
         cb_p : val, 
         app_key_p : val,
         (* overrun callback destination buffer *)
         buf_p : val, buf_size : Z, computed_size : Z
    PRE [tptr enc_rval_s, tptr type_descriptor_s, tptr tvoid, tint, 
         tuint, tptr cb_type, tptr tvoid]
      PROP (decoder_type td = BOOLEAN_t;
            isptr buf_p;
            0 <= buf_size <= Int.max_unsigned;
            0 <= computed_size <= Int.max_unsigned) 
      PARAMS (res; td_p; sptr_p; Vint (Int.repr tag_mode);
              Vint (Int.repr tag); cb_p; app_key_p)
      GLOBALS ()
      SEP (if buf_size <? (computed_size + 2) + 1
           (* this is used after dwt execution, so computed_size += 2 *)
           then emp 
           else memory_block Tsh 1 (offset_val (computed_size + 2) buf_p);
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
      let res_val := 
          match evalErrW (bool_encoder td (bool_of_int sptr_val)) [] with 
                     | Some v => mk_enc_rval (encoded v) Vzero 
                     | None => mk_enc_rval (-1) sptr_p end in
      let arr := match execErrW (bool_encoder td (bool_of_int sptr_val)) [] with 
         | Some res => res
         | None => [] end in
      let size := if Zlength arr =? 0 then tags_enc_len td else Zlength arr in
      SEP (if buf_size <? computed_size + 2 
           then emp 
           else data_at Tsh (tarray tuchar 2) (map Vubyte [1%byte; 1%byte]) 
                        (offset_val computed_size buf_p);
           data_at Tsh enc_rval_s res_val res;
           data_at_ Tsh type_descriptor_s td_p; 
           data_at Tsh tint (Vint sptr_val) sptr_p;
           if buf_size <? computed_size + size
           then data_at Tsh enc_key_s 
                        (mk_enc_key buf_p 0 (computed_size + size)) app_key_p
           else (data_at Tsh (tarray tuchar (size - tags_enc_len td)) 
                         ([Vint 
                             (Int.zero_ext 8 
                                           (Int.repr (Byte.unsigned 
                                                        (last arr (Byte.zero)))))])
                         (offset_val (computed_size + tags_enc_len td) buf_p) * 
                 data_at Tsh enc_key_s 
                         (mk_enc_key buf_p buf_size (computed_size + size))    
                         app_key_p);
           valid_pointer cb_p; 
           func_ptr' callback cb_p).

Definition Gprog := ltac:(with_library prog [der_write_tags_spec; 
                                             callback_overrun_spec; 
                                             bool_der_encode_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog 
                                     (normalize_function f_BOOLEAN_encode_der
                                                         composites)
                                     bool_der_encode_spec.
Proof.
  start_function; rename H into DT; rename H0 into Bf_ptr.
    rename H1 into Bsz; rename H2 into Bsmu. (* rename H3 into Csz; *)
    (*  rename H into Csmu; rename H5 into BsDWT; rename H6 into BsR. *)
 (* rewrite eval_boolean_enc in Csmu by assumption; unfold encoded in Csmu.
  rewrite Exec.eval_dwt_boolean in BsDWT by assumption; unfold encoded in BsDWT.
  rewrite eval_boolean_enc in BsR by assumption; unfold encoded in BsR. *)
  forward.
  forward_call (td_p, td, 1, tag_mode, 0, tag, cb_p, app_key_p, buf_p, buf_size, 
                computed_size).
  rewrite Exec.eval_dwt_boolean by assumption; 
    rewrite Exec.exec_dwt_boolean by assumption; unfold encoded.
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
      SEP (if buf_size <? computed_size + 2 + 1
           then data_at Tsh enc_key_s (mk_enc_key buf_p 0 (computed_size + 2 + 1)) 
                        app_key_p
           else data_at Tsh (tarray tuchar 1) 
                        ([Vint (Int.zero_ext 8 (Int.repr (Byte.unsigned 
                                                            (byte_of_bool 
                                                               (bool_of_int 
                                                                  sptr_val)))))]) 
                        (offset_val (computed_size + 2) buf_p) *
            data_at Tsh enc_key_s (mk_enc_key buf_p buf_size 
                                              (computed_size + 2 + 1)) app_key_p;
           let b_v := match execErrW (bool_encoder td (bool_of_int sptr_val)) 
                                     [] with 
                      | Some v => last v (Byte.repr (-1)) 
                      | None => (Byte.repr (-1)) end in
           match (cb_p) with 
           | Vint _ => data_at_ Tsh tuchar v_bool_value
           | _ => data_at Tsh tuchar (Vint (Int.zero_ext 8 (Int.repr (Byte.unsigned b_v)))) v_bool_value 
           end;
           data_at_ Tsh type_descriptor_s td_p;
           func_ptr' callback cb_p;
           field_at Tsh (Tstruct _asn_enc_rval_s noattr)
                    (DOT _encoded) (Vint (Int.repr 2)) v_erval;
           field_at Tsh (Tstruct _asn_enc_rval_s noattr)
                    (DOT _failed_type)
                    (default_val
                       (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                    v_erval;
           field_at Tsh (Tstruct _asn_enc_rval_s noattr)
                    (DOT _structure_ptr) (default_val (tptr tvoid))
                    v_erval;
           (if buf_size <? computed_size + 2 
                        then emp
                        else data_at Tsh (tarray tuchar 2) 
                                     (map Vubyte [1%byte; 1%byte]) 
                                     (offset_val computed_size buf_p));
           data_at_ Tsh enc_rval_s res;
           data_at Tsh tint (Vint sptr_val) sptr_p;
           valid_pointer cb_p)).
  * (* if(cb) = true *)
    forward.
    (* bool_value = *st ? 0xff : 0; /* 0xff mandated by DER */ *)
    forward_if (
        PROP()
        LOCAL(temp _t'2 (Vubyte (byte_of_bool (bool_of_int sptr_val)));
              temp _st sptr_p; 
              lvar _bool_value tuchar v_bool_value; 
              lvar _erval (Tstruct _asn_enc_rval_s noattr) v_erval; 
              temp __res res; temp _cb cb_p; 
              temp _app_key app_key_p)
        SEP(if buf_size <? computed_size + 2 + 1
            then emp
            else memory_block Tsh 1 (offset_val (computed_size + 2) buf_p);
            data_at_ Tsh tuchar v_bool_value;
            if buf_size <? computed_size + 2 
            then data_at Tsh enc_key_s (mk_enc_key buf_p 0 (computed_size + 2)) 
                         app_key_p 
            else data_at Tsh (tarray tuchar 2) (map Vubyte [1%byte; 1%byte]) 
                         (offset_val computed_size buf_p) * 
                 data_at Tsh enc_key_s (mk_enc_key buf_p buf_size 
                                                   (computed_size + 2)) 
                         app_key_p;
            data_at_ Tsh type_descriptor_s td_p; 
            func_ptr' callback cb_p;
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
            valid_pointer cb_p)).
    - (* if(b) = true *)
      forward.
      entailer!.
      unfold bool_of_int, byte_of_bool, Vubyte;
        destruct Int.eq eqn:S; [apply int_eq_e in S; congruence| reflexivity].
    - (* if(b) = false *)
      forward.
      entailer!.
    - forward.
      deadvars!.
      rewrite <-data_at_tuchar_singleton_array_eq.
      freeze L := (data_at Tsh tint (Vint sptr_val) sptr_p)
                  (data_at_ Tsh enc_rval_s res)
                  (data_at_ Tsh type_descriptor_s td_p)
                  (valid_pointer cb_p).
      forward_call ([(Int.zero_ext 8 
                                   (Int.repr (Byte.unsigned (byte_of_bool 
                                                               (bool_of_int 
                                                                  sptr_val)))))], 
                    v_bool_value, 1, app_key_p, buf_p, 
                    buf_size, computed_size + 2).
      instantiate (1:= [FRZL L; 
                        field_at Tsh (Tstruct _asn_enc_rval_s noattr) 
                                 (DOT _encoded) (Vint (Int.repr 2)) v_erval;
                        field_at Tsh (Tstruct _asn_enc_rval_s noattr) 
                                 (DOT _failed_type) 
                                 (default_val (tptr (Tstruct _asn_TYPE_descriptor_s 
                                                             noattr))) v_erval;
                        field_at Tsh (Tstruct _asn_enc_rval_s noattr) 
                                 (DOT _structure_ptr) (default_val (tptr tvoid)) 
                                 v_erval;
                        if buf_size <? computed_size + 2 
                        then emp
                        else data_at Tsh (tarray tuchar 2) 
                                     (map Vubyte [1%byte; 1%byte]) 
                                     (offset_val computed_size buf_p);
                        func_ptr' callback cb_p]) in (Value of Frame).
      destruct (buf_size <? computed_size + 2) eqn:K; 
        cbn; entailer!.
      admit.
     (* cbn in *.
      replace (computed_size + 3) with (computed_size + 2 + 1) in BsR by lia. *)
      repeat split; try lia; try assumption; admit.
      thaw L.
      forward_if; [congruence|].
      ** (* cb() >= 0 *)
        forward.
        destruct cb_p; intuition.
        rewrite exec_boolean_enc by assumption.
        cbn [Zlength map]; rewrite data_at_tuchar_singleton_array_eq.
        entailer!.
  * (* post if *)
    forward.
    rewrite H; entailer!.
  * (* if(cb) = false *)
    rewrite exec_boolean_enc by assumption.
    repeat forward.
    deadvars!.
    forward_loop (
        PROP ( )
           LOCAL (lvar _bool_value tuchar v_bool_value; 
               lvar _erval (Tstruct _asn_enc_rval_s noattr) v_erval; 
               temp __res res)
        SEP (if buf_size <? computed_size + 2 + 1 
             then data_at Tsh enc_key_s (mk_enc_key buf_p 0 
                                                    (computed_size + 2 + 1)) 
                          app_key_p 
             else data_at Tsh (tarray tuchar 1) 
                          [Vint (Int.zero_ext 8 (Int.repr (Byte.unsigned 
                                                             (byte_of_bool  
                                                                (bool_of_int 
                                                                   sptr_val)))))] 
                          (offset_val (computed_size + 2) buf_p) * 
                  data_at Tsh enc_key_s (mk_enc_key buf_p buf_size 
                                                    (computed_size + 2 + 1)) 
                          app_key_p; 
             match cb_p with 
             | Vint _ => data_at_ Tsh tuchar v_bool_value 
             | _ => data_at Tsh tuchar (Vint (Int.zero_ext 8 (Int.repr 
                                                               (Byte.unsigned 
                                                                  (last 
                                                                     [1%byte; 1%byte; 
                                                                      byte_of_bool 
                                                                        (bool_of_int sptr_val)] 
                                                                     (Byte.repr (-1))))))) 
                           v_bool_value 
             end; data_at_ Tsh type_descriptor_s td_p; 
             func_ptr' callback cb_p; 
             field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _encoded) 
                      (Vint (Int.repr 2 + Int.repr 1)%int) v_erval; 
             field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _failed_type) 
                      (default_val (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) v_erval; 
             field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _structure_ptr) 
                      (default_val (tptr tvoid)) v_erval; 
             if buf_size <? computed_size + 2 
             then emp 
             else data_at Tsh (tarray tuchar 2) (map Vubyte [1%byte; 1%byte]) 
                          (offset_val computed_size buf_p); 
             data_at_ Tsh enc_rval_s res; 
             data_at Tsh tint (Vint sptr_val) sptr_p; 
             valid_pointer cb_p)).
    - entailer!.
    - unfold_data_at_ res; unfold_data_at (data_at _ _ _ res).
      repeat forward.
      rewrite eval_boolean_enc by assumption.
      rewrite exec_boolean_enc by assumption.
      unfold tags_enc_len.
      rewrite Exec.eval_dwt_boolean by assumption.
      unfold_data_at (data_at _ _ _ res); unfold_data_at_ v_erval; 
        unfold_data_at (data_at _ _ _ v_erval).
      cbn.
      destruct cb_p; intuition.
      replace (computed_size + 3) with (computed_size + 2 + 1) by lia.
      entailer!.
Admitted.

End Boolean_der_encode_primitive.
