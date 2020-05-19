Require Import Core.Core Core.StructNormalizer VstLib Callback.Overrun
        Boolean.Exec ErrorWithWriter DWT.Vst.
Require Import VST.floyd.proofauto Psatz.
Require Import Clight.BOOLEAN.
Require Import Core.Notations. 

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
    WITH gv : globals,
         res: val,  sptr_p : val, sptr_val : int, 
         td_p : val, td : TYPE_descriptor,
         tag_mode : Z, tag : Z,
         app_key_p : val,
         (* overrun callback destination buffer *)
         buf_p : val, buf_size : Z, computed_size : Z
    PRE [tptr enc_rval_s, tptr type_descriptor_s, tptr tvoid, tint, 
         tuint, tptr cb_type, tptr tvoid]
      PROP (decoder_type td = BOOLEAN_t;
            isptr buf_p;
            0 <= buf_size <= Int.max_unsigned;
            0 <= computed_size <= Int.max_unsigned;
            0 <= computed_size + 3 <= Int.max_unsigned;
            isptr buf_p) 
      PARAMS (res; td_p; sptr_p; Vint (Int.repr tag_mode);
              Vint (Int.repr tag); (gv cbi); app_key_p)
      GLOBALS (gv)
      SEP (data_at_ Tsh enc_rval_s res;
           data_at_ Tsh type_descriptor_s td_p; 
           data_at Tsh tint (Vint sptr_val) sptr_p;
           data_at Tsh enc_key_s (mk_enc_key buf_p buf_size computed_size) 
                   app_key_p;
           memory_block Tsh buf_size buf_p;
           valid_pointer (gv cbi))
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
      let size := Zlength arr in
      SEP (data_at_ Tsh type_descriptor_s td_p; 
           data_at Tsh tint (Vint sptr_val) sptr_p;
           func_ptr' callback (gv cbi);
           data_at Tsh enc_rval_s res_val res;
           if buf_size <? computed_size + size
           then (data_at Tsh enc_key_s 
                        (mk_enc_key buf_p 0 (computed_size + size)) app_key_p *
                 memory_block Tsh buf_size buf_p)
           else (memory_block Tsh computed_size buf_p *
                 data_at Tsh (tarray tuchar size) (map Vubyte arr) 
                         (offset_val computed_size buf_p) *
                 memory_block Tsh (buf_size - computed_size - size)
                              (offset_val (computed_size + size) buf_p) *
                 data_at Tsh enc_key_s 
                         (mk_enc_key buf_p buf_size (computed_size + size))    
                         app_key_p);
           valid_pointer (gv cbi)).

Definition Gprog := ltac:(with_library prog [der_write_tags_spec; 
                                             callback_overrun_spec; 
                                             bool_der_encode_spec]).

(*
Theorem bool_der_encode : semax_body Vprog Gprog 
                                     (normalize_function f_BOOLEAN_encode_der
                                                         composites)
                                     bool_der_encode_spec.
Proof.
  start_function. 
  rename H into DT; rename H0 into Bf_ptr; 
    rename H1 into Bsm; rename H2 into Bcsm; rename H3 into Bcsm3.
  forward.
  forward_call (gv, td_p, td, 1, tag_mode, 0, tag, app_key_p, buf_p, 
                buf_size, computed_size).
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
             temp _cb (gv cbi); temp _app_key app_key_p)
      SEP (if buf_size <? computed_size + 2 + 1
           then data_at Tsh enc_key_s (mk_enc_key buf_p 0 (computed_size + 2 + 1)) 
                        app_key_p 
           else data_at Tsh (tarray tuchar 1) 
                        (map Vubyte [byte_of_bool (bool_of_int sptr_val)]) 
                        (offset_val (computed_size + 2) buf_p) * 
                data_at Tsh enc_key_s (mk_enc_key buf_p buf_size 
                                                  (computed_size + 2 + 1)) app_key_p; 
           match (gv cbi) with
           | Vint _ => data_at_ Tsh tuchar v_bool_value
           | _ => data_at Tsh tuchar 
                         (Vubyte (byte_of_bool (bool_of_int sptr_val))) 
                         v_bool_value
           end;
           data_at_ Tsh type_descriptor_s td_p; 
           func_ptr' callback (gv cbi); 
           data_at_ Tsh tuchar v_bool_value; 
           field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _encoded) 
                    (Vint (Int.repr 2)) v_erval; 
           field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _failed_type) 
                    (default_val (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) 
                    v_erval; 
           field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _structure_ptr) 
                    (default_val (tptr tvoid)) v_erval; 
           data_at_ Tsh enc_rval_s res; 
           data_at Tsh tint (Vint sptr_val) sptr_p; 
           memory_block Tsh buf_size buf_p;
           valid_pointer (gv cbi))).
  * (* if(cb) = true *)
    forward.
    (* bool_value = *st ? 0xff : 0; /* 0xff mandated by DER */ *)
    forward_if (
        PROP()
        LOCAL(temp _t'2 (Vubyte (byte_of_bool (bool_of_int sptr_val)));
              temp _st sptr_p; 
              lvar _bool_value tuchar v_bool_value; 
              lvar _erval (Tstruct _asn_enc_rval_s noattr) v_erval; 
              temp __res res; temp _cb (gv cbi); 
              temp _app_key app_key_p)
        SEP(if buf_size <? computed_size + 2 
            then data_at Tsh enc_key_s 
                         (mk_enc_key buf_p 0 (computed_size + 2)) 
                         app_key_p 
            else data_at Tsh (tarray tuchar 2) (map Vubyte [1%byte; 1%byte]) 
                         (offset_val computed_size buf_p) * 
                 data_at Tsh enc_key_s 
                         (mk_enc_key buf_p buf_size (computed_size + 2)) 
                         app_key_p; 
            data_at_ Tsh tuchar v_bool_value;
            data_at_ Tsh type_descriptor_s td_p; 
            func_ptr' callback (gv cbi); 
            field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _encoded) 
                     (Vint (Int.repr 2)) v_erval; 
            field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _failed_type) 
                     (default_val (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) 
                     v_erval; 
            field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _structure_ptr) 
                     (default_val (tptr tvoid)) v_erval; 
            data_at_ Tsh enc_rval_s res; 
            data_at Tsh tint (Vint sptr_val) sptr_p; 
            memory_block Tsh buf_size buf_p; 
            valid_pointer (gv cbi))).
    - (* if(b) = true *)
      forward.
      entailer!.
      unfold bool_of_int, byte_of_bool, Vubyte;
        destruct Int.eq eqn:S; [apply int_eq_e in S; congruence| reflexivity].
    - (* if(b) = false *)
      forward.
      entailer!.
    - forward.
      freeze L := (data_at Tsh tint (Vint sptr_val) sptr_p)
                  (data_at_ Tsh enc_rval_s res)
                  (data_at_ Tsh type_descriptor_s td_p)
                  (valid_pointer (gv cbi)).
      rewrite <-data_at_tuchar_singleton_array_eq.
      unfold isptr in H4.
      destruct buf_p; intuition.
      deadvars!.
      forward_call ([(Int.zero_ext 8 
                                   (Int.repr (Byte.unsigned (byte_of_bool 
                                                               (bool_of_int 
                                                                  sptr_val)))))], 
                    v_bool_value, 1, app_key_p, b, i, 
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
                        then data_at Tsh enc_key_s 
                                     (mk_enc_key (Vptr b i) 0 
                                                 (computed_size + 2)) app_key_p 
                        else data_at Tsh (tarray tuchar 2) 
                                     (map Vubyte [1%byte; 1%byte]) 
                                     (offset_val computed_size (Vptr b i)); 
                        func_ptr' callback (gv cbi)]) in (Value of Frame).
      destruct (buf_size <? computed_size + 2) eqn:K;
        cbn; entailer!.
      admit.
      (* cbn in *. *)
      replace (computed_size + 3) with (computed_size + 2 + 1) in * by lia.
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

*)
End Boolean_der_encode.
