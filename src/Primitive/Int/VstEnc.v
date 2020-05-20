Require Import Core.Core Lib.Lib Core.StructNormalizer 
        VstLib Int.Exec Lib.Callback.Dummy Lib.DWT.Vst.
Require Import VST.floyd.proofauto.
Require Import Clight.dummy Clight.INTEGER.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Section Integer_der_encode.

Definition prim_type_s := (Tstruct _ASN__PRIMITIVE_TYPE_s noattr).
Definition mk_prim_type_s (buf_p : val) size := (buf_p, Vint (Int.repr size)).

Definition int_enc_rval td li sptr_p := 
  match evalErrW (int_encoder td li) [] with
  | Some v => mk_enc_rval (encoded v) Vzero
  | None => mk_enc_rval (-1) sptr_p
  end.

Definition int_enc_res td li := 
  match execErrW (int_encoder td li) [] with
  | Some v => v
  | None => []
  end.

Definition int_der_encode_spec : ident * funspec :=
  DECLARE _INTEGER_encode_der
    WITH res_p : val,  
         sptr_p : val, buf_p : val, size : Z, data : list byte,
         td_p : val, td : TYPE_descriptor,
         tag_mode : Z, tag : Z,
         cb_p : val, app_key_p : val
    PRE [tptr enc_rval_s, tptr type_descriptor_s, tptr tvoid, tint, tuint, 
          tptr cb_type, tptr tvoid]
      PROP (decoder_type td = BOOLEAN_t;
            0 < size;
            size = Zlength data;
            (* if sptr_p is null, then encoder will crush *)
            sptr_p <> nullval;
            is_pointer_or_null buf_p)
      PARAMS (res_p; td_p; sptr_p; Vint (Int.repr tag_mode);
              Vint (Int.repr tag); cb_p; app_key_p)
      GLOBALS ()
      SEP (data_at_ Tsh enc_rval_s res_p;
           data_at_ Tsh type_descriptor_s td_p; 
           (* sptr *)
           valid_pointer buf_p;
           if Val.eq buf_p nullval 
           then emp
           else data_at Tsh (tarray tuchar size) (map Vbyte data) buf_p;
           field_at Tsh prim_type_s (DOT _buf) buf_p sptr_p;
           field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p;
           (* Callback *)
           data_at_ Tsh enc_key_s app_key_p;
           valid_pointer cb_p)
    POST [tvoid]
      PROP ()
      LOCAL ()
      SEP (data_at_ Tsh type_descriptor_s td_p;
           (* sptr *)
           valid_pointer buf_p;
           if Val.eq buf_p nullval 
           then emp
           else data_at Tsh (tarray tuchar size) 
                        (map Vbyte (int_enc_res td data)) buf_p;
           data_at Tsh prim_type_s (mk_prim_type_s buf_p size) sptr_p;
           (* Result *)
           data_at Tsh enc_rval_s (int_enc_rval td data sptr_p) res_p;
           (* Callback *)
           valid_pointer cb_p;
           data_at_ Tsh enc_key_s app_key_p;
           func_ptr' dummy_callback_spec cb_p).

Definition Gprog := ltac:(with_library prog [int_der_encode_spec]).

Ltac forward_empty_loop :=
      match goal with
      | [ _ : _ |- semax _ ?Pre (Ssequence (Sloop Sskip Sbreak) _) _ ] =>
          forward_loop Pre break: Pre; try forward ; try entailer! 
      end. 

Theorem int_der_encode : semax_body Vprog Gprog 
                                     (normalize_function f_INTEGER_encode_der
                                                         composites)
                                     int_der_encode_spec.
Proof.
  start_function. 
  rename H into DT; rename H0 into SgtZ; rename H1 into SeqDl.
  replace (Tstruct _asn_enc_rval_s noattr) with enc_rval_s by reflexivity.
  replace (Tstruct _ASN__PRIMITIVE_TYPE_s noattr) with prim_type_s by reflexivity.
  forward.
  forward_empty_loop.
  forward_if (
      PROP ( ) 
      LOCAL (temp _t'2 buf_p; temp _st sptr_p; 
             lvar __res__1 enc_rval_s v__res__1;
             lvar _unconst (Tunion __3988 noattr) v_unconst;
             lvar _effective_integer prim_type_s v_effective_integer;
             lvar _rval (Tstruct _asn_enc_rval_s noattr) v_rval; 
             temp __res res_p; temp _td td_p; 
             temp _sptr sptr_p; temp _tag_mode (Vint (Int.repr tag_mode));
             temp _tag (Vint (Int.repr tag)); 
             temp _cb cb_p; temp _app_key app_key_p)
       SEP ((* Local vars *)
            data_at_ Tsh enc_rval_s v__res__1;
            data_at_ Tsh (Tunion __3988 noattr) v_unconst;
            data_at_ Tsh prim_type_s v_effective_integer;
            data_at_ Tsh (Tstruct _asn_enc_rval_s noattr) v_rval; 
            (* type descriptor *)
            data_at_ Tsh type_descriptor_s td_p; 
            (* sptr *)
            valid_pointer buf_p;
            if Val.eq buf_p nullval
            then emp
            else data_at Tsh (tarray tuchar size) (map Vbyte data) buf_p;
            field_at Tsh prim_type_s (DOT _buf) buf_p sptr_p;
            field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p; 
            (* Result *)
            data_at_ Tsh enc_rval_s res_p;
            (* Callback *)
            data_at_ Tsh enc_key_s app_key_p;
            valid_pointer cb_p)).
  * (* st->buf <> null *)
    destruct buf_p; try contradiction; rewrite if_false by discriminate.
    repeat forward.
    normalize.
    forward_loop (EX z : Z, 
               PROP ()
               LOCAL (temp 
                        _end1 
                        (Vptr b 
                              (Ptrofs.sub 
                                 (Ptrofs.add i 
                                             (Ptrofs.repr 
                                                (Int.unsigned (Int.repr size)))) 
                                 (Ptrofs.repr 1))); 
                      temp _buf (Vptr b (Ptrofs.add i (Ptrofs.repr z))); 
                      temp _t'10 (Vint (Int.repr size));
                      temp _t'2 (Vptr b i); temp _st sptr_p;
                      lvar __res__1 enc_rval_s v__res__1; 
                      lvar _unconst (Tunion __3988 noattr) v_unconst;
                      lvar _effective_integer prim_type_s v_effective_integer; 
                      lvar _rval enc_rval_s v_rval; temp _tag (Vint (Int.repr tag));
                      temp __res res_p; temp _td td_p; temp _sptr sptr_p;
                      temp _tag_mode (Vint (Int.repr tag_mode));
                      temp _cb cb_p; temp _app_key app_key_p)
               SEP (data_at_ Tsh enc_rval_s v__res__1; 
                    data_at_ Tsh (Tunion __3988 noattr) v_unconst;
                    data_at_ Tsh prim_type_s v_effective_integer; 
                    data_at_ Tsh enc_rval_s v_rval;
                    data_at_ Tsh enc_rval_s res_p; data_at_ Tsh type_descriptor_s td_p;
                    data_at_ Tsh enc_key_s app_key_p; valid_pointer (Vptr b i);
                    data_at Tsh (tarray tuchar size) (map Vbyte data) (Vptr b i);
                    field_at Tsh prim_type_s (DOT _buf) (Vptr b i) sptr_p;
                    field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p; 
                    valid_pointer cb_p))%assert
      continue: (EX z : Z, 
               PROP ()
               LOCAL (temp 
                        _end1 
                        (Vptr b 
                              (Ptrofs.sub 
                                 (Ptrofs.add i 
                                             (Ptrofs.repr 
                                                (Int.unsigned (Int.repr size)))) 
                                 (Ptrofs.repr 1))); 
                      temp _t'10 (Vint (Int.repr size));
                      temp _buf (Vptr b (Ptrofs.add i (Ptrofs.repr z))); 
                      temp _t'2 (Vptr b i); temp _st sptr_p;
                      lvar __res__1 enc_rval_s v__res__1; 
                      lvar _unconst (Tunion __3988 noattr) v_unconst;
                      lvar _effective_integer prim_type_s v_effective_integer; 
                      lvar _rval enc_rval_s v_rval; temp _tag (Vint (Int.repr tag));
                      temp __res res_p; temp _td td_p; temp _sptr sptr_p;
                      temp _tag_mode (Vint (Int.repr tag_mode));
                      temp _cb cb_p; temp _app_key app_key_p)
               SEP (data_at_ Tsh enc_rval_s v__res__1; 
                    data_at_ Tsh (Tunion __3988 noattr) v_unconst;
                    data_at_ Tsh prim_type_s v_effective_integer; 
                    data_at_ Tsh enc_rval_s v_rval;
                    data_at_ Tsh enc_rval_s res_p; data_at_ Tsh type_descriptor_s td_p;
                    data_at_ Tsh enc_key_s app_key_p; valid_pointer (Vptr b i);
                    data_at Tsh (tarray tuchar size) (map Vbyte data) (Vptr b i);
                    field_at Tsh prim_type_s (DOT _buf) (Vptr b i) sptr_p;
                    field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p; 
                    valid_pointer cb_p))%assert
      break: (PROP ()
              LOCAL (temp 
                       _end1 
                       (Vptr b 
                             (Ptrofs.sub 
                                (Ptrofs.add i 
                                            (Ptrofs.repr 
                                               (Int.unsigned (Int.repr size)))) 
                                (Ptrofs.repr 1))); 
                     temp _t'10 (Vint (Int.repr size));
                     temp _buf (Vptr b i); temp _t'2 (Vptr b i); temp _st sptr_p;
                     lvar __res__1 enc_rval_s v__res__1; 
                     lvar _unconst (Tunion __3988 noattr) v_unconst;
                     lvar _effective_integer prim_type_s v_effective_integer; 
                     lvar _rval enc_rval_s v_rval; temp _tag (Vint (Int.repr tag));
                     temp __res res_p; temp _td td_p; temp _sptr sptr_p;
                     temp _tag_mode (Vint (Int.repr tag_mode));
                     temp _cb cb_p; temp _app_key app_key_p)
              SEP(data_at_ Tsh enc_rval_s v__res__1; 
                  data_at_ Tsh (Tunion __3988 noattr) v_unconst;
                  data_at_ Tsh prim_type_s v_effective_integer; 
                  data_at_ Tsh enc_rval_s v_rval;
                  data_at_ Tsh enc_rval_s res_p; data_at_ Tsh type_descriptor_s td_p;
                  data_at_ Tsh enc_key_s app_key_p; valid_pointer (Vptr b i);
                  data_at Tsh (tarray tuchar size) (map Vbyte data) (Vptr b i);
                  field_at Tsh prim_type_s (DOT _buf) (Vptr b i) sptr_p;
                  field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p; 
                  valid_pointer cb_p)).
    - (* invariant check *)
      Exists 0.
      entailer!.
    - (* loop *)
      Intros z.
      forward_if.
      admit.
      forward.
Lemma split_array_head_tale : forall {cs : compspecs} size data p t,
          size = Zlength data ->
          data_at Tsh (tarray t size) data p = 
          (data_at Tsh t (match hd_error data with
                          | Some v => v
                          | None => Vundef
                          end) p) * 
          (data_at Tsh (tarray t (size - 1)) (tl data) p)
      rewrite split2_data_at_Tarray_app.
      rewrite data_at_tuchar_singleton_array_eq.
    - (* break postcondition check *)
    
  * (* postcondition check *)
    forward.
    entailer!.
  * (* st->buf = null *)
  
Admitted.

End Integer_der_encode.
