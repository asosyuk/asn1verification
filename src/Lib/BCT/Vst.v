Require Import Core.Core Core.Tactics Core.VstTactics Core.StructNormalizer
        (* Core.SepLemmas *)
        VstLib ErrorWithWriter BCT.Exec.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_decoder.
Require Import VST.ASN__STACK_OVERFLOW_CHECK
    BFT.Vst BFL.Vst   
 (* ber_fetch_tag ber_fetch_length *) Lib.Forward. 
Require Import Core.VstTactics Core.Notations.
Require Import  Clight.ber_decoder.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section Ber_check_tags.

Instance Change1 : change_composite_env CompSpecs BFT.Vst.CompSpecs.
Proof. make_cs_preserve CompSpecs BFT.Vst.CompSpecs. Defined.

Instance Change2 : change_composite_env  BFT.Vst.CompSpecs CompSpecs.
Proof. make_cs_preserve  BFT.Vst.CompSpecs CompSpecs. Defined.

Instance Change3 : change_composite_env CompSpecs BFL.Vst.CompSpecs.
Proof. make_cs_preserve CompSpecs BFL.Vst.CompSpecs. Defined.

Instance Change4 : change_composite_env BFL.Vst.CompSpecs CompSpecs.
Proof. make_cs_preserve BFL.Vst.CompSpecs CompSpecs. Defined.

Definition ber_check_tags_spec : ident * funspec :=
  DECLARE _ber_check_tags
    WITH opt_codec_ctx_p : val, 
         td_p : val, td : TYPE_descriptor, 
         tags_p : val,
         opt_ctx_p : val,
         b : block, i : ptrofs, ptr : list int,
         res_p : val,
         size : Z, tag_mode : Z, last_tag_form : Z,
         last_length_p : val,
         opt_tlv_form_p : val,
         max_stack_size : Z
    PRE [tptr asn_dec_rval_s, tptr (Tstruct _asn_codec_ctx_s noattr),
         tptr (Tstruct _asn_TYPE_descriptor_s noattr),
         tptr (Tstruct _asn_struct_ctx_s noattr), 
         tptr tvoid, tuint, tint, tint, tptr tint, tptr tint]
      PROP (tag_mode = 0;
            last_tag_form = 0;
            0 < len ptr <= Ptrofs.max_unsigned;
            (Znth 0 ptr & Int.repr 32 = 0)%int;
            nullval = opt_ctx_p;
            nullval = opt_tlv_form_p;
            1 = len (tags td);
            0 <= Ptrofs.unsigned i + len ptr <= Ptrofs.max_unsigned;
            Forall (fun x => 0 <= Int.unsigned x <= Byte.max_unsigned) ptr;
            0 <= size <= Int.max_unsigned)
      PARAMS (res_p; opt_codec_ctx_p; td_p; opt_ctx_p; (Vptr b i); 
                Vint (Int.repr size);
                Vint (Int.repr tag_mode); Vint (Int.repr last_tag_form);
                  last_length_p; opt_tlv_form_p)
      GLOBALS ((* (fun _ : ident => Vint 0%int) *))
      SEP (data_at Tsh (tarray tuchar (len ptr)) 
                   (map Vint ptr) (Vptr b i);
           field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) 
                         [StructField _tags] 
                         tags_p td_p;
           field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) 
                         [StructField _tags_count] 
                         (Vint (Int.repr (Zlength (tags td)))) td_p;
           data_at Tsh (tarray tuint (Zlength (tags td))) 
                   (map Vint (map Int.repr (tags td))) tags_p;
           data_at_ Tsh asn_dec_rval_s res_p;
           data_at_ Tsh tint last_length_p;
           data_at Tsh (Tstruct _asn_codec_ctx_s noattr) 
                   (Vint (Int.repr (max_stack_size))) opt_codec_ctx_p)
    POST [tvoid]
      PROP ()
      LOCAL ()
      SEP (data_at Tsh (tarray tuchar (len ptr)) 
                   (map Vint ptr) (Vptr b i);
           field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) 
                         [StructField _tags] 
                         tags_p td_p;
           field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) 
                         [StructField _tags_count] 
                         (Vint (Int.repr (Zlength (tags td)))) td_p;
           data_at Tsh (tarray tuint (Zlength (tags td))) 
                   (map Vint (map Int.repr (tags td))) tags_p;
           data_at Tsh (Tstruct _asn_codec_ctx_s noattr) 
                  (Vint (Int.repr (max_stack_size))) opt_codec_ctx_p;
           match ber_check_tags_primitive ptr
                                       td max_stack_size
                                       size (sizeof tuint) Int.max_signed with
           | Some v => 
             data_at Tsh asn_dec_rval_s 
                     (mk_dec_rval 0 (snd v)) res_p *
             data_at Tsh tint (Vint (Int.repr (fst v))) last_length_p
           | None => 
             data_at Tsh asn_dec_rval_s (mk_dec_rval 2 0) res_p *
             data_at_ Tsh tint last_length_p
        end).

Definition assert_spec {cs : compspecs} :=
   WITH e : bool(* , str2 : val, str3 : val, func : val *)
   PRE [ (tptr tschar), (tptr tschar), tuint, (tptr tschar)]
       PROP ()
       PARAMS (nullval; nullval; Vint (Int.repr 137); nullval) 
       GLOBALS()
       SEP ()
    POST [ tvoid ] 
       PROP (e = true)
       LOCAL ()
       SEP ().

Definition Gprog := ltac:(with_library prog 
                                       [(___assert_fail, assert_spec);
                                        ber_check_tags_spec;
                                        ber_fetch_tag_spec;
                                        ber_fetch_len_spec;
                                        ASN__STACK_OVERFLOW_CHECK_spec]).

Theorem ber_check_tags_correctness : 
  semax_body Vprog Gprog
             (normalize_function f_ber_check_tags composites) 
             ber_check_tags_spec.
(* Proof.
  start_function.
  subst.
  repeat forward.
  forward_if (temp _t'1 Vzero).
  contradiction.
  - forward.
    entailer!.
  - forward.
    Time forward_call (opt_codec_ctx_p, max_stack_size).
      assert (-1 <= ASN__STACK_OVERFLOW_CHECK 0 max_stack_size <= 0) as A.
    { unfold ASN__STACK_OVERFLOW_CHECK.
      repeat break_if; lia. }
    forward_if [opt_codec_ctx_p <> nullval;
                (if eq_dec opt_codec_ctx_p nullval
                 then 0
                 else ASN__STACK_OVERFLOW_CHECK 0 max_stack_size) = 0].
  +  forward_empty_while.
  assert (opt_codec_ctx_p <> nullval) as ON.
  { break_if; try nia.
    eassumption. }
  rewrite_if_b. 
  forward_if True; try contradiction.
  * forward.
    entailer!. 
  * forward_if (temp _t'2 Vzero);
      try forward; try entailer!.
    forward_if_add_sep (data_at Tsh (Tstruct _asn_dec_rval_s noattr)
       (Vint (Int.repr 2), Vint (Int.repr 0)) v_rval) v_rval; 
      try forward; try entailer!.
    repeat forward. 
    assert (ber_check_tags_primitive ptr td max_stack_size
                            size (sizeof tuint) Int.modulus = None) as N.
       { unfold ber_check_tags_primitive.
         assert (ASN__STACK_OVERFLOW_CHECK 0 max_stack_size =? 0 = false) 
           as AS by (Zbool_to_Prop;
                    eassumption).
         erewrite AS.
         auto. }
    erewrite N.
    entailer!. 
  + forward.    
    entailer!.
    apply repr_inj_signed.
    repeat break_if; try rep_lia.
    rep_lia.
    eassumption. 
  + forward_if
      (temp _t'4 Vzero); try congruence.
  -- forward.
     entailer!.
  -- forward.
     forward_if (temp _t'10 
                  ((force_val
                  (sem_cast tint tbool
                  (eval_binop Oeq tint tint
                    (Vint
                       (Int.repr 0))
                    (eval_cast tuint tint (Vint (Int.repr (len (tags td))))))))
                   )); try discriminate.
     --- forward.
         forward.
         entailer!. 
     ---
       Arguments eq_dec : simpl never.
       forward_if True.
       cbn in H3.
       unfold sem_cast_i2bool in H3.
       unfold Val.of_bool in H3.
       destruct (Int.repr 0 == Int.repr (len (tags td)))%int eqn : S.
       cbn in H3.
       eapply int_eq_e in S.
       erewrite <- H5 in *.
       discriminate.
       cbn in H3.
       setoid_rewrite if_true in H3.
       discriminate.
       auto.
       forward.
       forward_if True.
       forward.
       entailer!.
       forward_call (false).
       entailer!.
       entailer!.
     (* MAIN LOOP *)       
     (* match goal with
       | [ _ : _ |-  semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) ?C ?Post ] =>
         let Q' := remove_LOCAL _tagno Q in
         replace Q with Q'
        end. *)
       rewrite H0.
       match goal with
       | [ _ : _ |-  semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) ?C ?Post ] =>
       (*  let Q' := remove_LOCAL _tagno Q in
         let Q'' := remove_LOCAL _step Q' in *)
         forward_loop (
     EX z : Z,
     let (tag_len, tlv_tag) := Exec.ber_fetch_tags ptr
                                                   size  in
     let (len_len, tlv_len) := Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 
                                                  (size - tag_len) (sizeof tuint) Int.modulus in
     let ll := if z =? 0 then -1 else (tlv_len)%Z in (* + tag_len + len_len *)
     let cm := if z =? 0 then 0 else (tag_len + len_len)%Z in 
     PROP ( 0 <= z <= 1;
            if z =? 0 then
              True else
           0 < tag_len /\
           0 < len_len /\
           0 < tlv_len /\
           tag_len <> 0 /\
           len_len <> -1 /\
           len_len <> 0 /\ 
           tlv_tag = (Int.repr (nth O (tags td) 0)))
     LOCAL (temp _t'10
              (force_val
                 (sem_cast tint tbool
                    (eval_binop Oeq tint tint (Vint (Int.repr 0))
                       (eval_cast tuint tint (Vint (Int.repr (len (tags td))))))));
     temp _tagno (Vint (Int.repr z));
     temp _t'4 Vzero;
     temp _t'3 (Vint (Int.repr 0));
     temp _step (Vint (Int.repr z)); 
     temp _t'1 Vzero; 
     temp _tlv_constr (Vint (Int.repr (if z =? 0 then -1 else 0)));
     temp _expect_00_terminators (Vint (Int.repr 0));
     temp _limit_len (Vint (Int.repr ll)); 
     temp _consumed_myself (Vint (Int.repr cm));
     lvar _rval__12 (Tstruct _asn_dec_rval_s noattr) v_rval__12;
     lvar _rval__11 (Tstruct _asn_dec_rval_s noattr) v_rval__11;
     lvar _rval__10 (Tstruct _asn_dec_rval_s noattr) v_rval__10;
     lvar _rval__9 (Tstruct _asn_dec_rval_s noattr) v_rval__9;
     lvar _rval__8 (Tstruct _asn_dec_rval_s noattr) v_rval__8;
     lvar _rval__7 (Tstruct _asn_dec_rval_s noattr) v_rval__7;
     lvar _rval__6 (Tstruct _asn_dec_rval_s noattr) v_rval__6;
     lvar _rval__5 (Tstruct _asn_dec_rval_s noattr) v_rval__5;
     lvar _rval__4 (Tstruct _asn_dec_rval_s noattr) v_rval__4;
     lvar _rval__3 (Tstruct _asn_dec_rval_s noattr) v_rval__3;
     lvar _rval__2 (Tstruct _asn_dec_rval_s noattr) v_rval__2;
     lvar _rval__1 (Tstruct _asn_dec_rval_s noattr) v_rval__1;
     lvar _rval (Tstruct _asn_dec_rval_s noattr) v_rval; 
     lvar _tlv_len tint v_tlv_len;
     lvar _tlv_tag tuint v_tlv_tag; 
     temp __res res_p; temp _opt_codec_ctx opt_codec_ctx_p;
     temp _td td_p; temp _opt_ctx nullval;
     temp _ptr (offset_val cm  (Vptr b i));
     temp _size (Vint (Int.repr (if z =? 0 
                                 then size - cm
                                 else if size - tag_len - len_len >? tlv_len
                                   then tlv_len
                                   else size - ((tag_len + len_len)%Z))));
     temp _tag_mode (Vint (Int.repr 0));
     temp _last_tag_form (Vint (Int.repr 0));
     temp _last_length last_length_p;
     temp _opt_tlv_form nullval)
     SEP (data_at Tsh (Tstruct _asn_codec_ctx_s noattr)
                  (Vint (Int.repr max_stack_size))
            opt_codec_ctx_p;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__12;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__11;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__10;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__9;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__8;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__7;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__6;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__5;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__4;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__3;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__2;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__1;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval;
     if z =? 0 then (data_at_ Tsh tint v_tlv_len *
                     data_at_ Tsh tuint v_tlv_tag)
     else (data_at Tsh tint (Vint (Int.repr tlv_len)) v_tlv_len *
                     data_at Tsh tuint (Vint (tlv_tag)) v_tlv_tag);
     data_at Tsh (tarray tuchar (len ptr)) 
             (map Vint ptr) (Vptr b i);
     field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p;
     field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
       (Vint (Int.repr (len (tags td)))) td_p;
     data_at Tsh (tarray tuint (len (tags td))) 
             (map Vint (map Int.repr (tags td))) tags_p;
     data_at_ Tsh asn_dec_rval_s res_p; 
     data_at_ Tsh tint last_length_p))%assert
                      (* CONTINUE *)
                      continue:
           (let (tag_len, tlv_tag) := 
                Exec.ber_fetch_tags ptr
                                    size  in
       let (len_len, tlv_len) :=
         Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 (size - tag_len) 
           (sizeof tuint) Int.modulus in
       PROP (0 < tag_len;
           0 < len_len;
           0 < tlv_len;
           tag_len <> 0;
           len_len <> -1;
           len_len <> 0;
           tlv_tag = Int.repr (nth O (tags td) 0))
       LOCAL (temp _t'10
                (force_val
                   (sem_cast tint tbool
                      (eval_binop Oeq tint tint (Vint (Int.repr 0))
                         (eval_cast tuint tint (Vint (Int.repr (len (tags td))))))));
       temp _tagno (Vint (Int.repr 0)); temp _t'4 Vzero; temp _t'3 (Vint (Int.repr 0));
       temp _step (Vint (Int.repr 0)); temp _t'1 Vzero;
       temp _tlv_constr (Vint (Int.repr (0)));
       temp _expect_00_terminators (Vint (Int.repr 0));
       temp _limit_len (Vint (Int.repr ((tlv_len)%Z)));
       temp _consumed_myself (Vint (Int.repr ((tag_len + len_len)%Z)));
       lvar _rval__12 (Tstruct _asn_dec_rval_s noattr) v_rval__12;
       lvar _rval__11 (Tstruct _asn_dec_rval_s noattr) v_rval__11;
       lvar _rval__10 (Tstruct _asn_dec_rval_s noattr) v_rval__10;
       lvar _rval__9 (Tstruct _asn_dec_rval_s noattr) v_rval__9;
       lvar _rval__8 (Tstruct _asn_dec_rval_s noattr) v_rval__8;
       lvar _rval__7 (Tstruct _asn_dec_rval_s noattr) v_rval__7;
       lvar _rval__6 (Tstruct _asn_dec_rval_s noattr) v_rval__6;
       lvar _rval__5 (Tstruct _asn_dec_rval_s noattr) v_rval__5;
       lvar _rval__4 (Tstruct _asn_dec_rval_s noattr) v_rval__4;
       lvar _rval__3 (Tstruct _asn_dec_rval_s noattr) v_rval__3;
       lvar _rval__2 (Tstruct _asn_dec_rval_s noattr) v_rval__2;
       lvar _rval__1 (Tstruct _asn_dec_rval_s noattr) v_rval__1;
       lvar _rval (Tstruct _asn_dec_rval_s noattr) v_rval; lvar _tlv_len tint v_tlv_len;
       lvar _tlv_tag tuint v_tlv_tag; temp __res res_p; temp _opt_codec_ctx opt_codec_ctx_p;
       temp _td td_p; temp _opt_ctx nullval;
       temp _ptr (offset_val ((tag_len + len_len)%Z) (Vptr b i));
       temp _size (Vint (Int.repr (if size - tag_len - len_len >? tlv_len
                                   then tlv_len
                                   else size - ((tag_len + len_len)%Z))));
       temp _tag_mode (Vint (Int.repr 0)); temp _last_tag_form (Vint (Int.repr 0));
       temp _last_length last_length_p; temp _opt_tlv_form nullval)
       SEP (data_at Tsh (Tstruct _asn_codec_ctx_s noattr) (Vint (Int.repr max_stack_size))
              opt_codec_ctx_p; data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__12;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__11;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__10;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__9;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__8;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__7;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__6;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__5;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__4;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__3;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__2;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__1;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval;
        data_at Tsh tint (Vint (Int.repr tlv_len)) v_tlv_len ;
        data_at Tsh tuint (Vint (tlv_tag)) v_tlv_tag;
       data_at Tsh (tarray tuchar (len ptr)) (map Vint ptr) (Vptr b i);
       field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p;
       field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
         (Vint (Int.repr (len (tags td)))) td_p;
       data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
       data_at_ Tsh asn_dec_rval_s res_p; data_at_ Tsh tint last_length_p))
                             break: (
     let (tag_len, tlv_tag) := Exec.ber_fetch_tags ptr
                                                   size in
     let (len_len, tlv_len) := Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 
                                                  (size - tag_len) (sizeof tuint) Int.modulus in
     PROP (0 < tag_len;
           0 < len_len;
           0 < tlv_len;
           tag_len <> 0;
           len_len <> -1;
           len_len <> 0;
           tlv_tag = Int.repr (nth O (tags td) 0))
     LOCAL (temp _t'10
              (force_val
                 (sem_cast tint tbool
                    (eval_binop Oeq tint tint (Vint (Int.repr 0))
                       (eval_cast tuint tint (Vint (Int.repr (len (tags td))))))));
     temp _tagno (Vint (Int.repr 1));
     temp _t'4 Vzero;
     temp _t'3 (Vint (Int.repr 0));
     temp _step (Vint (Int.repr 1)); 
     temp _t'1 Vzero; 
     temp _tlv_constr (Vint (Int.repr 0));
     temp _expect_00_terminators (Vint (Int.repr 0));
     temp _limit_len (Vint ((Int.repr (tlv_len (* + tag_len + len_len *))))); 
     temp _consumed_myself (Vint (Int.repr (tag_len + len_len)));
     lvar _rval__12 (Tstruct _asn_dec_rval_s noattr) v_rval__12;
     lvar _rval__11 (Tstruct _asn_dec_rval_s noattr) v_rval__11;
     lvar _rval__10 (Tstruct _asn_dec_rval_s noattr) v_rval__10;
     lvar _rval__9 (Tstruct _asn_dec_rval_s noattr) v_rval__9;
     lvar _rval__8 (Tstruct _asn_dec_rval_s noattr) v_rval__8;
     lvar _rval__7 (Tstruct _asn_dec_rval_s noattr) v_rval__7;
     lvar _rval__6 (Tstruct _asn_dec_rval_s noattr) v_rval__6;
     lvar _rval__5 (Tstruct _asn_dec_rval_s noattr) v_rval__5;
     lvar _rval__4 (Tstruct _asn_dec_rval_s noattr) v_rval__4;
     lvar _rval__3 (Tstruct _asn_dec_rval_s noattr) v_rval__3;
     lvar _rval__2 (Tstruct _asn_dec_rval_s noattr) v_rval__2;
     lvar _rval__1 (Tstruct _asn_dec_rval_s noattr) v_rval__1;
     lvar _rval (Tstruct _asn_dec_rval_s noattr) v_rval; 
     lvar _tlv_len tint v_tlv_len;
     lvar _tlv_tag tuint v_tlv_tag; 
     temp __res res_p; temp _opt_codec_ctx opt_codec_ctx_p;
     temp _td td_p; temp _opt_ctx nullval;
     temp _ptr (offset_val (tag_len + len_len) (Vptr b i));
     temp _size (Vint (Int.repr ((if size - tag_len - len_len >? tlv_len
                                  then tlv_len
                                  else size - ((tag_len + len_len)%Z)))));
     temp _tag_mode (Vint (Int.repr 0));
     temp _last_tag_form (Vint (Int.repr 0));
     temp _last_length last_length_p;
     temp _opt_tlv_form nullval)
     SEP (data_at Tsh (Tstruct _asn_codec_ctx_s noattr)
                  (Vint (Int.repr max_stack_size))
            opt_codec_ctx_p;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__12;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__11;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__10;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__9;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__8;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__7;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__6;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__5;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__4;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__3;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__2;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__1;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval;
     data_at Tsh tint (Vint (Int.repr tlv_len)) v_tlv_len;
     data_at Tsh tuint (Vint (tlv_tag)) v_tlv_tag;
     data_at Tsh (tarray tuchar (len ptr)) 
             (map Vint ptr) (Vptr b i);
     field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p;
     field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
       (Vint (Int.repr (len (tags td)))) td_p;
     data_at Tsh (tarray tuint (len (tags td))) 
             (map Vint (map Int.repr (tags td))) tags_p;
     data_at_ Tsh asn_dec_rval_s res_p; 
     data_at_ Tsh tint last_length_p))
       end.
       +++ (* Pre -> LI *)
         Exists 0.
         repeat rewrite_if_b.
         repeat break_let.
         entailer!.
         apply derives_refl. 
       +++ Intros z.
           repeat break_let.
           break_if.
           * simpl.
             Intros.
             Zbool_to_Prop.
             forward.
           forward_if.
           2: (* LI -> break *) lia.
           deadvars.
           Time forward_call (b, i, ptr, size, v_tlv_tag). 
           unfold Frame.
            instantiate (1 := [emp]).
            simpl.
            admit.
           { repeat split; try rep_lia.
             all: admit. }
           
          




               Require Import VST.floyd.proofauto.
                Set Ltac Backtrace.
                Ltac process_cases sign ::= 
match goal with
| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N (LScons (Some ?X) ?C ?SL)
      with Some _ => _ | None => _ end) _ =>
       let y := constr:(adjust_for_sign sign X) in let y := eval compute in y in 
      rewrite (select_switch_case_signed y); 
           [ | reflexivity | clear; compute; split; congruence];
     let E := fresh "E" in let NE := fresh "NE" in 
     destruct (zeq N (Int.unsigned (Int.repr y))) as [E|NE];
      [ try ( rewrite if_true; [  | symmetry; apply E]);
        unfold seq_of_labeled_statement at 1;
        apply unsigned_eq_eq in E;
        match sign with
        | Signed => apply repr_inj_signed in E; try rep_lia
        | Unsigned => apply repr_inj_unsigned in E;  try rep_lia
        end;
        try match type of E with ?a = _ => is_var a; subst a end;
        repeat apply -> semax_skip_seq
     | try (rewrite if_false by (contradict NE; symmetry; apply NE));
        process_cases sign
    ]
| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N (LScons None ?C ?SL)
      with Some _ => _ | None => _ end) _ =>
      change (select_switch_case N (LScons None C SL))
       with (select_switch_case N SL);
        process_cases sign
| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N LSnil
      with Some _ => _ | None => _ end) _ =>
      change (select_switch_case N LSnil)
           with (@None labeled_statements);
      cbv iota;
      unfold seq_of_labeled_statement at 1;
      repeat apply -> semax_skip_seq
end.
                Time match goal with
                  | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
               forward_if Pre                              
             end.
Ltac process_cases sign ::= 
match goal with
| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N (LScons (Some ?X) ?C ?SL)
      with Some _ => _ | None => _ end) _ =>
      let y := constr:(adjust_for_sign sign X) in 
      let y := eval compute in y in 
      rewrite (select_switch_case_signed y); 
           [ | reflexivity | clear; compute; split; congruence];
     let E := fresh "E" in let NE := fresh "NE" in 
     destruct (zeq N (Int.unsigned (Int.repr y))) as [E|NE];
      [ try ( rewrite if_true; [  | symmetry; apply E]);
        unfold seq_of_labeled_statement at 1;
        apply unsigned_eq_eq in E;
         match sign with
        | Signed =>  (apply repr_inj_signed in E; [ | rep_lia | rep_lia])
        | Unsigned =>  (apply repr_inj_unsigned in E; [ | rep_lia | rep_lia])
        end;
        try match type of E with ?a = _ => is_var a; subst a end;
        repeat apply -> semax_skip_seq 
        | 
        try (rewrite if_false by (contradict NE; symmetry; apply NE));
        process_cases sign  
    ] 

| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N (LScons None ?C ?SL)
      with Some _ => _ | None => _ end) _ =>
      change (select_switch_case N (LScons None C SL))
       with (select_switch_case N SL);
      process_cases sign

| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N LSnil
      with Some _ => _ | None => _ end) _ =>
      change (select_switch_case N LSnil)
           with (@None labeled_statements);
      cbv iota;
      unfold seq_of_labeled_statement at 1;
      repeat apply -> semax_skip_seq

end. 


             Time match goal with
                  | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
               forward_if Pre                              
             end.
             congruence.
             process_cases Signed.
             congruence.
             process_cases Signed.
             process_cases Signed.
             change (select_switch_case (Int.unsigned (Int.repr 0))
                                        (LScons None Sbreak LSnil))
               with (select_switch_case (Int.unsigned (Int.repr 0)) LSnil).

             change (select_switch_case (Int.unsigned (Int.repr 0)) LSnil)
               with (@None labeled_statements);
               cbv iota;
               unfold seq_of_labeled_statement at 1;
               repeat apply -> semax_skip_seq.
             forward.
               process_cases Signed.
             
apply repr_inj_signed in E; [ | try rep_lia | try rep_lia].
           
                     
             Set Ltac Backtrace.
             unfold MORE_COMMANDS.
             unfold abbreviate.
             
             match goal with
             | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
               forward_switch Pre 
                              
             end.

          (* FIXME : forward switch doesn't work with complex terms *)
           (* in VST 2.6 forward_switch needs change and can fail here *)
           Require Import Forward.
           Set Ltac Backtrace.

           
          
           Ltac process_cases sign := 
match goal with
| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N (LScons (Some ?X) ?C ?SL)
      with Some _ => _ | None => _ end) _ =>
       let y := constr:(adjust_for_sign sign X) in let y := eval compute in y in 
      rewrite (select_switch_case_signed y); 
           [ | reflexivity | clear; compute; split; congruence];
     let E := fresh "E" in let NE := fresh "NE" in 
     destruct (zeq (Int.unsigned (Int.repr y)) N) as [E|NE];
      [ unfold seq_of_labeled_statement at 1 ;
        apply unsigned_eq_eq in E;
        match sign with
        | Signed => apply repr_inj_signed in E; [ | rep_omega | rep_omega]
        | Unsigned => apply repr_inj_unsigned in E; [ | rep_omega | rep_omega]
        end;
        try match type of E with ?a = _ => is_var a; subst a end;
        repeat apply -> semax_skip_seq
     | process_cases sign
    ]
| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N (LScons None ?C ?SL)
      with Some _ => _ | None => _ end) _ =>
      change (select_switch_case N (LScons None C SL))
       with (select_switch_case N SL);
      process_cases sign
| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N LSnil
      with Some _ => _ | None => _ end) _ =>
      change (select_switch_case N LSnil)
           with (@None labeled_statements);
      cbv iota;
      unfold seq_of_labeled_statement at 1;
      repeat apply -> semax_skip_seq
end.


 Ltac do_compute_expr1 Delta Pre e :=
 match Pre with
 | @exp _ _ ?A ?Pre1 => fail "BLA1"
  (* let P := fresh "P" in let Q := fresh "Q" in let R := fresh "R" in
  let H8 := fresh "DCE" in let H9 := fresh "DCE" in
  evar (P: A -> list Prop);
  evar (Q: A -> list localdef);
  evar (R: A -> list mpred);
  assert (H8: Pre1 =  (fun a => PROPx (P a) (LOCALx (Q a) (SEPx (R a)))))
    by (extensionality; unfold P,Q,R; reflexivity);
  let v := fresh "v" in evar (v: A -> val);
  assert (H9: forall a, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a))) |--
                       local ((eq (v a)) (eval_expr e)))
     by (let a := fresh "a" in intro a; do_compute_expr_helper Delta (Q a) v) *)

 | PROPx ?P (LOCALx ?Q (SEPx ?R)) => fail "BLA2"

 (* let H9 := fresh "H" in
  let v := fresh "v" in (evar (v: val);
  assert (H9:  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))|--
                     local ((eq v) (eval_expr e)))
   by (do_compute_expr_helper Delta Q v))  *)
| _ => fail "YES"
 end. 

Ltac forward_switch' := 
 match goal with
| |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Sswitch ?e _) _ => 
  let sign := constr:(signof e) in let sign := eval hnf in sign in
   let HRE := fresh "H" in let v := fresh "v" in
    evar (v: val);
    do_compute_expr1 Delta P Q R e v HRE;
    simpl in v;
    let n := fresh "n" in evar (n: int); 
    let H := fresh in assert (H: v=Vint n) by (unfold v,n; reflexivity);
    let A := fresh in 
    match goal with |- ?AA => set (A:=AA) end;
    revert n H; normalize; intros n H; subst A;
    let n' := fresh "n" in pose (n' := Int.unsigned n); 
    let H' := fresh in assert (H': n = Int.repr n');
    [try (symmetry; apply Int.repr_unsigned) 
       | rewrite H,H' in HRE; clear H H';
         subst n' n v; 
         rewrite (Int.repr_unsigned (Int.repr _)) in HRE;
          eapply semax_switch_PQR ; 
           [reflexivity | check_typecheck | exact HRE 
           | clear HRE; unfold select_switch at 1; unfold select_switch_default at 1;
             try match goal with H := @abbreviate statement _ |- _ => clear H end;
             process_cases sign ] 
]

end.

Ltac forward_switch_seq post :=
  check_Delta; check_POSTCONDITION;
  repeat (apply -> seq_assoc; abbreviate_semax);
  repeat apply -> semax_seq_skip;
first [ignore (post: environ->mpred)
      | fail 1 "Invariant (first argument to forward_if) must have type (environ->mpred)"];
     match goal with
     | _ : _ |- semax _ _ (Ssequence (Sswitch _ _) _) _ => 
       apply semax_seq with post;
       [forward_switch' 
      | abbreviate_semax; 
        simpl_ret_assert (*autorewrite with ret_assert*)]
end.    

           match goal with
           | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                forward_switch_seq Pre 
            
           end.

 clear Z0. 
           admit.
           *** (* RC_FAIL  *)             
              match goal with
                 | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                   forward_empty_while_break Pre
              end.
              assert (opt_codec_ctx_p <> nullval) as ON.
              { break_if; try nia;
                eassumption. }
              rewrite_if_b. 
              forward_if True; try contradiction.
              forward.
              admit. (* entailer!. *) 
              forward_if (temp _t'12 Vzero);
               try forward; try entailer!.
             forward_if_add_sep (data_at Tsh 
                                         (Tstruct _asn_dec_rval_s noattr)
                                         (Vint (Int.repr 2), Vint (Int.repr 0))
                                         v_rval__3) v_rval__3; 
               try forward; try entailer!.
             repeat forward. 
             assert (ber_check_tags_primitive ptr td max_stack_size
                                              size (sizeof tuint) Int.modulus = None) as N.
             { unfold ber_check_tags_primitive.
               erewrite H0.
               erewrite Heqp.
               simpl.
               auto. }
             erewrite N.
             (* entailer!. *)
             admit. *)
       (*    *** admit. (* (* RC_FAIL: same *)
              match goal with
                 | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                   forward_empty_while_break Pre
              end.
              assert (opt_codec_ctx_p <> nullval) as ON.
              { break_if; try nia;
                eassumption. }
              rewrite_if_b. 
              forward_if True; try contradiction.
              forward.
              admit. (* entailer!. *) 
              forward_if (temp _t'12 Vzero);
               try forward; try entailer!.
             forward_if_add_sep (data_at Tsh 
                                         (Tstruct _asn_dec_rval_s noattr)
                                         (Vint (Int.repr 2), Vint (Int.repr 0))
                                         v_rval__3) v_rval__3; 
               try forward; try entailer!.
             repeat forward. 
             assert (ber_check_tags_primitive ptr td max_stack_size
                                              size (sizeof tuint) Int.modulus = None) as N.
             { unfold ber_check_tags_primitive.
               erewrite H0.
               erewrite Heqp.
               simpl.
               auto. }
             erewrite N.
             (* entailer!. *)
             admit. *)
           *** admit. (* forward.
               entailer!. *) 
           *** remember (map Vint ptr) as ptr'.
               normalize.
               Intros. 
               assert_PROP ((Vptr b i) = 
                            field_address 
                              (tarray tuchar (len ptr)) [ArraySubsc 0] (Vptr b i)).
               { entailer!.
                 rewrite field_address_offset; cbn.
                 normalize.
                 econstructor;
                 auto.
                 repeat split; auto; 
                   autorewrite with norm;  try rep_lia.
                 cbn.
                 autorewrite with norm.
                 rep_lia.
                 constructor.
                 intros.
                 econstructor; auto; cbn.
                 auto.
                 eapply Z.divide_1_l. }
               forward.
               entailer!.
               unfold is_int.
               assert (0 <= Znth 0 ptr <= Byte.max_unsigned) as B.
               { eapply Forall_Znth.
                 lia.
                 eassumption. }
               repeat erewrite Znth_map; auto; try nia.
               strip_repr.
               forward_if (temp _t'13 Vzero).
             ** admit. 
                (* assert ((Znth 0 ptr & 32) <> 0) as Z.
                { generalize H10.
                  subst.
                  repeat erewrite Znth_map.
                  simpl.
                  autorewrite with norm.
                  intro V.
                  eapply typed_true_tint_Vint in V.
                  eapply repr_neq_e in V.
                  auto.
                  lia.
                  erewrite Zlength_map.
                  lia. }
                lia. *)
             ** admit. (* forward.  entailer!. *)
             ** forward.
                forward_if
                  (temp _t'15 Vzero); try contradiction;
                  try forward; try entailer!; rewrite_if_b; try entailer!.
                forward_if True; try nia.
                forward_if True.
                forward.
                admit. (* entailer! *)
                lia.
                forward.
                forward. 
                normalize.
                forward.
                forward_if. 
             ++ admit. 
                (* (* RC_FAIL case *) 
               forward_empty_while.
              rewrite_if_b. 
              forward_if True; try contradiction.
              forward.
              admit. (* entailer!. *) 
              forward_if (temp _t'14 Vzero);
               try forward; try entailer!.
             forward_if_add_sep (data_at Tsh 
                                         (Tstruct _asn_dec_rval_s noattr)
                                         (Vint (Int.repr 2), Vint (Int.repr 0))
                                         v_rval__4) v_rval__4; 
               try forward; try entailer!.
             repeat forward. 
             assert (ber_check_tags_primitive ptr td max_stack_size
                                              size (sizeof tuint) Int.modulus = None) as N.
             { unfold ber_check_tags_primitive.
               erewrite H0.
               erewrite Heqp.
               simpl.
               assert (z1 <>
                       (nth 0 (tags td) 0)) as O.
               { replace z1 with (snd (Exec.ber_fetch_tags ptr size 0 4)).
                 generalize H11.
                 erewrite Byte.unsigned_repr.
                 intro V.
                 eapply repr_neq_e in V.
                 easy.
                 (* lemma: 0 <= snd (Exec.ber_fetch_tags ptr size 0 4)
                    <= Byte.max_unsigned *)
                 admit.
                 cbn in Heqp.
                 erewrite Heqp.
                 easy.
                  }
               break_if; auto.
               break_if.
               Zbool_to_Prop.
               lia.
               auto. }
             erewrite N.
             admit. (* entailer!. *) *)
             ++ admit. (* forward. 
                entailer!. *) 
             ++  forward.
                 forward_if True.
                 lia.
             ++++ forward_if (temp _t'18 Vzero); try congruence.
                  forward.
                  admit. (* entailer!. *)
                  forward_if.
                  lia.
                  forward;  admit. (* entailer!. *) 
             ++++  
              (* size : Z, data : list Z,
                 isc : Z, buf_b : block, buf_ofs : ptrofs,      
                 res_v : Z, res_ptr : val *)   
               erewrite Heqptr'.
               replace (data_at Tsh (tarray tuchar (len ptr))
                       (map Vint ptr) (Vptr b i))
                       with
                        (data_at Tsh tuchar (Vubyte (Byte.repr (Znth 0 ptr)))
                                   (Vptr b i) * 
                         data_at Tsh (tarray tuchar (len ptr - 1)) 
                                 (map Vubyte (map Byte.repr (sublist 1 (len ptr) ptr)))
                                   (Vptr b (i + Ptrofs.repr z0)%ptrofs))%logic.             
                forward_call (0, Vptr b (i + Ptrofs.repr z0)%ptrofs, size - z0, 
                             sublist 1 (len ptr) ptr, v_tlv_len).
                entailer!.
                cbn.
                repeat f_equal; auto.
                strip_repr.
                (* need Int.min_signed <= z0 <= Int.max_signed *)
                admit.
                unfold Frame.
                instantiate (1 := 
  [data_at Tsh tuchar (Vubyte (Byte.repr (Znth 0 ptr))) (Vptr b i) *
   data_at Tsh tuint (Vubyte (Byte.repr 
                 (snd (Exec.ber_fetch_tags ptr size 0 (sizeof tuint)))))
     v_tlv_tag *
   data_at Tsh (Tstruct _asn_codec_ctx_s noattr) (Vint (Int.repr max_stack_size)) 
           opt_codec_ctx_p *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__12 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__11 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__10 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__9 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__8 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__7 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__6 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__5 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__4 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__3 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__2 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__1 *
   data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval *
   field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p *
   field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
     (Vint (Int.repr (len (tags td)))) td_p *
   data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p *
   data_at_ Tsh asn_dec_rval_s res_p * data_at_ Tsh tint last_length_p]%logic).
                simpl.
                entailer!.
                autorewrite with sublist.
                entailer!.
                (* need 0 <= size - z0 <= Int.max_unsigned *)
                admit.
                Intros v.
                erewrite H10.
                assert (z2 = 99) as Z2 by admit.
                replace (fst
                       (Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 
                          (size - z0) (sizeof tuint) Int.modulus))
                  with z2.
                 match goal with
                 | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                   forward_switch Pre
                 end. clear Z2.
             admit. (* (* RC FAIL 
                 {  match goal with
                 | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                   forward_empty_while_break Pre
              end.
              rewrite_if_b. 
              forward_if True; try contradiction.
              forward.
              admit. (* entailer!. *) 
              forward_if (temp _t'20 Vzero);
               try forward; try entailer!.
             forward_if_add_sep (data_at Tsh 
                                         (Tstruct _asn_dec_rval_s noattr)
                                         (Vint (Int.repr 2), Vint (Int.repr 0))
                                         v_rval__7) v_rval__7; 
               try forward; try entailer!.
             repeat forward. 
             assert (ber_check_tags_primitive ptr td max_stack_size
                                              size (sizeof tuint) Int.modulus = None) as N.
             { unfold ber_check_tags_primitive.
               erewrite H0.
               erewrite Heqp.
               erewrite Heqp0.
               simpl.
               break_if; auto.
               break_if; auto.
               }
             erewrite N.
             admit. (* RC_FAIL *) } *) *)
             admit. (* same *)
                 forward.
                 admit. (* entailer! *)
                 forward.
                 forward_if.
                 admit. (* no indefinite length - see ber_fetch_length spec *)
                 forward_if True; try contradiction.
                 forward.
                 admit. (* entailer! *)
                 forward_if (temp _limit_len
           (Vint
              (Int.repr
                 (Byte.unsigned
                    (Byte.repr
                       (snd
                          (Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 
                             (size - z0) (sizeof tuint) Int.modulus)))) + 
               Int.repr z0 + Int.repr z2)%int)); try contradiction.
                 forward.
                 forward.
                 entailer!.
                 admit. (* bounds *)
                 forward_if (temp _limit_len
           (Vint
              (Int.repr
                 (Byte.unsigned
                    (Byte.repr
                       (snd
                          (Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 
                             (size - z0) (sizeof tuint) Int.modulus)))) + 
               Int.repr z0 + Int.repr z2)%int)); try contradiction.
                 (* RC_FAIL *)
            admit. (*      {  forward_empty_while.
              rewrite_if_b. 
              forward_if True; try contradiction.
              forward.
              admit. (* entailer!. *) 
              forward_if (temp _t'23 Vzero);
               try forward; try entailer!.
             forward_if_add_sep (data_at Tsh 
                                         (Tstruct _asn_dec_rval_s noattr)
                                         (Vint (Int.repr 2), Vint (Int.repr 0))
                                         v_rval__10) v_rval__10; 
               try forward; try entailer!.
             repeat forward. 
             assert (ber_check_tags_primitive ptr td max_stack_size
                                              size (sizeof tuint) Int.modulus = None) as N.
             { unfold ber_check_tags_primitive.
               erewrite H0.
               erewrite Heqp.
               erewrite Heqp0.
               simpl.
               break_if; auto.
               break_if; auto.
               generalize H14.
               strip_repr.
               erewrite Byte.unsigned_repr.
               replace (snd (Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 
                                                0 0 (size - z0) 4 Int.modulus))
                       with z3.
               intro.
               break_if; Zbool_to_Prop; try lia; auto.
               Zbool_to_Prop.
               lia.
               simpl in Heqp0.
               erewrite Heqp0.
               easy.
               (* bounds *)
               admit.
               admit.
               }
             erewrite N.
             admit. } *)
                 forward.
                 admit. (* entailer! *)
                 admit. (* entailer! *)
                 discriminate.
                **** (* ADVANCE *)
                 match goal with
                 | [ _ : _ |- semax _ ?Pre ?C ?Post ] =>
                   forward_empty_while_break 
                     (PROP (0 < z0; 0 < z2; 0 < z3; z0 <> 0; z2 <> -1;
                            z2 <> 0; z1 = nth 0 (tags td) 0)
  LOCAL (temp _consumed_myself (Vint (Int.repr 0 + (Int.repr z0 + Int.repr z2))%int);
  temp _size (Vint (Int.repr size - (Int.repr z0 + Int.repr z2))%int);
  temp _ptr
    (Vptr b
       (i +
        Ptrofs.repr (sizeof tschar) * 
        ptrofs_of_int Unsigned (Int.repr z0 + Int.repr z2)%int)%ptrofs);
  temp _num__2 (Vint (Int.repr z0 + Int.repr z2)%int);
  temp _limit_len
    (Vint
       (Int.repr
          (Byte.unsigned
             (Byte.repr
                (snd
                   (Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 
                      (size - z0) (sizeof tuint) Int.modulus)))) + 
        Int.repr z0 + Int.repr z2)%int);
  temp _t'29
    (Vubyte
       (Byte.repr
          (snd
             (Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 (size - z0) 
                (sizeof tuint) Int.modulus)))); 
  temp _len_len (Vint (Int.repr z2));
  temp _t'30 (Vint (Int.repr (len (tags td)))); 
  temp _t'15 Vzero; 
  temp _tlv_constr (Vint 0%int);
  temp _t'13 Vzero; temp _t'34 (Znth 0 (map Vint ptr));
  temp _tag_len (Vint (Int.repr z0)); temp _t'35 (Vint (Int.repr (len (tags td))));
  temp _t'10 (Val.of_bool (Int.repr 0 == Int.repr (len (tags td)))%int);
  temp _tagno (Vint (Int.repr z)); temp _t'4 Vzero; 
  temp _t'3 (Vint (Int.repr 0));
  temp _step (Vint (Int.repr z)); temp _t'1 Vzero;
  temp _expect_00_terminators (Vint (Int.repr 0));
  lvar _rval__12 (Tstruct _asn_dec_rval_s noattr) v_rval__12;
  lvar _rval__11 (Tstruct _asn_dec_rval_s noattr) v_rval__11;
  lvar _rval__10 (Tstruct _asn_dec_rval_s noattr) v_rval__10;
  lvar _rval__9 (Tstruct _asn_dec_rval_s noattr) v_rval__9;
  lvar _rval__8 (Tstruct _asn_dec_rval_s noattr) v_rval__8;
  lvar _rval__7 (Tstruct _asn_dec_rval_s noattr) v_rval__7;
  lvar _rval__6 (Tstruct _asn_dec_rval_s noattr) v_rval__6;
  lvar _rval__5 (Tstruct _asn_dec_rval_s noattr) v_rval__5;
  lvar _rval__4 (Tstruct _asn_dec_rval_s noattr) v_rval__4;
  lvar _rval__3 (Tstruct _asn_dec_rval_s noattr) v_rval__3;
  lvar _rval__2 (Tstruct _asn_dec_rval_s noattr) v_rval__2;
  lvar _rval__1 (Tstruct _asn_dec_rval_s noattr) v_rval__1;
  lvar _rval (Tstruct _asn_dec_rval_s noattr) v_rval; lvar _tlv_len tint v_tlv_len;
  lvar _tlv_tag tuint v_tlv_tag; temp __res res_p; temp _opt_codec_ctx opt_codec_ctx_p;
  temp _td td_p; temp _opt_ctx nullval; temp _tag_mode (Vint (Int.repr 0));
  temp _last_tag_form (Vint (Int.repr 0)); temp _last_length last_length_p;
  temp _opt_tlv_form nullval)
  SEP (data_at Tsh (tarray tuchar (len (sublist 1 (len ptr) ptr)))
         (map Vubyte (map Byte.repr (sublist 1 (len ptr) ptr)))
         (Vptr b (i + Ptrofs.repr z0)%ptrofs);
  data_at Tsh tint
    (Vubyte
       (Byte.repr
          (snd
             (Exec.ber_fetch_len (sublist 1 (len ptr) ptr) 0 0 (size - z0) 
                (sizeof tuint) Int.modulus)))) v_tlv_len;
  data_at Tsh tuchar (Vubyte (Byte.repr (Znth 0 ptr))) (Vptr b i);
  data_at Tsh tuint (Vubyte (Byte.repr (snd (Exec.ber_fetch_tags ptr size 0 (sizeof tuint)))))
    v_tlv_tag;
  data_at Tsh (Tstruct _asn_codec_ctx_s noattr) (Vint (Int.repr max_stack_size)) opt_codec_ctx_p;
  data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__12;
  data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__11;
  data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__10;
  data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__9;
  data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__8;
  data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__7;
  data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__6;
  data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__5;
  data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__4;
  data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__3;
  data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__2;
  data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval__1;
  data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval;
  field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p;
  field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
    (Vint (Int.repr (len (tags td)))) td_p;
  data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
  data_at_ Tsh asn_dec_rval_s res_p; data_at_ Tsh tint last_length_p))
                 end.
                 admit.
                 repeat forward.
                 admit. (* entailer!. *)
                 admit.
                 forward_if.
                 ***** 
                   (* z3 < size - z0 - z2 *) 
                 forward.
                 entailer!.
                 repeat split; do 2 f_equal.
                 rewrite Byte.unsigned_repr.
                 erewrite Heqp0.
                 cbn.
                 lia.
                 assert (ber_fetch_len_bounds :
                           forall (ptr : list Z) (isc len_r size sizeofval rssizem : Z),
                          0 <=  len_r <= 255 ->
                         Forall (fun x => 0 <= x <= Byte.max_unsigned) ptr ->
                         snd (Exec.ber_fetch_len ptr isc len_r size sizeofval rssizem) <> -1 ->
                        0 <= snd (Exec.ber_fetch_len ptr isc len_r size sizeofval rssizem) 
                        <= Byte.max_unsigned).
                 { intros.
                   unfold Exec.ber_fetch_len in H46.
                    unfold Exec.ber_fetch_len.
                   repeat break_if; cbn; try lia.
                   admit.
                   admit.
                   repeat break_let.
                   admit. }
                 eapply ber_fetch_len_bounds.
                 lia.
                 (* add to PRE:
                   Forall (fun x : Z => 0 <= x <= Byte.max_unsigned) ptr
                  also precondition to fetch length *)
                 admit.
                 
                 eapply repr_neq_e in H11.
                 generalize H11.
                 rewrite Byte.unsigned_repr.
                 easy.
                 admit.
                 cbn.
                 f_equal.
                 strip_repr.
                 (* NEED: 0 <= z0 + z2 <= Int.max_unsigned *)
                 admit.
                 replace (size - z0 - z2 >? z3) with true. 
                  (* true  *)
                 admit.
                   (* true  *)
                 symmetry.
                 generalize H17.
                 rewrite Byte.unsigned_repr.
                 simpl in Heqp0.
                 erewrite Heqp0.
                 strip_repr.
                 intro.
                 erewrite Z.gtb_lt.
                 lia.
                 (* Int.min_signed <= size - (z0 + z2) <= Int.max_signed *)
                 admit.
                 admit.
                 erewrite Heqp0.
                 erewrite Heqp.
                 simpl.
                 entailer!.
                 admit.
                 (* check Bytes and Int *)
                 *****
                 forward.
                 entailer!.
                 repeat split; do 2 f_equal.
                 (* true *)
                 admit.
                 (* true *)
                 admit.
                 replace (size - z0 - z2 >? z3)  with false by admit.
                 lia.
                 (* true  *)
                 admit.
                 (* true  *)
                 
                **** admit.
                **** admit.
               *** admit.
           * Zbool_to_Prop.
              simpl.
             Intros.
             Zbool_to_Prop.
             forward.
           forward_if.
           generalize H3.
           strip_repr.
           intro.
           lia.
         (*  unfold POSTCONDITION.
           unfold abbreviate.
           simpl. *)
           forward.
           assert (z = 1) as Z by lia.
           erewrite Z.
           entailer!.
           (* do 2 f_equal. try lia. *)
      +++  (* CONTINUE  to LI *)
          repeat break_let.
          forward.
          forward.
          Exists 1.
          repeat rewrite_if_b.
          repeat break_let.
          entailer!.
          break_if; Zbool_to_Prop; try lia.
          break_if; Zbool_to_Prop; try lia.          
          entailer!.         
      +++ (* BREAK to rest *)
          repeat break_let.
          forward_if True; try contradiction.
          forward.
          entailer!.
          
          forward_if_add_sep (data_at Tsh tint (Vint (Int.repr z2)) last_length_p) 
                             last_length_p; try contradiction.
          forward.
          forward.
          entailer!.
          (* RETURN OK *)
          forward_empty_while.
          forward_if True; try contradiction.
          forward.
          entailer!.
          forward_if (temp _t'25 Vone); try contradiction.
          forward.
          entailer!.
          discriminate.
          forward_if_add_sep
            (data_at Tsh (Tstruct _asn_dec_rval_s noattr)
                     (Vint (Int.repr 0), (Vint (Int.repr (z + z1))))
                     v_rval__12) v_rval__12. 
          forward.
          entailer!. 
          discriminate.
          repeat forward.
          assert (ber_check_tags_primitive
                    ptr td max_stack_size size (sizeof tuint)
                    Int.modulus = Some (z2, z + z1)) as B.
          {  unfold ber_check_tags_primitive.             
             erewrite Heqp.
             erewrite Heqp0.
             repeat rewrite_if_b.            
             repeat break_if;
               try destruct_orb_hyp;
               repeat rewrite_if_b; symmetry; repeat Zbool_to_Prop;
                 try lia; auto. }
          erewrite B.
          entailer!.  *)
Admitted.

End Ber_check_tags.
