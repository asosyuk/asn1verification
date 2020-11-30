Require Import Core.Core Lib.Lib Core.StructNormalizer 
        VstLib Int.Exec Lib.Callback.Dummy Lib.DWT.VST.Der_write_tags. 
Require Import VST.floyd.proofauto.
Require Import Clight.dummy Clight.INTEGER Prim.Der_encode_primitive.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Section Integer_der_encode.

Definition prim_type_s := (Tstruct _ASN__PRIMITIVE_TYPE_s noattr).
Definition mk_prim_type_s (buf_p : val) size := (buf_p, Vint (Int.repr size)).


Definition int_enc_rval td li struct_len buf_size td_p sptr_p := 
  match evalErrW (int_encoder td struct_len buf_size li) [] with
  | Some v => mk_enc_rval (v) Vzero Vzero
  | None => mk_enc_rval (-1) td_p sptr_p
  end.

Definition int_enc_res td struct_len buf_size li := 
  match execErrW (int_encoder td struct_len buf_size li) [] with
  | Some v => v
  | None => []
  end.

Definition Z_of_val v := 
  match v with
  | Vptr b i => Ptrofs.unsigned i 
  | _ => 0
  end.

Instance Change1 : change_composite_env Callback.Dummy.CompSpecs CompSpecs.
Proof. make_cs_preserve Dummy.CompSpecs CompSpecs. Defined.

Instance Change2 : change_composite_env CompSpecs Dummy.CompSpecs.
Proof. make_cs_preserve CompSpecs Dummy.CompSpecs. Defined.

Instance Change4 : change_composite_env CompSpecs Der_encode_primitive.CompSpecs.
Proof. make_cs_preserve CompSpecs Der_encode_primitive.CompSpecs. Defined.

Instance Change3 : change_composite_env Der_encode_primitive.CompSpecs CompSpecs.
Proof. make_cs_preserve Der_encode_primitive.CompSpecs CompSpecs. Defined.


Definition int_der_encode_spec : ident * funspec :=
  DECLARE _INTEGER_encode_der
    WITH res_p : val,  
         sptr_p : val, sptr_buf : val, tag_b : block, tag_ofs : ptrofs, 
         struct_len : Z, data : list byte,
         td_p : val, td : TYPE_descriptor,
         tag_mode : Z,
         cb_p : val, app_key_p : val
    PRE [tptr enc_rval_s, tptr type_descriptor_s, tptr tvoid, tint, tuint, 
          tptr cb_type, tptr tvoid]
      PROP (1 = Zlength (tags td);
            tag_mode = 0;
            0 <= struct_len <= Int.max_signed - 11;
            sptr_p <> nullval; 
            is_pointer_or_null sptr_buf;
            struct_len = Zlength data;
            0 <= Z_of_val sptr_buf + struct_len <= Ptrofs.max_unsigned)
      PARAMS (res_p; td_p; sptr_p; Vint (Int.repr tag_mode);
              Vint (Int.repr 0); cb_p; app_key_p)
      GLOBALS ()
      SEP (data_at_ Tsh enc_rval_s res_p;
           field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr) 
                    (DOT der_encoder._tags) (Vptr tag_b tag_ofs) td_p;
           field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr)
                    (DOT der_encoder._tags_count) 
                    (Vint (Int.repr (Zlength (tags td)))) td_p;
           data_at Tsh (tarray tuint (Zlength (tags td))) 
                   (map Vint (map Int.repr (tags td)))
                   (Vptr tag_b tag_ofs);
           valid_pointer sptr_buf;
           if eq_dec sptr_buf nullval 
           then emp else
           data_at Tsh (tarray tuchar (Zlength data)) (map Vubyte data) sptr_buf; 
           field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr struct_len)) sptr_p;
           field_at Tsh prim_type_s (DOT _buf) sptr_buf sptr_p; 
           data_at_ Tsh enc_key_s app_key_p;
           valid_pointer cb_p; 
           func_ptr' dummy_callback_spec cb_p)
    POST [tvoid]
      PROP ()
      LOCAL ()
      SEP (field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr) 
                    (DOT der_encoder._tags) (Vptr tag_b tag_ofs) td_p;
           field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr)
                    (DOT der_encoder._tags_count)
                    (Vint (Int.repr (Zlength (tags td)))) td_p;
           data_at Tsh (tarray tuint (Zlength (tags td)))
                   (map Vint (map Int.repr (tags td)))
                   (Vptr tag_b tag_ofs);
            valid_pointer sptr_buf;
           if eq_dec sptr_buf nullval 
           then emp else
           data_at Tsh (tarray tuchar (Zlength data)) (map Vubyte data) sptr_buf;
           field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr struct_len)) sptr_p;
           field_at Tsh prim_type_s (DOT _buf)  sptr_buf sptr_p;
           data_at Tsh enc_rval_s (int_enc_rval td data struct_len 
                                                (if eq_dec cb_p nullval
                                                then 0
                                                else 32) td_p sptr_p) res_p;
           valid_pointer cb_p;
           data_at_ Tsh enc_key_s app_key_p;
           func_ptr' dummy_callback_spec cb_p).

Definition Gprog := ltac:(with_library prog [int_der_encode_spec; 
                                               der_primitive_encoder_spec]).

Ltac forward_empty_loop :=
      match goal with
      | [ _ : _ |- semax _ ?Pre (Ssequence (Sloop Sskip Sbreak) _) _ ] =>
          forward_loop Pre break: Pre; try forward ; try entailer! 
      end. 

Ltac prove_field_compatible_arr := 
  match goal with
  | |- field_compatible _ _ ?p => 
    match p with
    | (Vptr _ ?ofs) => 
      unfold field_compatible;
      repeat split; cbn; 
      [rewrite Zmax0r by lia; rep_omega
      | constructor 2
      | lia
      | lia];
      match goal with
      | |- (forall i, _) => intros i; intros; econstructor 1; cbn; 
                     [reflexivity 
                     | cbn; unfold Z.divide; exists (Ptrofs.unsigned ofs + i); lia ]
      | _ => fail "Something went wrong"
      end
    | _ => fail "?p must be in the form (Vptr _ ?ofs)"
    end
  | _ => fail "Goal must be in the form field_compatible _ _ ?p"
  end.

Theorem int_der_encode : semax_body Vprog Gprog 
                                     (normalize_function f_INTEGER_encode_der
                                                         composites)
                                     int_der_encode_spec.
Proof.
  start_function. 
  rename H into DT.
  remember (Vptr tag_b tag_ofs) as buf_p.
  replace (Tstruct _asn_enc_rval_s noattr) with enc_rval_s by reflexivity.
  replace (Tstruct _ASN__PRIMITIVE_TYPE_s noattr) with prim_type_s by reflexivity.
  forward.
  forward_empty_loop.
  (* add condition about shift here *)
  forward_if (
      PROP ( ) 
      LOCAL (temp _t'2 sptr_buf; temp _st sptr_p; 
             lvar __res__1 enc_rval_s v__res__1;
           (*  lvar _unconst (Tunion __4050 noattr) v_unconst; *)
             lvar _effective_integer prim_type_s v_effective_integer;
             lvar _rval (Tstruct _asn_enc_rval_s noattr) v_rval; 
             temp __res res_p; temp _td td_p; 
             temp _sptr sptr_p; temp _tag_mode (Vint (Int.repr tag_mode));
             temp _tag (Vint (Int.repr 0)); 
             temp _cb cb_p; temp _app_key app_key_p)
       SEP ((* Local vars *)
            data_at_ Tsh enc_rval_s v__res__1;
           (* data_at_ Tsh (Tunion __4050 noattr) v_unconst; *)
            data_at_ Tsh prim_type_s v_effective_integer;
            data_at_ Tsh (Tstruct _asn_enc_rval_s noattr) v_rval; 
            (* type descriptor *)
            field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr) 
                    (DOT der_encoder._tags) (Vptr tag_b tag_ofs) td_p;
           field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr)
                    (DOT der_encoder._tags_count) (Vint (Int.repr (Zlength (tags td)))) td_p;
           data_at Tsh (tarray tuint (Zlength (tags td))) (map Vint (map Int.repr (tags td)))
                   (Vptr tag_b tag_ofs);
            (* sptr *)
            valid_pointer sptr_buf;
            if eq_dec sptr_buf nullval
            then emp
            else data_at Tsh (tarray tuchar struct_len) (map Vubyte data) sptr_buf;

            (* st->buf + shift;
            effective_integer.size = st->size - shift; *)
            field_at Tsh prim_type_s (DOT _buf) sptr_buf sptr_p;
            field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr struct_len)) sptr_p; 
            (* Result *)
            data_at_ Tsh enc_rval_s res_p;
            (* Callback *)
            data_at_ Tsh enc_key_s app_key_p;
            valid_pointer cb_p;
            func_ptr' dummy_callback_spec cb_p)).
  * (* sptr_buf->buf <> null *)
    destruct sptr_buf; simpl in H;   try contradiction.
    Require Import VstTactics.
    rewrite if_false by discriminate.
    repeat forward.
    normalize.
    forward_loop (EX z : Z, 
               PROP (0 <=  z;
                     Ptrofs.unsigned i + z <= Ptrofs.max_unsigned)
               LOCAL (temp 
                        _end1 
                        (Vptr b
                              (Ptrofs.sub 
                                 (Ptrofs.add i (Ptrofs.repr struct_len)) (Ptrofs.repr 1))); 
                      temp _buf (Vptr b (Ptrofs.add i (Ptrofs.repr z))); 
                      temp _t'9 (Vint (Int.repr struct_len));
                      temp _t'2 (Vptr b i); temp _st sptr_p;
                      lvar __res__1 enc_rval_s v__res__1; 
                    (* lvar _unconst (Tunion __4050 noattr) v_unconst; *)
                      lvar _effective_integer prim_type_s v_effective_integer; 
                      lvar _rval enc_rval_s v_rval; 
                      temp _tag (Vint (Int.repr 0));
                      temp __res res_p; temp _td td_p; temp _sptr sptr_p;
                      temp _tag_mode (Vint (Int.repr tag_mode));
                      temp _cb cb_p; temp _app_key app_key_p)
               SEP (data_at_ Tsh enc_rval_s v__res__1; 
                   (* data_at_ Tsh (Tunion __4050 noattr) v_unconst; *)
                    data_at_ Tsh prim_type_s v_effective_integer; 
                    data_at_ Tsh enc_rval_s v_rval;
                    data_at_ Tsh enc_rval_s res_p;
                    data_at_ Tsh enc_key_s app_key_p;
                     field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr) 
                              (DOT der_encoder._tags) (Vptr tag_b tag_ofs) td_p;
                     field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr)
                              (DOT der_encoder._tags_count) 
                              (Vint (Int.repr (Zlength (tags td)))) td_p;
                     data_at Tsh (tarray tuint (Zlength (tags td)))
                             (map Vint (map Int.repr (tags td)))
                             (Vptr tag_b tag_ofs);
                     (* sptr *)
                     valid_pointer (Vptr b i);
                      data_at Tsh (tarray tuchar (Zlength data)) (map Vubyte data) (Vptr b i);
                     field_at Tsh prim_type_s (DOT _buf) (Vptr b i) sptr_p;
                     field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr struct_len)) sptr_p;  
                     valid_pointer cb_p;
                     func_ptr' dummy_callback_spec cb_p))%assert
      continue: (EX z : Z, 
               PROP (0 <= z;
                     Ptrofs.unsigned i+ z + 1 <= Ptrofs.max_unsigned)
               LOCAL (temp 
                        _end1 
                        (Vptr b
                              (Ptrofs.sub 
                                 (Ptrofs.add i(Ptrofs.repr struct_len)) (Ptrofs.repr 1))); 
                      temp _t'9 (Vint (Int.repr struct_len));
                      temp _buf (Vptr b(Ptrofs.add i (Ptrofs.repr z))); 
                      temp _t'2 (Vptr b i); temp _st sptr_p;
                      lvar __res__1 enc_rval_s v__res__1; 
                     (* lvar _unconst (Tunion __4050 noattr) v_unconst; *)
                      lvar _effective_integer prim_type_s v_effective_integer; 
                      lvar _rval enc_rval_s v_rval; temp _tag (Vint (Int.repr 0));
                      temp __res res_p; temp _td td_p; temp _sptr sptr_p;
                      temp _tag_mode (Vint (Int.repr tag_mode));
                      temp _cb cb_p; temp _app_key app_key_p)
               SEP (data_at_ Tsh enc_rval_s v__res__1; 
                   (* data_at_ Tsh (Tunion __4050 noattr) v_unconst; *)
                    data_at_ Tsh prim_type_s v_effective_integer; 
                    data_at_ Tsh enc_rval_s v_rval;
                    data_at_ Tsh enc_rval_s res_p;
                    data_at_ Tsh enc_key_s app_key_p;
                     field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr) 
                              (DOT der_encoder._tags) (Vptr tag_b tag_ofs) td_p;
                     field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr)
                              (DOT der_encoder._tags_count) 
                              (Vint (Int.repr (Zlength (tags td)))) td_p;
                     data_at Tsh (tarray tuint (Zlength (tags td)))
                             (map Vint (map Int.repr (tags td)))
                             (Vptr tag_b tag_ofs);
                     (* sptr *)
                     valid_pointer (Vptr b i);
                      data_at Tsh (tarray tuchar (Zlength data)) (map Vubyte data) (Vptr b i);
                     field_at Tsh prim_type_s (DOT _buf) (Vptr b i) sptr_p;
                     field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr struct_len)) sptr_p;  
                     valid_pointer cb_p;
                     func_ptr' dummy_callback_spec cb_p))%assert
      break: (EX z : Z,
              PROP ()
              LOCAL (
                     temp 
                       _end1 
                       (Vptr b
                             (Ptrofs.sub 
                                (Ptrofs.add i(Ptrofs.repr struct_len)) (Ptrofs.repr 1))); 
                     temp _t'9 (Vint (Int.repr struct_len));
                     temp _buf (Vptr b(Ptrofs.add i(Ptrofs.repr z))); 
                     temp _t'2 (Vptr b i); 
                     temp _st sptr_p; lvar __res__1 enc_rval_s v__res__1; 
                    (* lvar _unconst (Tunion __4050 noattr) v_unconst; *)
                     lvar _effective_integer prim_type_s v_effective_integer; 
                     lvar _rval enc_rval_s v_rval; temp _tag (Vint (Int.repr 0));
                     temp __res res_p; temp _td td_p; temp _sptr sptr_p;
                     temp _tag_mode (Vint (Int.repr tag_mode));
                     temp _cb cb_p; temp _app_key app_key_p)
              SEP (data_at_ Tsh enc_rval_s v__res__1; 
                  (*  data_at_ Tsh (Tunion __4050 noattr) v_unconst; *)
                    data_at_ Tsh prim_type_s v_effective_integer; 
                    data_at_ Tsh enc_rval_s v_rval;
                    data_at_ Tsh enc_rval_s res_p;
                    data_at_ Tsh enc_key_s app_key_p;
                     field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr) 
                              (DOT der_encoder._tags) (Vptr tag_b tag_ofs) td_p;
                     field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr)
                              (DOT der_encoder._tags_count) 
                              (Vint (Int.repr (Zlength (tags td)))) td_p;
                     data_at Tsh (tarray tuint (Zlength (tags td)))
                             (map Vint (map Int.repr (tags td)))
                             (Vptr tag_b tag_ofs);
                     (* sptr *)
                     valid_pointer (Vptr b i);
                      data_at Tsh (tarray tuchar (Zlength data)) (map Vubyte data) (Vptr b i);
                     field_at Tsh prim_type_s (DOT _buf) (Vptr b i) sptr_p;
                     field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr struct_len)) sptr_p;  
                     valid_pointer cb_p;
                     func_ptr' dummy_callback_spec cb_p))%assert.
    - (* invariant check *)
      Exists 0.
      entailer!.
    - (* loop *)
      Intros z.
      forward_if.
      unfold test_order_ptrs, sameblock.
      destruct peq; try congruence. simpl.
      entailer!.
      admit. (* weak valid pointer admit *)
      cbn in H5.
      assert (Z : 0 < z + 1 < Zlength data).
      { unfold typed_true, strict_bool_val, sem_cmp_pp in H8; cbn in H8.
        destruct eq_block in H8; try congruence.
        break_match_hyp; try congruence.
        unfold force_val, Val.of_bool, Ptrofs.ltu in Heqv; cbn in Heqv.
        destruct zlt in Heqv.
        unfold Ptrofs.add in l.
        repeat rewrite ->Ptrofs.add_unsigned in l.
        replace (Ptrofs.repr 1) with Ptrofs.one in l by reflexivity.
        unfold Ptrofs.sub in l.
        replace (Ptrofs.unsigned (Ptrofs.repr z)) with z in l.
        rewrite Ptrofs.unsigned_repr in l.
        replace (Ptrofs.unsigned (Ptrofs.repr struct_len)) with struct_len in l.
        replace (Ptrofs.unsigned Ptrofs.one) with 1 in l by reflexivity.
        rewrite Ptrofs.unsigned_repr in l at 1.
        rewrite Ptrofs.unsigned_repr in l.
        assert (T : forall p, (p + struct_len - 1) = (p + struct_len + (-1))) by (intros; lia);
          rewrite T in l; clear T.
        rewrite <-Z.add_assoc in l.
        apply Zplus_lt_reg_l with (n := z) (m := (struct_len + -1)) 
                                    (p := Ptrofs.unsigned i) in l.
        lia.
        Require Import Core.Tactics.
        all: simpl in *.
        rep_omega.
        rewrite Ptrofs.unsigned_repr; try rep_omega.
        rewrite Ptrofs.unsigned_repr in l at 1.
         rewrite Ptrofs.unsigned_repr in l.
         rep_omega.
         rep_omega.
        rewrite Ptrofs.unsigned_repr;  try rep_omega.
        rewrite Ptrofs.unsigned_repr in l at 1.
         rewrite Ptrofs.unsigned_repr in l.
         rep_omega.
         rep_omega.
        rewrite Ptrofs.unsigned_repr. 
        all: admit. }

      assert_PROP (Vptr b (Ptrofs.add i (Ptrofs.repr z)) =
                  field_address (tarray tuchar (Zlength data)) (SUB z) (Vptr b i)).
      entailer!.
 
      assert (FA : field_compatible (tarray tuchar (Zlength data)) (SUB z) 
                                    (Vptr b i)).
      (* prove_field_compatible_arr. *) admit.
      apply field_compatible_field_address in FA.
      rewrite FA; cbn; replace (0 + 1* z) with (z) by lia; try reflexivity.
      forward.
      entailer!.
      { cbn; pose proof Byte.unsigned_range_2 (Znth z data) as T; cbn in T; 
          inversion T as [T1 T2].
        pose proof unsigned_repr_le (Byte.unsigned (Znth z data)) T1.
        lia. }
      rewrite Znth_map_Vubyte by lia.
      forward_if (
          PROP ( ) 
          LOCAL ((*if eq_dec (Byte.unsigned (Znth z data)) 0 
                 then temp _t'8 (Vubyte (Znth (z + 1) data))
                 else if eq_dec (Byte.unsigned (Znth z data)) 255 
                      then     temp _t'7 (Vubyte (Znth (z + 1) data))
                      else temp _t'6 (Vubyte (Znth z data)); *)
                 temp _t'6 (Vubyte (Znth z data)); 
                 temp _end1 (Vptr b(Ptrofs.sub 
                                           (Ptrofs.add i(Ptrofs.repr struct_len)) 
                                           (Ptrofs.repr 1)));
                 temp _buf (Vptr b (Ptrofs.add i (Ptrofs.repr z)));
                 temp _t'9 (Vint (Int.repr struct_len)); temp _t'2 (Vptr b i); 
                 temp _st sptr_p; lvar __res__1 enc_rval_s v__res__1;
                (* lvar _unconst (Tunion __4050 noattr) v_unconst; *)
                 lvar _effective_integer prim_type_s v_effective_integer; 
                 lvar _rval enc_rval_s v_rval;
                 temp _tag (Vint (Int.repr 0)); temp __res res_p; temp _td td_p; 
                 temp _sptr sptr_p; temp _tag_mode (Vint (Int.repr tag_mode)); 
                 temp _cb cb_p; temp _app_key app_key_p)
          SEP (data_at_ Tsh enc_rval_s v__res__1; 
              (* data_at_ Tsh (Tunion __4050 noattr) v_unconst; *)
               data_at_ Tsh prim_type_s v_effective_integer; 
               data_at_ Tsh enc_rval_s v_rval; 
               data_at_ Tsh enc_rval_s res_p; 

               field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr) 
                              (DOT der_encoder._tags) (Vptr tag_b tag_ofs) td_p;
                     field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr)
                              (DOT der_encoder._tags_count) 
                              (Vint (Int.repr (Zlength (tags td)))) td_p;
                     data_at Tsh (tarray tuint (Zlength (tags td)))
                             (map Vint (map Int.repr (tags td)))
                             (Vptr tag_b tag_ofs);
               
               data_at_ Tsh enc_key_s app_key_p; 

               valid_pointer (Vptr b i); 
               
               data_at Tsh (Tarray tuchar (Zlength data) noattr) (map Vubyte data) 
                       (Vptr b i); 
               field_at Tsh prim_type_s (DOT _buf) (Vptr b i) sptr_p; 
               field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr struct_len)) sptr_p; 
               valid_pointer cb_p;
               func_ptr' dummy_callback_spec cb_p)).
      -- (* case 0 *)
      { (* *buf = 0 -> first switch case *)

        assert_PROP (Vptr b (Ptrofs.add (Ptrofs.add i(Ptrofs.repr z)) 
                                            (Ptrofs.mul (Ptrofs.repr 1) 
                                                        (Ptrofs.of_ints (Int.repr 1)))) =
                     field_address (tarray tuchar (Zlength data) ) (SUB (z + 1)) (Vptr b i)).
        entailer!.
        assert (FA : field_compatible (tarray tuchar (Zlength data)) (SUB (z + 1)) 
                                 (Vptr b i)).
        (* prove_field_compatible_arr. *) 
        { econstructor. auto. repeat split; auto. cbn. 
          unfold Z.max. break_match; simpl in H5; try rep_omega. 
          all: try rep_omega. admit.  }
        apply field_compatible_field_address in FA.
        rewrite FA; cbn; replace (0 + 1 * (z + 1)) with (z + 1) by lia; reflexivity.
        forward.
        entailer!.
        { cbn; pose proof Byte.unsigned_range_2 (Znth (z + 1) data) as T; cbn in T; 
            inversion T as [T1 T2].
          pose proof unsigned_repr_le (Byte.unsigned (Znth (z + 1) data)) T1.
          lia. }
        simpl in H5.
        forward_if.
        + (* buf[1] & 0x80 = 0 -> continue *) 
          forward.
          Exists z.
          entailer!.
        + (* buf[1] & 0x80 <> 0 -> break *)
          forward.
          Exists z.
          entailer!.
      }
      -- (* case 1 *)
      { (* *buf = 255 -> second switch case *)

        assert_PROP (Vptr b(Ptrofs.add (Ptrofs.add i(Ptrofs.repr z)) 
                                            (Ptrofs.mul (Ptrofs.repr 1) 
                                                        (Ptrofs.of_ints (Int.repr 1)))) =
                     field_address (tarray tuchar  (Zlength data)) (SUB (z + 1)) (Vptr b i)).
        entailer!.
        assert (FA : field_compatible (tarray tuchar (Zlength data)) (SUB (z + 1)) 
                                 (Vptr b i)).
        (* prove_field_compatible_arr. *) admit.
        apply field_compatible_field_address in FA.
        rewrite FA; cbn; replace (0 + 1 * (z + 1)) with (z + 1) by lia; reflexivity.
        forward.
        entailer!.
        { cbn; pose proof Byte.unsigned_range_2 (Znth (z + 1) data) as T; cbn in T; 
            inversion T as [T1 T2].
          pose proof unsigned_repr_le (Byte.unsigned (Znth (z + 1) data)) T1.
          lia. }

        simpl in H5.
        forward_if.
        + (* buf[1] & 0x80 <> 0 -> continue *)
          forward. 
          Exists z.
          entailer!.
        + (* buf[1] & 0x80 = 0 -> break *)
          forward.
          Exists z.
          entailer!.
      }
      --
       (* default case *)
        forward. 
        Exists z.
        entailer!.
      --
       (* break after switch *)
        forward. 
        Exists z.
        entailer!.
    - (* continue post-condition *)
      Intros z.
      forward.
      Exists (z + 1).
      entailer!. 
    - (* after switch shift manipulation *)
      Intros z.
      repeat forward.
      entailer!.
      unfold denote_tc_samebase.
      unfold sameblock.
      destruct peq; try congruence.
      entailer!.
      forward_if.
      + (* shift <> 0 *)
        (*
        repeat forward.
        entailer!.
        (* sptr_p = v_effective_integer WHY ?*)
        admit.
        rewrite if_false by discriminate.
        entailer!.
      + (* shift = 0 *)
        forward.
        rewrite if_false by discriminate.
        entailer!. 
  * (* sptr_buf = nullval *)
    forward.
    subst.
    repeat rewrite if_true by auto.
    entailer!.
  * (* sptr_buf is null or pointer - we pass it to prim decoder anyway *)
    forward_call (v__res__1,   
                  sptr_p,
                  tag_b, tag_ofs,
                  sptr_buf, 
                  map Byte.unsigned data,
                  struct_len,
                  td_p, td,
                  0,
                  cb_p, app_key_p).
    entailer!.
    unfold Frame.
    instantiate (1 := [(* data_at_ Tsh (Tunion __4050 noattr) v_unconst * *)
                       data_at_ Tsh prim_type_s v_effective_integer *
                       data_at_ Tsh (Tstruct _asn_enc_rval_s noattr) v_rval *
                       data_at_ Tsh enc_rval_s res_p]).
    simpl.
    break_if; entailer!.
    (* compspecs issue *)
    admit.
    replace (Zlength (map Byte.unsigned data)) with (Zlength (data)).
    replace (map Vint (map Int.repr (map Byte.unsigned data))) with (map Vubyte data).
    entailer!.
    (* tuint and tuchar issue, compspecs issue *)
    admit.
    admit.
    erewrite Zlength_map. auto.
    Intros.
    unfold prim_enc_rval.
    destruct (evalErrW
           (Exec.primitive_encoder td struct_len (if eq_dec cb_p nullval then 0 else 32)
              (map Int.repr (map Byte.unsigned data))) []) eqn : G.
    -- repeat forward. 
       Require Import Forward.
       forward_if_add_sep (
        if eq_dec (Vint Int.zero) v_effective_integer 
        then data_at Tsh (Tstruct _asn_enc_rval_s noattr)
                       (Vint (Int.repr z), (Vint Int.zero, sptr_p))
                       v_rval
        else data_at Tsh (Tstruct _asn_enc_rval_s noattr)
                       (Vint (Int.repr z),
                        (Vint Int.zero, Vint Int.zero)) v_rval) v_rval.
       ++ entailer!.
          eapply denote_tc_test_eq_split.
          entailer!.
          unfold prim_type_s.
          unfold data_at_.
          unfold field_at_.
          simpl.
          assert (0 < sizeof (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) by (cbn; lia).
          assert (field_at Tsh (Tstruct _ASN__PRIMITIVE_TYPE_s noattr) []
                           (default_val
                              (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                           v_effective_integer
                           |-- valid_pointer v_effective_integer) as F.
          { eapply field_at_valid_ptr0; cbn; auto.
            lia. }
          entailer!.
       ++ forward.
          break_if;
          rewrite if_true;
          try entailer!.
          all: destruct v_effective_integer; cbn in H; try contradiction;
          try discriminate;
          eapply typed_true_of_bool in H;
          eapply int_eq_e in H;
          erewrite H; auto.
       ++ forward.
          break_if;
          rewrite if_false;
          try entailer!;
          destruct v_effective_integer; cbn in H; try contradiction;
          try discriminate;
          eapply typed_false_of_bool in H;
          eapply int_eq_false_e in H;
          unfold not; intro K;
          inversion K; contradiction.
       ++ destruct (eq_dec (Vint Int.zero) v_effective_integer) eqn : S.
          **
          repeat forward.
          **
          repeat forward.
          entailer!.
          assert ((int_enc_rval td data (Zlength data) (if eq_dec cb_p nullval then 0 else 32)
                                td_p sptr_p) = 
                   (Vint (Int.repr z), (Vint Int.zero, Vint Int.zero))) as RES.
           { unfold int_enc_rval.
             unfold evalErrW.
             unfold int_encoder.
             generalize G.
             break_if.
             -
             Require Import VstTactics.
             rewrite_if_b.
             unfold evalErrW.
             break_match. congruence.
             break_let. intro GG.
             inversion GG.
             auto.
             - rewrite_if_b.
               unfold evalErrW.
               break_match. congruence.
               break_let. intro GG.
               inversion GG.
               auto.
               (* need (canonicalize_int data) instead of  data *)
               admit. }
           erewrite RES.
           entailer!.
           (* tuint and tuchar issue, compspecs issue *)
           admit.
    -- repeat forward.       
       forward_if_add_sep (
        if eq_dec sptr_p v_effective_integer 
        then data_at Tsh (Tstruct _asn_enc_rval_s noattr)
                     (Vint (Int.repr (-1)), (td_p, sptr_p)) v_rval
        else data_at Tsh (Tstruct _asn_enc_rval_s noattr)
                     (Vint (Int.repr (-1)), (td_p, sptr_p)) v_rval) v_rval.
       ++ eapply denote_tc_test_eq_split.
          admit. (* valid_pointer sptr_p *)
          unfold prim_type_s.
          unfold data_at_.
          unfold field_at_.
          simpl.
          assert (0 < sizeof (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)) by (cbn; lia).
          assert (field_at Tsh (Tstruct _ASN__PRIMITIVE_TYPE_s noattr) []
                           (default_val
                              (Tstruct _ASN__PRIMITIVE_TYPE_s noattr))
                           v_effective_integer
                           |-- valid_pointer v_effective_integer) as F.
          { eapply field_at_valid_ptr0; cbn; auto.
            lia. }
          entailer!. 
       ++ forward.
          break_if.
          ** rewrite if_true.
             entailer!.
          { (* need  typed_true tint (force_val (sem_cmp_pp Ceq sptr_p v_effective_integer))
               ->   sptr_p = v_effective_integer *)  admit. }
          ** rewrite if_false.
             entailer!.
             admit.
       ++ forward.
          break_if.
          (* contradiction *)
          admit.
          { admit. }
       ++ 
         destruct (eq_dec sptr_p v_effective_integer) eqn: EI.
          **
          repeat forward.
          entailer!.
              assert ((int_enc_rval td data (Zlength data) 
                                    (if eq_dec cb_p nullval then 0 else 32) td_p
                                    v_effective_integer) = 
                   (Vint (Int.repr (-1)), (td_p, v_effective_integer))) as RES.
              {  unfold int_enc_rval.
                 unfold evalErrW.
                 unfold int_encoder.
                 generalize G.
                 break_if.
                 -
                   Require Import VstTactics.
                   rewrite_if_b.
                   unfold evalErrW.
                   break_match; try break_let; try congruence.
                   auto.
                 - rewrite_if_b.
                   unfold evalErrW.
                   break_match;  try break_let; try congruence.
                   (* need (canonicalize_int data) instead of  data *)
                   admit.
           }
           erewrite RES.
           entailer!.
           (* tuint and tuchar issue, compspecs issue *)
           admit.
          **
          repeat forward.
          entailer!.
           assert ((int_enc_rval td data (Zlength data)
                                 (if eq_dec cb_p nullval
                                  then 0 else 32) 
                                 td_p sptr_p) = 
                   (Vint (Int.repr (-1)), (td_p, sptr_p))) as RES.
           {  unfold int_enc_rval.
              unfold evalErrW.
              unfold int_encoder.
              generalize G.
              break_if.
              -
                Require Import VstTactics.
                rewrite_if_b.
                unfold evalErrW.
                break_match; try break_let; try congruence.
                auto.
              - rewrite_if_b.
                unfold evalErrW.
                break_match;  try break_let; try congruence.
                (* need (canonicalize_int data) instead of  data *)
                admit. }
           erewrite RES.
           entailer!.
           (* tuint and tuchar issue, compspecs issue *)
           admit.  
Admitted.

End Integer_der_encode.

