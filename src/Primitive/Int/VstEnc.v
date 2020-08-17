Require Import Core.Core Lib.Lib Core.StructNormalizer 
        VstLib Int.Exec Lib.Callback.Dummy Lib.DWT.Vst. 
Require Import VST.floyd.proofauto.
Require Import Clight.dummy Clight.INTEGER.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Section Integer_der_encode.

Definition prim_type_s := (Tstruct _ASN__PRIMITIVE_TYPE_s noattr).
Definition mk_prim_type_s (buf_p : val) size := (buf_p, Vint (Int.repr size)).

Definition int_enc_rval td li td_p sptr_p := 
  match evalErrW (int_encoder td li) [] with
  | Some v => mk_enc_rval (encoded v) td_p Vzero
  | None => mk_enc_rval (-1) td_p sptr_p
  end.

Definition int_enc_res td li := 
  match execErrW (int_encoder td li) [] with
  | Some v => v
  | None => []
  end.

Definition int_der_encode_spec : ident * funspec :=
  DECLARE _INTEGER_encode_der
    WITH res_p : val,  
         sptr_p : val, buf_b : block, buf_ofs : ptrofs, 
         size : Z, data : list byte,
         td_p : val, td : TYPE_descriptor,
         tag_mode : Z, tag : Z,
         cb_p : val, app_key_p : val
    PRE [tptr enc_rval_s, tptr type_descriptor_s, tptr tvoid, tint, tuint, 
          tptr cb_type, tptr tvoid]
      PROP (decoder_type td = BOOLEAN_t;
            1 < size <= Int.max_unsigned;
            size = Zlength data;
            Forall (fun x => Int.unsigned (Int.repr (Byte.signed x)) <= 
                          Byte.max_unsigned) data;
            (* if sptr_p is null, then encoder will crush *)
            sptr_p <> nullval;
            is_pointer_or_null (Vptr buf_b buf_ofs);
            is_pointer_or_null (Vptr buf_b (Ptrofs.add buf_ofs (Ptrofs.repr size)));
            0 <= Ptrofs.unsigned buf_ofs + size <= Ptrofs.max_unsigned)
      PARAMS (res_p; td_p; sptr_p; Vint (Int.repr tag_mode);
              Vint (Int.repr tag); cb_p; app_key_p)
      GLOBALS ()
      SEP (data_at_ Tsh enc_rval_s res_p;
           data_at_ Tsh type_descriptor_s td_p; 
           (* sptr *)
           valid_pointer (Vptr buf_b buf_ofs);
           if Val.eq (Vptr buf_b buf_ofs) nullval 
           then emp
           else data_at Tsh (tarray tuchar size) (map Vubyte data) (Vptr buf_b buf_ofs);
           field_at Tsh prim_type_s (DOT _buf) (Vptr buf_b buf_ofs) sptr_p;
           field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p;
           (* Callback *)
           data_at_ Tsh enc_key_s app_key_p;
           valid_pointer cb_p)
    POST [tvoid]
      PROP ()
      LOCAL ()
      SEP (data_at_ Tsh type_descriptor_s td_p;
           (* sptr *)
           valid_pointer (Vptr buf_b buf_ofs);
           if Val.eq (Vptr buf_b buf_ofs) nullval 
           then emp
           else data_at Tsh (tarray tuchar size) (map Vubyte (int_enc_res td data)) 
                        (Vptr buf_b buf_ofs);
           data_at Tsh prim_type_s (mk_prim_type_s (Vptr buf_b buf_ofs) size) sptr_p;
           (* Result *)
           data_at Tsh enc_rval_s (int_enc_rval td data td_p sptr_p) res_p;
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
  remember (Vptr buf_b buf_ofs) as buf_p.
  replace (Tstruct _asn_enc_rval_s noattr) with enc_rval_s by reflexivity.
  replace (Tstruct _ASN__PRIMITIVE_TYPE_s noattr) with prim_type_s by reflexivity.
  forward.
  forward_empty_loop.
  forward_if (
      PROP ( ) 
      LOCAL (temp _t'2 buf_p; temp _st sptr_p; 
             lvar __res__1 enc_rval_s v__res__1;
             lvar _unconst (Tunion __3990 noattr) v_unconst;
             lvar _effective_integer prim_type_s v_effective_integer;
             lvar _rval (Tstruct _asn_enc_rval_s noattr) v_rval; 
             temp __res res_p; temp _td td_p; 
             temp _sptr sptr_p; temp _tag_mode (Vint (Int.repr tag_mode));
             temp _tag (Vint (Int.repr tag)); 
             temp _cb cb_p; temp _app_key app_key_p)
       SEP ((* Local vars *)
            data_at_ Tsh enc_rval_s v__res__1;
            data_at_ Tsh (Tunion __3990 noattr) v_unconst;
            data_at_ Tsh prim_type_s v_effective_integer;
            data_at_ Tsh (Tstruct _asn_enc_rval_s noattr) v_rval; 
            (* type descriptor *)
            data_at_ Tsh type_descriptor_s td_p; 
            (* sptr *)
            valid_pointer buf_p;
            if Val.eq buf_p nullval
            then emp
            else data_at Tsh (tarray tuchar size) (map Vubyte data) buf_p;
            field_at Tsh prim_type_s (DOT _buf) buf_p sptr_p;
            field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p; 
            (* Result *)
            data_at_ Tsh enc_rval_s res_p;
            (* Callback *)
            data_at_ Tsh enc_key_s app_key_p;
            valid_pointer cb_p)).
  * (* st->buf <> null *)
    destruct Val.eq; 
      [unfold nullval in e; rewrite Heqbuf_p in e; simpl in e; congruence|].
    repeat forward.
    normalize.
    forward_loop (EX z : Z, 
               PROP (0 <=  z;
                     Ptrofs.unsigned buf_ofs + z <= Ptrofs.max_unsigned)
               LOCAL (temp 
                        _end1 
                        (Vptr buf_b
                              (Ptrofs.sub 
                                 (Ptrofs.add buf_ofs (Ptrofs.repr size)) (Ptrofs.repr 1))); 
                      temp _buf (Vptr buf_b (Ptrofs.add buf_ofs (Ptrofs.repr z))); 
                      temp _t'10 (Vint (Int.repr size));
                      temp _t'2 (Vptr buf_b buf_ofs); temp _st sptr_p;
                      lvar __res__1 enc_rval_s v__res__1; 
                      lvar _unconst (Tunion __3990 noattr) v_unconst;
                      lvar _effective_integer prim_type_s v_effective_integer; 
                      lvar _rval enc_rval_s v_rval; temp _tag (Vint (Int.repr tag));
                      temp __res res_p; temp _td td_p; temp _sptr sptr_p;
                      temp _tag_mode (Vint (Int.repr tag_mode));
                      temp _cb cb_p; temp _app_key app_key_p)
               SEP (data_at_ Tsh enc_rval_s v__res__1; 
                    data_at_ Tsh (Tunion __3990 noattr) v_unconst;
                    data_at_ Tsh prim_type_s v_effective_integer; 
                    data_at_ Tsh enc_rval_s v_rval;
                    data_at_ Tsh enc_rval_s res_p; data_at_ Tsh type_descriptor_s td_p;
                    data_at_ Tsh enc_key_s app_key_p; valid_pointer (Vptr buf_b buf_ofs);
                    data_at Tsh (tarray tuchar size) (map Vubyte data) (Vptr buf_b buf_ofs);
                    field_at Tsh prim_type_s (DOT _buf) (Vptr buf_b buf_ofs) sptr_p;
                    field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p; 
                    valid_pointer cb_p))%assert
      continue: (EX z : Z, 
               PROP (0 <= z;
                     Ptrofs.unsigned buf_ofs + z + 1 <= Ptrofs.max_unsigned)
               LOCAL (temp 
                        _end1 
                        (Vptr buf_b
                              (Ptrofs.sub 
                                 (Ptrofs.add buf_ofs (Ptrofs.repr size)) (Ptrofs.repr 1))); 
                      temp _t'10 (Vint (Int.repr size));
                      temp _buf (Vptr buf_b (Ptrofs.add buf_ofs (Ptrofs.repr z))); 
                      temp _t'2 (Vptr buf_b buf_ofs); temp _st sptr_p;
                      lvar __res__1 enc_rval_s v__res__1; 
                      lvar _unconst (Tunion __3990 noattr) v_unconst;
                      lvar _effective_integer prim_type_s v_effective_integer; 
                      lvar _rval enc_rval_s v_rval; temp _tag (Vint (Int.repr tag));
                      temp __res res_p; temp _td td_p; temp _sptr sptr_p;
                      temp _tag_mode (Vint (Int.repr tag_mode));
                      temp _cb cb_p; temp _app_key app_key_p)
               SEP (data_at_ Tsh enc_rval_s v__res__1; 
                    data_at_ Tsh (Tunion __3990 noattr) v_unconst;
                    data_at_ Tsh prim_type_s v_effective_integer; 
                    data_at_ Tsh enc_rval_s v_rval;
                    data_at_ Tsh enc_rval_s res_p; data_at_ Tsh type_descriptor_s td_p;
                    data_at_ Tsh enc_key_s app_key_p; valid_pointer (Vptr buf_b buf_ofs);
                    data_at Tsh (tarray tuchar size) (map Vubyte data) (Vptr buf_b buf_ofs);
                    field_at Tsh prim_type_s (DOT _buf) (Vptr buf_b buf_ofs) sptr_p;
                    field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p; 
                    valid_pointer cb_p))%assert
      break: (EX z : Z,
              PROP ()
              LOCAL (temp 
                       _end1 
                       (Vptr buf_b
                             (Ptrofs.sub 
                                (Ptrofs.add buf_ofs (Ptrofs.repr size)) (Ptrofs.repr 1))); 
                     temp _t'10 (Vint (Int.repr size));
                     temp _buf (Vptr buf_b (Ptrofs.add buf_ofs (Ptrofs.repr z))); 
                     temp _t'2 (Vptr buf_b buf_ofs); 
                     temp _st sptr_p; lvar __res__1 enc_rval_s v__res__1; 
                     lvar _unconst (Tunion __3990 noattr) v_unconst;
                     lvar _effective_integer prim_type_s v_effective_integer; 
                     lvar _rval enc_rval_s v_rval; temp _tag (Vint (Int.repr tag));
                     temp __res res_p; temp _td td_p; temp _sptr sptr_p;
                     temp _tag_mode (Vint (Int.repr tag_mode));
                     temp _cb cb_p; temp _app_key app_key_p)
              SEP(data_at_ Tsh enc_rval_s v__res__1; 
                  data_at_ Tsh (Tunion __3990 noattr) v_unconst;
                  data_at_ Tsh prim_type_s v_effective_integer; 
                  data_at_ Tsh enc_rval_s v_rval;
                  data_at_ Tsh enc_rval_s res_p; data_at_ Tsh type_descriptor_s td_p;
                  data_at_ Tsh enc_key_s app_key_p; valid_pointer (Vptr buf_b buf_ofs);
                  data_at Tsh (tarray tuchar size) (map Vubyte data) (Vptr buf_b buf_ofs);
                  field_at Tsh prim_type_s (DOT _buf) (Vptr buf_b buf_ofs) sptr_p;
                  field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p; 
                  valid_pointer cb_p))%assert.
    - (* invariant check *)
      Exists 0.
      entailer!.
    - (* loop *)
      Intros z.
      forward_if.
      unfold test_order_ptrs, sameblock.
      destruct peq; try congruence.
      entailer!.
      admit.

      assert (Z : 0 < z + 1 < Zlength data).
      { unfold typed_true, strict_bool_val, sem_cmp_pp in H9; cbn in H9.
        destruct eq_block in H9; try congruence.
        break_match_hyp; try congruence.
        unfold force_val, Val.of_bool, Ptrofs.ltu in Heqv; cbn in Heqv.
        destruct zlt in Heqv.
        unfold Ptrofs.add in l.
        repeat rewrite ->Ptrofs.add_unsigned in l.
        replace (Ptrofs.repr 1) with Ptrofs.one in l by reflexivity.
        unfold Ptrofs.sub in l.
        replace (Ptrofs.unsigned (Ptrofs.repr z)) with z in l.
        rewrite Ptrofs.unsigned_repr in l.
        replace (Ptrofs.unsigned (Ptrofs.repr size)) with size in l.
        replace (Ptrofs.unsigned Ptrofs.one) with 1 in l by reflexivity.
        rewrite Ptrofs.unsigned_repr in l at 1.
        rewrite Ptrofs.unsigned_repr in l.
        assert (T : forall p, (p + size - 1) = (p + size + (-1))) by lia; 
          rewrite T in l; clear T.
        rewrite <-Z.add_assoc in l.
        apply Zplus_lt_reg_l with (n := z) (m := (size + -1)) 
                                    (p := Ptrofs.unsigned buf_ofs) in l.
        lia.
        rep_omega.
        rewrite Ptrofs.unsigned_repr; rep_omega.
        rewrite Ptrofs.unsigned_repr; rep_omega.
        rep_omega.
        rewrite Ptrofs.unsigned_repr. 
        reflexivity.
        rep_omega.
        unfold Vfalse in Heqv; inversion Heqv; rewrite <-H11 in H9; 
          unfold Int.eq in H9; rewrite Int.unsigned_zero in H9; cbn in H9.
        congruence. }

      assert_PROP (Vptr buf_b (Ptrofs.add buf_ofs (Ptrofs.repr z)) =
                  field_address (tarray tuchar size) (SUB z) (Vptr buf_b buf_ofs)).
      entailer!.
      assert (FA : field_compatible (tarray tuchar (Zlength data)) (SUB z) 
                                    (Vptr buf_b buf_ofs)).
      prove_field_compatible_arr.
      apply field_compatible_field_address in FA.
      rewrite FA; cbn; replace (0 + 1 * z) with z by lia; reflexivity.

      forward.
      entailer!.
      { cbn; pose proof Byte.unsigned_range_2 (Znth z data) as T; cbn in T; 
          inversion T as [T1 T2].
        pose proof unsigned_repr_le (Byte.unsigned (Znth z data)) T1.
        lia. }

      rewrite Znth_map_Vubyte by lia.
      forward_if (
          PROP ( ) 
          LOCAL (temp _t'7 (Vubyte (Znth z data)); 
                 temp _end1 (Vptr buf_b (Ptrofs.sub 
                                           (Ptrofs.add buf_ofs (Ptrofs.repr size)) 
                                           (Ptrofs.repr 1)));
                 temp _buf (Vptr buf_b (Ptrofs.add buf_ofs (Ptrofs.repr z)));
                 temp _t'10 (Vint (Int.repr size)); temp _t'2 (Vptr buf_b buf_ofs); 
                 temp _st sptr_p; lvar __res__1 enc_rval_s v__res__1;
                 lvar _unconst (Tunion __3990 noattr) v_unconst;
                 lvar _effective_integer prim_type_s v_effective_integer; 
                 lvar _rval enc_rval_s v_rval;
                 temp _tag (Vint (Int.repr tag)); temp __res res_p; temp _td td_p; 
                 temp _sptr sptr_p; temp _tag_mode (Vint (Int.repr tag_mode)); 
                 temp _cb cb_p; temp _app_key app_key_p)
          SEP (data_at_ Tsh enc_rval_s v__res__1; 
               data_at_ Tsh (Tunion __3990 noattr) v_unconst; 
               data_at_ Tsh prim_type_s v_effective_integer; 
               data_at_ Tsh enc_rval_s v_rval; 
               data_at_ Tsh enc_rval_s res_p; data_at_ Tsh type_descriptor_s td_p; 
               data_at_ Tsh enc_key_s app_key_p; valid_pointer (Vptr buf_b buf_ofs); 
               data_at Tsh (Tarray tuchar size noattr) (map Vubyte data) 
                       (Vptr buf_b buf_ofs); 
               field_at Tsh prim_type_s (DOT _buf) (Vptr buf_b buf_ofs) sptr_p; 
               field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p; 
               valid_pointer cb_p)).
      { (* *buf = 0 -> first switch case *)

        assert_PROP (Vptr buf_b (Ptrofs.add (Ptrofs.add buf_ofs (Ptrofs.repr z)) 
                                            (Ptrofs.mul (Ptrofs.repr 1) 
                                                        (Ptrofs.of_ints (Int.repr 1)))) =
                     field_address (tarray tuchar size) (SUB (z + 1)) (Vptr buf_b buf_ofs)).
        entailer!.
        assert (FA : field_compatible (tarray tuchar (Zlength data)) (SUB (z + 1)) 
                                 (Vptr buf_b buf_ofs)).
        prove_field_compatible_arr.
        apply field_compatible_field_address in FA.
        rewrite FA; cbn; replace (0 + 1 * (z + 1)) with (z + 1) by lia; reflexivity.

        forward.
        entailer!.
        { cbn; pose proof Byte.unsigned_range_2 (Znth (z + 1) data) as T; cbn in T; 
            inversion T as [T1 T2].
          pose proof unsigned_repr_le (Byte.unsigned (Znth (z + 1) data)) T1.
          lia. }

        forward_if.
        + (* buf[1] & 0x80 = 0 -> continue *) 
          forward.
          Exists z.
          entailer!.
        + (* buf[1] & 0x80 <> 0 -> break *)
          forward.
          entailer!.
      }
      { (* *buf = 255 -> second switch case *)

        assert_PROP (Vptr buf_b (Ptrofs.add (Ptrofs.add buf_ofs (Ptrofs.repr z)) 
                                            (Ptrofs.mul (Ptrofs.repr 1) 
                                                        (Ptrofs.of_ints (Int.repr 1)))) =
                     field_address (tarray tuchar size) (SUB (z + 1)) (Vptr buf_b buf_ofs)).
        entailer!.
        assert (FA : field_compatible (tarray tuchar (Zlength data)) (SUB (z + 1)) 
                                 (Vptr buf_b buf_ofs)).
        prove_field_compatible_arr.
        apply field_compatible_field_address in FA.
        rewrite FA; cbn; replace (0 + 1 * (z + 1)) with (z + 1) by lia; reflexivity.

        forward.
        entailer!.
        { cbn; pose proof Byte.unsigned_range_2 (Znth (z + 1) data) as T; cbn in T; 
            inversion T as [T1 T2].
          pose proof unsigned_repr_le (Byte.unsigned (Znth (z + 1) data)) T1.
          lia. }

        forward_if.
        + (* buf[1] & 0x80 <> 0 -> continue *)
          forward. 
          Exists z.
          entailer!.
        + (* buf[1] & 0x80 = 0 -> break *)
          forward.
          entailer!.
      }
      { (* default case *)
        forward.
        entailer!.
      }
      { (* break after switch *)
        forward.
        Exists z.
        entailer!.
      }
      (* *buf <> 0 /\ *buf <> 255 -> default case -> break *)
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
        admit.

      + (* shift = 0 *)
        forward.
        entailer!.
    
  * (* postcondition check *)
    forward.
    entailer!.
  * (* st->buf = null *)
  
Admitted.

End Integer_der_encode.
