Require Import Core.Core Lib.Lib Core.StructNormalizer 
        VstLib Int.Exec Lib.Callback.Dummy Lib.DWT.Vst.
Require Import VST.floyd.proofauto.
Require Import Clight.dummy Clight.INTEGER.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Section Integer_der_encode.

Theorem split3_data_at_Tarray_tuchar : forall (sh : Share.t) (n n1 : Z) 
                                         (v : list val) (p : val), 
    0 < n1 ->
    n1 + 1 <= n <= Zlength v -> 
    Zlength v = n -> 
    data_at sh (Tarray tuchar n noattr) v p = 
    (data_at sh (Tarray tuchar (n1 - 1) noattr) (sublist 0 (n1 - 1) v) p *
     data_at sh (Tarray tuchar 1 noattr) (sublist (n1 - 1) n1 v) 
             (field_address0 (Tarray tuchar n1 noattr) (SUB (n1 -1)) p) *
     data_at sh (Tarray tuchar 1 noattr) (sublist n1 (n1 + 1) v) 
             (field_address0 (Tarray tuchar n noattr) (SUB n1) p) *
     data_at sh (Tarray tuchar (n - (n1 + 1)) noattr) (sublist (n1 + 1) n v) 
             (field_address0 (Tarray tuchar n noattr) (SUB (n1 + 1)) p))%logic.
Proof.
  intros. 
  erewrite split3_data_at_Tarray with (n2 := n1) 
                                      (n3 := n1 + 1)
                                      (t := tuchar)
                                      (v' := v); auto.
  erewrite split2_data_at_Tarray_tuchar with (n2 := (n1 - 1)); auto.
  repeat rewrite sublist_sublist0.
  autorewrite with sublist.
  reflexivity.
  all: try lia.
  rewrite Zlength_sublist; lia.
  cbn; auto.
  rewrite sublist_same; try reflexivity; symmetry; assumption.
Qed.
  

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
           else data_at Tsh (tarray tuchar size) 
                        (map Vubyte (int_enc_res td data)) (Vptr buf_b buf_ofs);
           data_at Tsh prim_type_s (mk_prim_type_s (Vptr buf_b buf_ofs) size) sptr_p;
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
    rewrite Heqbuf_p in *.
    repeat forward.
    normalize.
    forward_loop (EX z : Z, 
               PROP (0 < z + 1 < Zlength data)
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
               PROP (0 < z + 1 < Zlength data)
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
      break: (PROP ()
              LOCAL (temp 
                       _end1 
                       (Vptr buf_b
                             (Ptrofs.sub 
                                (Ptrofs.add buf_ofs (Ptrofs.repr size)) (Ptrofs.repr 1))); 
                     temp _t'10 (Vint (Int.repr size));
                     temp _buf (Vptr buf_b buf_ofs); temp _t'2 (Vptr buf_b buf_ofs); 
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
                  valid_pointer cb_p)).
    - (* invariant check *)
      Exists 0.
      entailer!.
    - (* loop *)
      Intros z.
      forward_if.
      unfold test_order_ptrs.
      admit.
      unfold tarray.
      rewrite split3_data_at_Tarray_tuchar with (n1 := z + 1) 
                                                (p := (Vptr buf_b buf_ofs));
          [|lia | rewrite H1; rewrite Zlength_map; lia | 
           rewrite Zlength_map; symmetry; assumption].
      fold_types.
      normalize.
      replace (z + 1 - 1) with z by lia.
      repeat rewrite sublist_len_1 by (rewrite Zlength_map; lia).
      assert (field_address0 (tarray tuchar (z + 1)) 
                             (SUB z) (Vptr buf_b buf_ofs) =
              offset_val z (Vptr buf_b buf_ofs)). 
      { assert (field_compatible0 (tarray tuchar (z + 1)) (SUB z) (Vptr buf_b buf_ofs)).
        { unfold field_compatible0. 
          repeat split; [idtac | 
                         constructor 2; econstructor 1; cbn | 
                         lia | 
                         lia ]. 
          cbn.
          rewrite Zmax0r by lia.
          unfold Ptrofs.modulus, two_power_nat; cbn; 
            unfold Ptrofs.max_unsigned, Ptrofs.modulus, two_power_nat in H6; cbn in H6; 
              lia.
          reflexivity. 
          cbn; unfold Z.divide; exists (Ptrofs.unsigned buf_ofs + i); lia.
        }
        rewrite field_compatible0_field_address0 by assumption.
        cbn; replace (0 + 1 * z) with z by lia; reflexivity.
      }
      rewrite H9; rewrite data_at_tuchar_singleton_array_eq with 
                      (p := offset_val z (Vptr buf_b buf_ofs)).
      forward.
      entailer!.
      {
        cbn; pose proof Byte.unsigned_range_2 (Znth z data); cbn in H1; inversion H1.
        pose proof unsigned_repr_le (Byte.unsigned (Znth z data)) H31.
        lia.
      }
      autorewrite with sublist norm.
      forward_if (
          PROP ( ) 
          LOCAL (temp _t'7 (Vbyte (Znth z data)); 
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
          SEP (data_at Tsh (tarray tuchar z) (sublist 0 z (map Vbyte data)) 
                       (Vptr buf_b buf_ofs);
               data_at Tsh tuchar (Vbyte (Znth z data)) (offset_val z (Vptr buf_b buf_ofs));
               data_at Tsh (tarray tuchar 1) (sublist (z + 1) (z + 1 + 1) (map Vbyte data))
                       (field_address0 (tarray tuchar size) (SUB (z + 1)) 
                                       (Vptr buf_b buf_ofs));
               data_at Tsh (tarray tuchar (size - (z + 1 + 1)))
                       (sublist (z + 1 + 1) size (map Vbyte data))
                       (field_address0 (tarray tuchar size) (SUB (z + 1 + 1)) 
                                       (Vptr buf_b buf_ofs));
               data_at_ Tsh enc_rval_s v__res__1; 
               data_at_ Tsh (Tunion __3990 noattr) v_unconst;
               data_at_ Tsh prim_type_s v_effective_integer; data_at_ Tsh enc_rval_s v_rval;
               data_at_ Tsh enc_rval_s res_p; data_at_ Tsh type_descriptor_s td_p;
               data_at_ Tsh enc_key_s app_key_p; valid_pointer (Vptr buf_b buf_ofs);
               field_at Tsh prim_type_s (DOT _buf) (Vptr buf_b buf_ofs) sptr_p;
               field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p; 
               valid_pointer cb_p)).

      {
        assert (field_compatible0 (tarray tuchar size) (SUB (z + 1)) (Vptr buf_b buf_ofs)).
        { unfold field_compatible0. 
          repeat split; [idtac | 
                         constructor 2; econstructor 1; cbn | 
                         lia | 
                         lia ]. 
          cbn.
          rewrite Zmax0r by lia.
          unfold Ptrofs.modulus, two_power_nat; cbn; 
            unfold Ptrofs.max_unsigned, Ptrofs.modulus, two_power_nat in H6; cbn in H6; 
              lia.
          reflexivity. 
          cbn; unfold Z.divide; exists (Ptrofs.unsigned buf_ofs + i); lia.
        }
        assert (field_compatible (tarray tuchar size) (SUB (z + 1)) (Vptr buf_b buf_ofs)).
        { unfold field_compatible. 
          repeat split; [idtac | 
                         constructor 2; econstructor 1; cbn | 
                         lia | 
                         lia ]. 
          cbn.
          rewrite Zmax0r by lia.
          unfold Ptrofs.modulus, two_power_nat; cbn; 
            unfold Ptrofs.max_unsigned, Ptrofs.modulus, two_power_nat in H6; cbn in H6; 
              lia.
          reflexivity. 
          cbn; unfold Z.divide; exists (Ptrofs.unsigned buf_ofs + i); lia.
        }
        assert (field_address0 (tarray tuchar (size)) 
                               (SUB (z + 1)) (Vptr buf_b buf_ofs) =
                offset_val (nested_field_offset (tarray tuchar size) (SUB (z + 1))) 
                           (Vptr buf_b buf_ofs)). 
        rewrite field_compatible0_field_address0 by assumption.
        cbn; replace (0 + 1 * (z + 1)) with (z + 1) by lia; reflexivity.
        rewrite H12.

        rewrite <-field_address_offset in H12 by assumption.
        rewrite data_at_tuchar_singleton_array_eq with (v := Vubyte (Znth (z + 1) data)).

        assert_PROP (Vptr buf_b (Ptrofs.add (Ptrofs.add buf_ofs (Ptrofs.repr z)) 
                                            (Ptrofs.mul (Ptrofs.repr 1) 
                                                        (Ptrofs.of_ints (Int.repr 1)))) =
                     field_address (tarray tuchar size) (SUB (z + 1)) 
                                    (Vptr buf_b buf_ofs)).
        entailer!.
        rewrite <-H12.
        rewrite field_address_offset in H12 by assumption.
        rewrite H12.
        cbn.
        replace (0 + 1 * (z + 1)) with (z + 1) by lia.
        reflexivity.
        subst.
        replace (offset_val (nested_field_offset (tarray tuchar (Zlength data)) (SUB (z + 1)))
          (Vptr buf_b buf_ofs)) with (Vptr buf_b
          (Ptrofs.add (Ptrofs.add buf_ofs (Ptrofs.repr z))
             (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1))))).
        forward.

        rewrite field_compatible_field_address.
        cbn.
        reflexivity.


        entailer!.
        clear - H10.
        unfold field_address.
        rewrite data_at_tuchar_singleton_array_eq with 
            (v := Znth (z + 1) (map Vubyte data)).
        
        normalize.
        
        entailer!.

        forward.

}
      
    - (* break postcondition check *)
    
  * (* postcondition check *)
    forward.
    entailer!.
  * (* st->buf = null *)
  
Admitted.

End Integer_der_encode.
