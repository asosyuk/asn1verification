Require Import Core.Core Core.StructNormalizer VstLib Stdlib
        Boolean.Exec ErrorWithWriter BCT.Vst.
Require Import VST.floyd.proofauto VST.floyd.library.
Require Import Clight.BOOLEAN.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Instance Change1 : change_composite_env CompSpecs BCT.Vst.CompSpecs.
Proof. make_cs_preserve CompSpecs BCT.Vst.CompSpecs. Defined.

Instance Change2 : change_composite_env BCT.Vst.CompSpecs CompSpecs.
Proof. make_cs_preserve BCT.Vst.CompSpecs CompSpecs. Defined.

Open Scope Z.

Section Boolean_ber_decode.

Definition bool_ber_decode_spec : ident * funspec :=
  DECLARE _BOOLEAN_decode_ber
    WITH ctx_p : val, ctx : val, td_p : val, td : TYPE_descriptor,
         bv_pp : val, buf_p : val, buf : list byte,
         res_p : val, size : Z, tag_mode : Z, bv_p : val 
    PRE [tptr asn_dec_rval_s, tptr asn_codec_ctx_s, tptr type_descriptor_s,
          tptr (tptr tvoid), tptr tvoid, tuint, tint] 
      PROP (is_pointer_or_null bv_p; decoder_type td = BOOLEAN_t; 
            (* 88 line in BOOLEAN.c, cast size of type tuint into tint *)
            0 <= size <= Int.max_signed;
            Zlength buf = size)
      PARAMS (res_p; ctx_p; td_p; bv_pp; buf_p; Vint (Int.repr size);
                Vint (Int.repr tag_mode))
      GLOBALS ()
      SEP (valid_pointer bv_p;
          (* if eq_dec bv_p nullval 
           then emp
           else data_at_ Tsh tint bv_p ; *)
           data_at Tsh asn_codec_ctx_s ctx ctx_p;
           data_at_ Tsh type_descriptor_s td_p;
           data_at Tsh (tarray tuchar (Zlength buf)) (map Vbyte buf) buf_p;
           data_at Tsh (tptr tvoid) bv_p bv_pp;
           data_at_ Tsh asn_dec_rval_s res_p)
    POST [tvoid] 
      PROP ()
      LOCAL ()
      SEP (
        (* Unchanged *)
         valid_pointer bv_p;
         data_at Tsh asn_codec_ctx_s ctx ctx_p;
         data_at_ Tsh type_descriptor_s td_p;
         data_at Tsh (tarray tuchar (Zlength buf)) (map Vbyte buf) buf_p;
         (* Changed according to spec *)
         let RC_FAIL := data_at Tsh asn_dec_rval_s (Vint (Int.repr 2), Vzero) res_p in
         if eq_dec bv_p nullval 
         then EX v : val, EX t : type, EX ls : list byte, 
                     data_at Tsh (tptr tvoid) v bv_pp *
                     if eq_dec v nullval 
                     then RC_FAIL  
                     else match bool_decoder td buf with
                           | Some (r, c) => 
                             data_at Tsh asn_dec_rval_s (Vzero, Vint (Int.repr c)) res_p *
                             data_at Tsh tschar (Val.of_bool r) v
                           | None => RC_FAIL * 
                                    malloc_token Ews t v *
                                    data_at Ews (tarray tschar 1) (map Vbyte ls) v 
                                    
      
                          end
         else data_at Tsh (tptr tvoid) bv_p bv_pp *
              match bool_decoder td buf with
                | Some (r, c) => 
                  data_at Tsh asn_dec_rval_s (Vzero, Vint (Int.repr c)) res_p *
                  data_at Tsh tschar (Val.of_bool r) bv_p 
                | None => RC_FAIL
                end).


Definition Gprog := ltac:(with_library prog [(_calloc, calloc_spec);
                                              ber_check_tags_spec; 
                                              bool_ber_decode_spec]).

Definition if_post1  bv_p v__res__1 v_tmp_error v_length v_rval 
           res_p ctx ctx_p td_p bv_pp buf buf_p size tag_mode := 
  EX p : val, EX t : type, EX ls : list byte,
  PROP (if eq_dec bv_p nullval then p <> nullval else (p = bv_p /\ bv_p <> nullval))
  LOCAL (temp _st p; 
         temp _t'11 bv_p;
         lvar __res__1 (Tstruct _asn_dec_rval_s noattr) v__res__1;
         lvar _tmp_error (Tstruct _asn_dec_rval_s noattr) v_tmp_error;
         lvar _length tint v_length; temp __res res_p; 
         temp _opt_codec_ctx ctx_p;
         lvar _rval (Tstruct _asn_dec_rval_s noattr) v_rval;
         temp _td td_p; temp _bool_value bv_pp;
         temp _buf_ptr buf_p; temp _size (Vint (Int.repr size));
         temp _tag_mode (Vint (Int.repr tag_mode)))
  SEP (data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v__res__1;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_tmp_error;
       data_at_ Tsh tint v_length; 
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval; valid_pointer bv_p;
       data_at Tsh asn_codec_ctx_s ctx ctx_p;
       data_at_ Tsh type_descriptor_s td_p;
       data_at Tsh (tarray tuchar (Zlength buf)) (map Vbyte buf) buf_p;
       data_at Tsh (tptr tvoid) p bv_pp;
       if eq_dec bv_p nullval 
       then data_at_ Tsh asn_dec_rval_s res_p * malloc_token Ews t p * 
            data_at Ews (tarray tschar 1) (map Vbyte ls) p 
       else data_at_ Tsh asn_dec_rval_s res_p 
       ).
Ltac forward_empty_loop :=
      match goal with
      | [ _ : _ |- semax _ ?Pre (Ssequence (Sloop Sskip Sbreak) _) _ ] =>
          forward_loop Pre break: Pre; try forward ; try entailer! 
      end. 

Theorem bool_der_encode : semax_body Vprog Gprog 
           (normalize_function f_BOOLEAN_decode_ber composites) 
           bool_ber_decode_spec.
Proof.
  start_function.
  rename H0 into DT.
  rename H1 into Size.
  rename H2 into Len.
  repeat forward.
  forward_if (if_post1 bv_p v__res__1 v_tmp_error v_length v_rval res_p ctx 
                       ctx_p td_p bv_pp buf buf_p size tag_mode).
  * (* _st = NULL *)
    forward_call (1, sizeof tint).
    cbn; nia.
    Intros p.
    forward.
    forward.
    forward_if.
    {
      if_tac; break_let. 
      cbn in H0; subst; entailer!.
      eapply denote_tc_test_eq_split; entailer!.
    }
    - (* malloc returned null *)
      unfold fst in *; rewrite H3.
      rewrite if_true by reflexivity.
      repeat forward.
      entailer!.
      if_tac; try congruence.
      Exists (fst (fst p)) (snd (fst p)) (snd p).
      rewrite if_true by assumption.
      entailer!.
      unfold fst.
      rewrite H3.
      entailer!.
    - (* maloc returned non-null value *)
      forward.
      unfold if_post1.
      break_let.
      Exists v.
      Exists t.
      Exists (snd p).
      rewrite if_false by assumption.
      repeat rewrite if_true by assumption.
      entailer!.
      entailer!.
      (* if_tac; try congruence.
      entailer!. *)
  * (* _st <> NULL *)
    forward.
    unfold if_post1.
    Exists bv_p (tptr tvoid) buf.
    repeat rewrite if_false by assumption.
    entailer!.
  * (* after the first if *)
    unfold if_post1.
    Intros p t ls.
    forward_empty_loop.
    forward_call (ctx_p, ctx, td_p, td, nullval, nullval, buf_p, buf,
                  v__res__1, size, tag_mode, 0, v_length, nullval, 0). 
    pose proof Exec.ber_check_tags_bool_res td buf DT as BCT.
    inversion BCT as [T | T]; rewrite T in *;
        unfold construct_dec_rval, tag_length, tag_consumed.
      2: { (* If ber_check_tags failed *)
        repeat break_if;
        normalize;
        repeat forward.
        all: forward_if; [|discriminate];
          repeat forward.
        Exists p t ls.
        rewrite if_false by assumption.
        unfold bool_decoder; rewrite T; 
          destruct buf;  entailer!. 
        simpl.
        entailer!.
        unfold bool_decoder. rewrite T.
        simpl.
        destruct buf; inversion H0; entailer!. }

      (* If ber_check_tags succeded *)
      clear BCT; rename T into BCT; cbn in Size; subst.
      normalize.
      repeat forward.
      forward_if; [congruence|].
      forward_empty_loop.
      repeat forward.
      forward_if.
      (* RW_MORE case *) admit.
      forward.
      forward_if True.
      (* if length <> 1 *)
      (* Since we're not yet working with real type_descriptors we're assuming 
         that if ber_check_tags succedes, then length = 1 *)
      congruence.

      forward; entailer!.
      (* if length = 1 *)
      cbn -[PROPx LOCALx SEPx abbreviate eq_dec nullval CompSpecs].
      rewrite data_at_isptr with (p0 := buf_p).
      normalize.
      rewrite sem_add_pi_ptr.
      2: assumption.
      2: cbn; lia.
      cbn -[PROPx LOCALx SEPx abbreviate eq_dec nullval CompSpecs].
      assert_PROP (offset_val 2 buf_p = 
                   field_address (tarray tuchar (Zlength buf)) 
                                 [ArraySubsc 2] buf_p).
      entailer!.
      rewrite field_address_offset;
      auto with field_compatible.
      forward.
      entailer!.
      admit.
      break_if.
      Intros.
      Fail forward.
Admitted.


End Boolean_ber_decode.
