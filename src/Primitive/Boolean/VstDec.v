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
      PROP (is_pointer_or_null bv_p; decoder_type td = BOOLEAN_t)
      PARAMS (res_p; ctx_p; td_p; bv_pp; buf_p; Vint (Int.repr size);
                Vint (Int.repr tag_mode))
      GLOBALS ()
      SEP (valid_pointer bv_p;
           data_at Tsh asn_codec_ctx_s ctx ctx_p;
           data_at_ Tsh type_descriptor_s td_p;
           data_at Tsh (tarray tschar (Zlength buf)) (map Vbyte buf) buf_p;
           data_at Tsh (tptr tvoid) bv_p bv_pp;
           data_at_ Tsh asn_dec_rval_s res_p)
    POST [tvoid]
      PROP ()
      LOCAL ()
      SEP ((* Unchanged by the execution : *)
           valid_pointer bv_p;
           data_at Tsh asn_codec_ctx_s ctx ctx_p;
           data_at_ Tsh type_descriptor_s td_p;
           data_at Tsh (tarray tschar (Zlength buf)) (map Vbyte buf) buf_p;
           data_at Tsh (tptr tvoid) bv_p bv_pp;
           (* Changes according to the exec spec *)
           let RC_FAIL := 
               data_at Tsh asn_dec_rval_s (construct_dec_rval 2 0) res_p in
           if Val.eq bv_p Vnullptr 
           then RC_FAIL 
           else match bool_decoder td buf with
                | Some (r, c) => 
                  data_at Tsh asn_dec_rval_s (construct_dec_rval 0 c) res_p *
                  data_at Tsh tuchar (Val.of_bool r) bv_p 
                | None => RC_FAIL                          
                end).

Definition if_post1 bv_p v__res__1 v_tmp_error v_length v_rval 
           res_p ctx ctx_p td_p bv_pp buf buf_p size tag_mode := 
  EX is_inner : bool, EX p : val * type * list byte,
  PROP ()
  LOCAL (temp _st (if is_inner then fst (fst p) else bv_p); temp _t'11 bv_p;
         lvar __res__1 (Tstruct _asn_dec_rval_s noattr) v__res__1;
         lvar _tmp_error (Tstruct _asn_dec_rval_s noattr) v_tmp_error;
         lvar _length tint v_length; temp __res res_p; temp _opt_codec_ctx ctx_p;
         lvar _rval (Tstruct _asn_dec_rval_s noattr) v_rval;
         temp _td td_p; temp _bool_value bv_pp;
         temp _buf_ptr buf_p; temp _size (Vint (Int.repr size));
         temp _tag_mode (Vint (Int.repr tag_mode)))
  SEP (if eq_dec (fst (fst p)) nullval 
       then emp 
       else malloc_token Ews (snd (fst p)) (fst (fst p)) * 
            data_at Ews (tarray tschar 1) (map Vbyte (snd p)) (fst (fst p));
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v__res__1;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_tmp_error;
       data_at_ Tsh tint v_length; 
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval; valid_pointer bv_p;
       data_at Tsh asn_codec_ctx_s ctx ctx_p;
       data_at_ Tsh type_descriptor_s td_p;
       data_at Tsh (tarray tschar (Zlength buf)) (map Vbyte buf) buf_p;
       data_at Tsh (tptr tvoid) (if is_inner then fst (fst p) else bv_p) bv_pp;
       data_at_ Tsh asn_dec_rval_s res_p).

(*Definition loop_inv1 :=.
Definition loop_post1 :=.*)

Definition Gprog := ltac:(with_library prog [(_calloc, calloc_spec);
                                              ber_check_tags_spec; 
                                              bool_ber_decode_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog 
           (normalize_function f_BOOLEAN_decode_ber composites) 
           bool_ber_decode_spec.
Proof.
  start_function.
  unfold MORE_COMMANDS.
  unfold abbreviate.
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
    if_tac; break_let.
    - cbn in H1; subst.
      entailer!.
    - eapply denote_tc_test_eq_split; entailer!.
    - unfold fst in *; rewrite H4.
      rewrite if_true by reflexivity.
      repeat forward.
      rewrite if_true by reflexivity.
      entailer!.
    - forward.
      unfold if_post1.
      rewrite if_false by assumption.
      Exists true p.
      rewrite if_false by assumption.
      entailer!.
  * (* _st <> NULL *)
    forward.
    unfold if_post1.
    (* p belongs to inner if, since we didn't reach it, it's uninitialized *)
    Exists false (nullval, tptr tvoid, buf).
    rewrite if_true by reflexivity.
    entailer!.
  * (* after the if *)
    unfold if_post1.
    Intros is_inner p.
    forward_loop 
      (PROP ()
       LOCAL (temp _st (if is_inner then fst (fst p) else bv_p);
              lvar __res__1 (Tstruct _asn_dec_rval_s noattr) v__res__1;
              lvar _tmp_error (Tstruct _asn_dec_rval_s noattr)
                v_tmp_error; lvar _length tint v_length;
              temp __res res_p; temp _opt_codec_ctx ctx_p;
              lvar _rval (Tstruct _asn_dec_rval_s noattr) v_rval;
              temp _td td_p; temp _bool_value bv_pp;
              temp _buf_ptr buf_p; temp _size (Vint (Int.repr size));
              temp _tag_mode (Vint (Int.repr tag_mode)))
       SEP (if eq_dec (fst (fst p)) nullval
            then emp
            else malloc_token Ews (snd (fst p)) (fst (fst p)) * 
                 data_at Ews (tarray tschar 1) (map Vbyte (snd p)) 
                         (fst (fst p));
            data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v__res__1;
            data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_tmp_error;
            data_at_ Tsh tint v_length;
            data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval;
            valid_pointer bv_p; data_at Tsh asn_codec_ctx_s ctx ctx_p;
            data_at_ Tsh type_descriptor_s td_p;
            data_at Tsh (tarray tschar (Zlength buf)) 
              (map Vbyte buf) buf_p;
            data_at Tsh (tptr tvoid)
              (if is_inner then fst (fst p) else bv_p) bv_pp;
            data_at_ Tsh asn_dec_rval_s res_p)) 
      break: 
      (PROP ()
       LOCAL (temp _st (if is_inner then fst (fst p) else bv_p);
              lvar __res__1 (Tstruct _asn_dec_rval_s noattr) v__res__1;
              lvar _tmp_error (Tstruct _asn_dec_rval_s noattr)
                v_tmp_error; lvar _length tint v_length;
              temp __res res_p; temp _opt_codec_ctx ctx_p;
              lvar _rval (Tstruct _asn_dec_rval_s noattr) v_rval;
              temp _td td_p; temp _bool_value bv_pp;
              temp _buf_ptr buf_p; temp _size (Vint (Int.repr size));
              temp _tag_mode (Vint (Int.repr tag_mode)))
       SEP (if eq_dec (fst (fst p)) nullval
            then emp
            else malloc_token Ews (snd (fst p)) (fst (fst p)) * 
                 data_at Ews (tarray tschar 1) (map Vbyte (snd p)) 
                         (fst (fst p));
            data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v__res__1;
            data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_tmp_error;
            data_at_ Tsh tint v_length;
            data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval;
            valid_pointer bv_p; data_at Tsh asn_codec_ctx_s ctx ctx_p;
            data_at_ Tsh type_descriptor_s td_p;
            data_at Tsh (tarray tschar (Zlength buf)) 
              (map Vbyte buf) buf_p;
            data_at Tsh (tptr tvoid)
              (if is_inner then fst (fst p) else bv_p) bv_pp;
            data_at_ Tsh asn_dec_rval_s res_p)).
    - (* pre-condition = invariant *)
      entailer!.
    - (* invariant step to post condition *)
      forward.
      entailer!.
    - (* after the loop *)
      forward_call (ctx_p, ctx, td_p, td, nullval, nullval, buf_p, buf, v_rval, 
                    size, tag_mode, 0, v_length, 0, nullval, 0). 
      admit.
Admitted.

End Boolean_ber_decode.
