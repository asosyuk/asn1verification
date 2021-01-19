Require Import Core.Core Lib.Lib Core.StructNormalizer 
        VstLib Prim.Exec Lib.Callback.Dummy Lib.DWT.VST.Der_write_tags.
Require Import VST.floyd.proofauto.
Require Import Clight.dummy Clight.asn_codecs_prim.
Require Import VstLib Stdlib  BCT.Vst.
Require Import VST.floyd.proofauto VST.floyd.library.
Require Import  VstTactics.

Definition Vprog : varspecs. 
Proof.
  mk_varspecs prog. 
Defined.

Instance CompSpecs : compspecs. 
Proof.
  make_compspecs prog.
Defined.

Instance Change1 : change_composite_env CompSpecs BCT.Vst.CompSpecs.
Proof. make_cs_preserve CompSpecs BCT.Vst.CompSpecs. Defined.

Instance Change2 : change_composite_env  BCT.Vst.CompSpecs CompSpecs.
Proof. make_cs_preserve  BCT.Vst.CompSpecs CompSpecs. Defined.

Section Ber_decode_primitive.

(* Definition prim_enc_rval td sl buf_size li td_p sptr_p := 
  match evalErrW (primitive_encoder td sl buf_size li) [] with
  | Some v => mk_enc_rval v Vzero Vzero
  | None => mk_enc_rval (-1) td_p sptr_p
  end.

Definition prim_enc_res td  sl buf_size li := 
  match execErrW (primitive_decoder td  sl buf_size li) [] with
  | Some v => v
  | None => []
  end.  *)

Definition prim_type_s := (Tstruct _ASN__PRIMITIVE_TYPE_s noattr).
Definition mk_prim_type_s (buf_p : val) struct_len := (buf_p, Vint (Int.repr struct_len)).

Definition Z_of_val v := 
  match v with
  | Vptr b i => Ptrofs.unsigned i 
  | _ => 0
  end.

Definition ber_decode_primitive_spec : ident * funspec :=
  DECLARE _ber_decode_primitive
    WITH ctx_p : val, ctx : Z, td_p : val, td : TYPE_descriptor,
         st_pp : val, buf_p : val, buf : list Z,
         res_p : val, size : Z, tag_mode : Z, st_p : val, tags_p : val, gv : globals
    PRE [tptr asn_dec_rval_s, tptr asn_codec_ctx_s, tptr type_descriptor_s,
          tptr (tptr tvoid), tptr tvoid, tuint, tint] 
      PROP (is_pointer_or_null st_p;
            tag_mode = 0;
            0 <= size <= Int.max_signed;
            Zlength buf = size;
            isptr buf_p;
           0 < Zlength buf <= Ptrofs.max_unsigned;
           Z.land (Znth 0 buf) 32 = 0; 
           1 = Zlength (tags td) ;
           0 <= Z_of_val buf_p + Zlength buf <= Ptrofs.max_unsigned;
           Forall (fun x : Z => 0 <= x <= Byte.max_unsigned) buf)

      PARAMS (res_p; ctx_p; td_p; st_pp; buf_p; Vint (Int.repr size);
                Vint (Int.repr tag_mode))
      GLOBALS (gv)
      SEP (mem_mgr gv;
           valid_pointer st_p;
           if eq_dec st_p nullval 
           then emp
           else data_at_ Ews (Tstruct _ASN__PRIMITIVE_TYPE_s noattr) st_p ; 
           (* need ctx value for ber_check_tags *)
           data_at Tsh asn_codec_ctx_s (Vint (Int.repr ctx)) ctx_p;
           data_at Tsh (tarray tuint (Zlength (tags td)))
                  (map Vint (map Int.repr (tags td))) tags_p;
           field_at Tsh (Tstruct ber_decoder._asn_TYPE_descriptor_s noattr)
                    (DOT ber_decoder._tags) tags_p td_p ;
           field_at Tsh (Tstruct ber_decoder._asn_TYPE_descriptor_s noattr)
                   (DOT ber_decoder._tags_count)
                   (Vint (Int.repr (Zlength (tags td))))
        td_p; 
           data_at Tsh (tarray tuchar (Zlength buf)) (map Vint (map Int.repr buf)) buf_p;
           data_at Tsh (tptr tvoid) st_p st_pp;
           data_at_ Tsh asn_dec_rval_s res_p)
    POST [tvoid] 
      PROP ()
      LOCAL ()
      SEP (
        (* Unchanged *)
        (mem_mgr gv);
         valid_pointer st_p;
         data_at Tsh asn_codec_ctx_s (Vint (Int.repr ctx)) ctx_p;
         data_at Tsh (tarray tuint (Zlength (tags td)))
                  (map Vint (map Int.repr (tags td))) tags_p;
         field_at Tsh (Tstruct ber_decoder._asn_TYPE_descriptor_s noattr)
                    (DOT ber_decoder._tags) tags_p td_p ;
         field_at Tsh (Tstruct ber_decoder._asn_TYPE_descriptor_s noattr)
                   (DOT ber_decoder._tags_count)
                   (Vint (Int.repr (Zlength (tags td)))) td_p; 
         data_at Tsh (tarray tuchar (Zlength buf))
                 (map Vint (map Int.repr buf)) buf_p;
         (* Changed according to spec *)
         let RC_FAIL := 
             data_at Tsh asn_dec_rval_s (Vint (Int.repr 2), Vzero) res_p in
         EX v : val, EX s : reptype (Tstruct _ASN__PRIMITIVE_TYPE_s noattr),
             data_at Tsh (tptr tvoid) v st_pp *
             if eq_dec v nullval 
             then RC_FAIL  
             else match primitive_decoder td ctx size (sizeof tuint)
                        Int.modulus (map Byte.repr buf) with
                  | Some (r, c) => 
                    data_at Tsh asn_dec_rval_s (Vzero, Vint (Int.repr c)) res_p *
                    data_at Tsh (tarray tuint (Zlength r))
                            (map Vubyte r) (fst s) *
                    data_at Ews (Tstruct _ASN__PRIMITIVE_TYPE_s noattr) s v
                  | None =>
                    RC_FAIL * 
                    data_at_ Ews (Tstruct _ASN__PRIMITIVE_TYPE_s noattr) v 
                  end).

Definition calloc_spec_prim {cs : compspecs} :=
   WITH m : Z, n : Z, t : type
   PRE [ size_t, size_t ]
       PROP (0 <= m <= Ptrofs.max_unsigned ;
             0 <= n <= Ptrofs.max_unsigned ;
             0 <= m * n <= Ptrofs.max_unsigned;
             sizeof t = n)
       PARAMS (Vptrofs (Ptrofs.repr m); 
               Vptrofs (Ptrofs.repr n)) 
       GLOBALS()
       SEP ()
    POST [ tptr tvoid ] EX p : val, 
                        EX s : reptype (Tstruct _ASN__PRIMITIVE_TYPE_s noattr),
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (if eq_dec p nullval then emp
            else data_at Ews (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)
                         s p).

Definition Gprog := ltac:(with_library prog [(_calloc, calloc_spec_prim);
                                              (_memcpy, memcpy_spec);
                                              ber_check_tags_spec; 
                                              ber_decode_primitive_spec]).

Theorem ber_decode_primitive_correctness : semax_body Vprog Gprog 
           (normalize_function f_ber_decode_primitive composites) 
           ber_decode_primitive_spec.
Proof.
  start_function.
  rename H0 into DT.
  rename H1 into Size.
  rename H2 into Len.
  repeat forward.
  forward_if 
  (EX p : val, EX s : reptype (Tstruct _ASN__PRIMITIVE_TYPE_s noattr),
  PROP (if eq_dec st_p nullval 
        then p <> nullval 
        else (p = st_p /\ st_p <> nullval))
  LOCAL (temp _st p; 
         temp _t'19 st_p;
         lvar __res__1 (Tstruct _asn_dec_rval_s noattr) v__res__1;
         lvar _tmp_error__2 (Tstruct _asn_dec_rval_s noattr) v_tmp_error__2;
         lvar _tmp_error__1 (Tstruct _asn_dec_rval_s noattr) v_tmp_error__1;
         lvar _tmp_error (Tstruct _asn_dec_rval_s noattr) v_tmp_error;
         lvar _length tint v_length; temp __res res_p; 
         temp _opt_codec_ctx ctx_p;
         lvar _rval (Tstruct _asn_dec_rval_s noattr) v_rval;
         temp _td td_p;
         temp _buf_ptr buf_p;
         temp _size (Vint (Int.repr size));
         temp _tag_mode (Vint (Int.repr tag_mode)))
  SEP (mem_mgr gv;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v__res__1;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_tmp_error__2;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_tmp_error__1;
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_tmp_error;
       data_at_ Tsh tint v_length; 
       data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval;
       valid_pointer st_p;
       data_at Tsh asn_codec_ctx_s (Vint (Int.repr ctx)) ctx_p;
       data_at Tsh (tarray tuint (Zlength (tags td)))
                  (map Vint (map Int.repr (tags td))) tags_p;
       field_at Tsh (Tstruct ber_decoder._asn_TYPE_descriptor_s noattr)
                (DOT ber_decoder._tags) tags_p td_p ;
       field_at Tsh (Tstruct ber_decoder._asn_TYPE_descriptor_s noattr)
                   (DOT ber_decoder._tags_count)
                   (Vint (Int.repr (Zlength (tags td)))) td_p; 
       data_at Tsh (tarray tuchar (Zlength buf))
               (map Vint (map Int.repr buf)) buf_p;
       data_at Tsh (tptr tvoid) p st_pp;
       data_at_ Tsh asn_dec_rval_s res_p;
       if eq_dec st_p nullval 
       then data_at Ews (Tstruct _ASN__PRIMITIVE_TYPE_s noattr) s p 
       else data_at_ Ews (Tstruct _ASN__PRIMITIVE_TYPE_s noattr) st_p
       ))%assert; try congruence.
  *  (* _st = NULL *)   
    forward_call (1, sizeof (Tstruct _ASN__PRIMITIVE_TYPE_s noattr),
                  (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)).
    cbn; try nia.
    Intros v.
    repeat forward.
    forward_if (
     (PROP ((fst v <> nullval))
     LOCAL (temp _st (fst v); temp _t'19 st_p;
     lvar __res__1 (Tstruct _asn_dec_rval_s noattr) v__res__1;
     lvar _tmp_error__2 (Tstruct _asn_dec_rval_s noattr) v_tmp_error__2;
     lvar _tmp_error__1 (Tstruct _asn_dec_rval_s noattr) v_tmp_error__1;
     lvar _tmp_error (Tstruct _asn_dec_rval_s noattr) v_tmp_error; lvar _length tint v_length;
     lvar _rval (Tstruct _asn_dec_rval_s noattr) v_rval; temp __res res_p;
     temp _opt_codec_ctx ctx_p; temp _td td_p; temp _sptr st_pp; temp _buf_ptr buf_p;
     temp _size (Vint (Int.repr size)); temp _tag_mode (Vint (Int.repr tag_mode)))
     SEP (
     mem_mgr gv;
     if eq_dec (fst v) nullval
     then emp
     else data_at Ews (Tstruct _ASN__PRIMITIVE_TYPE_s noattr) (snd v)
                       (fst v);
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v__res__1;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_tmp_error__2;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_tmp_error__1;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_tmp_error;
     data_at Tsh tint (Vint (Int.repr 0)) v_length;
     data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_rval; valid_pointer st_p;
     if eq_dec st_p nullval then 
       emp else 
       data_at_ Ews (Tstruct _ASN__PRIMITIVE_TYPE_s noattr) st_p;
     data_at Tsh asn_codec_ctx_s (Vint (Int.repr ctx)) ctx_p;
     data_at Tsh (tarray tuint (Zlength (tags td)))
             (map Vint (map Int.repr (tags td))) tags_p;
     field_at Tsh (Tstruct ber_decoder._asn_TYPE_descriptor_s noattr)
              (DOT ber_decoder._tags) tags_p td_p ;
     field_at Tsh (Tstruct ber_decoder._asn_TYPE_descriptor_s noattr)
                   (DOT ber_decoder._tags_count)
                   (Vint (Int.repr (Zlength (tags td)))) td_p; 
     data_at Tsh (tarray tuchar (Zlength buf)) (map Vint (map Int.repr buf))
             buf_p;
     data_at Tsh (tptr tvoid) st_p st_pp; data_at_ Tsh asn_dec_rval_s res_p))). 
    break_if. erewrite e. entailer!. entailer!.
    Require Import Forward.
    match goal with
    | [ _ : _ |- semax _ ?Pre ((Sloop _ Sbreak)) _ ] =>
      forward_loop Pre 
    end. 
    entailer!.
    (* st_p = nullval *)
    -- (* malloc returned null *)
      repeat forward.
      match goal with
      | [ _ : _ |- semax _ ?Pre _ _ ] =>
        forward_loop Pre break: Pre
      end. 
      entailer!.
      forward. entailer!.
      repeat forward. 
      Exists nullval. Exists (snd v).
      repeat rewrite_if_b.
      entailer!.
    -- (* maloc returned non-null value *)
      forward.
      entailer!.
      
    -- forward.
       Exists (fst v) (snd v).
       erewrite H0 in *.
       repeat rewrite_if_b.
       entailer!.
  * (* st_p <> nullval *)
    rewrite if_false in * by assumption.
    forward.
    Exists st_p. Exists (Vundef, Vundef).
    repeat rewrite if_false by assumption.
    entailer!.
  * (* after if *)
    Intros p s.
    forward_empty_loop.
    destruct buf_p; cbn in H3; try contradiction.
    deadvars!.
    forward_call (ctx_p,
                  td_p, td, tags_p, Vzero, b, i, buf,
                  v__res__1, size, tag_mode, 0, v_length, Vzero, ctx%Z).
    Require Import Core.Tactics.
    repeat split; auto; try lia; strip_repr_ptr.
    cbn in H7.
    strip_repr.
    break_match.  
      2: { (* If ber_check_tags failed *)
        normalize.
        unfold mk_dec_rval.
        unfold asn_dec_rval_s.
        repeat forward.
        all: forward_if; [|discriminate];
          repeat forward.
        Exists p s.
        break_if.
        { rewrite if_false by assumption.
          unfold primitive_decoder.
          replace (map Int.repr (map Byte.unsigned (map Byte.repr buf)))
            with (map Int.repr buf).
          rewrite Heqo.
          destruct buf; entailer!.  
          simpl. entailer!.
          f_equal.
          (* check types byte v. int in ber_check_tags *)
          admit. }
        { admit. }
      }
      (* If ber_check_tags succeded *)
      { 
        rename Heqo into BCT; cbn in Size; subst.
        normalize.
        change_compspecs CompSpecs.
        repeat forward.
        forward_if; [congruence|].
        forward_empty_loop.
        repeat forward.
        forward_if.
        (* RW_MORE case *) admit.
        forward.
        break_if.
        * forward.
          forward_if [temp _t'2 Vfalse].
          congruence.
          forward; entailer!.
          forward_if True. 
          forward.
          match goal with
          | [ _ : _ |- semax _ ?Pre _ _ ] =>
            forward_loop Pre break: Pre
          end. 
          entailer!. congruence.
          congruence.
          forward.
          entailer!.
          forward.
          Set Ltac Backtrace.
          (* forward_call (tint, gv). *) (* FAIL *)
          admit.
        * inversion H0.
          subst.
          forward.
          forward_if [temp _t'2 Vfalse].
          congruence.
          forward; entailer!.
          forward_if True. 
          forward.
          match goal with
          | [ _ : _ |- semax _ ?Pre _ _ ] =>
            forward_loop Pre break: Pre
          end. 
          entailer!. congruence.
          congruence.
          forward.
          entailer!.
          forward.
          Set Ltac Backtrace.
          (* forward_call (tint, gv). *) (* FAIL *)
          admit. 
      } 
    



(*
        forward_empty_loop.
        cbn -[PROPx LOCALx SEPx abbreviate eq_dec nullval CompSpecs].
        rewrite data_at_isptr with (p1 := (Vptr b i)).
        normalize.
        cbn -[PROPx LOCALx SEPx abbreviate eq_dec nullval CompSpecs]. 
        forward.
        assert_PROP (offset_val 2 (Vptr b i) = 
                     field_address (tarray tuchar (Zlength buf)) 
                                   [ArraySubsc 2] (Vptr b i)).
        entailer!.
        rewrite field_address_offset;
          auto with field_compatible.
        
        forward.
        entailer!.
        simpl. normalize.
        rep_omega.
        assert (exists i, ls = [i]) as LS.
          { destruct ls; autorewrite with sublist in *.
            nia.
            exists i. destruct ls. auto.
            assert (0 <= Zlength ls) by eapply Zlength_nonneg.
            autorewrite with sublist in *.
            nia. }
        destruct LS as [i LS].  
        subst.  
        erewrite data_at_singleton_array_eq with (t := tint) (v := (Vint i));
          auto.
        Intros.
        forward.
        repeat forward.
        forward_empty_loop.
        repeat forward.
        Exists p [Vint i].
        rewrite if_false by assumption.
        entailer!.
        unfold bool_decoder; rewrite BCT; 
        destruct buf; [simpl; entailer! |
                       destruct buf; 
                       [simpl; simpl in H4; try nia |
                        destruct buf; simpl; simpl in H4; try nia]].
      assert ((Zlength (i0 :: i1 :: i2 :: buf) - 2 <? 1) = false) 
          as Z by (erewrite Z.ltb_ge; nia).
      rewrite Z.
      simpl.
      entailer!. }
  ** (* bv <> nullval *)
      pose proof Exec.ber_check_tags_bool_res td buf DT as BCT.
      inversion BCT as [T | T]; rewrite T in *;
        unfold mk_dec_rval, tag_length, tag_consumed.
      2: { (* If ber_check_tags failed *)
        normalize;
          repeat forward.
        all: forward_if; [|discriminate];
          repeat forward.
        unfold bool_decoder; rewrite T; 
          destruct buf;  entailer!. 
        simpl.
        inversion H0.
        subst.
        entailer!.
        simpl. 
        entailer!.
        Exists st_p.
        Exists [default_val tint].
        inversion H0.
        subst.
        entailer!.
         erewrite data_at_singleton_array_eq with (t := tint) (v := Vundef).
         rewrite if_false in * by assumption.
         entailer!.
         reflexivity.
        Exists st_p. 
        Exists [default_val tint].
         rewrite if_false in * by assumption.
        inversion H0.
        subst.
        entailer!.
         erewrite data_at_singleton_array_eq with (t := tint) (v := Vundef).
         entailer!.
         simpl.
         entailer!.
         reflexivity.
      }
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
      simpl. normalize.
      rep_omega.
      Intros.
      inversion H0; subst.
      repeat forward.
      forward_empty_loop.
      repeat forward.
      Exists st_p.
      Exists [Vundef].
      unfold bool_decoder; rewrite BCT; 
        destruct buf; [simpl; entailer! |
                       destruct buf; 
                       [simpl; simpl in H2; try nia |
                        destruct buf; simpl; simpl in H2; try nia]].
      assert ((Zlength (i :: i0 :: i1 :: buf) - 2 <? 1) = false) 
          as Z by (erewrite Z.ltb_ge; nia).
      rewrite Z.
      simpl.
      rewrite if_false in * by assumption.
      entailer!.  *)
Admitted.
 End Ber_decode_primitive.
