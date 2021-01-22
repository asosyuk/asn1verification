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

Require Import Core.Notations.

Definition ber_decode_primitive_spec : ident * funspec :=
  DECLARE _ber_decode_primitive
    WITH ctx_p : val, ctx : Z, td_p : val, td : TYPE_descriptor,
         st_pp : val, buf_p : val, buf : list int,
         res_p : val, size : Z, tag_mode : Z, st_p : val,
         tags_p : val, gv : globals
    PRE [tptr asn_dec_rval_s, tptr asn_codec_ctx_s, tptr type_descriptor_s,
          tptr (tptr tvoid), tptr tvoid, tuint, tint] 
      PROP (is_pointer_or_null st_p;
            tag_mode = 0;
            0 <= size <= Int.max_signed;
            Zlength buf = size;
            isptr buf_p;
           0 < Zlength buf <= Int.max_signed;
           ((Znth 0 buf) & Int.repr 32 = 0)%int; 
           1 = Zlength (tags td) ;
           0 <= Z_of_val buf_p + Zlength buf <= Ptrofs.max_unsigned;
           Forall (fun x => 0 <= Int.unsigned x <= Byte.max_unsigned) buf)

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
           data_at Tsh (tarray tuchar (Zlength buf)) (map Vint buf) buf_p;
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
                 (map Vint buf) buf_p;
         (* Changed according to spec *)
         let RC_FAIL := 
             data_at Tsh asn_dec_rval_s (Vint (Int.repr 2), Vzero) res_p in
         EX v : val, 
         EX s : reptype (Tstruct _ASN__PRIMITIVE_TYPE_s noattr),
             data_at Tsh (tptr tvoid) v st_pp *
             if eq_dec v nullval 
             then RC_FAIL  
             else 
               match primitive_decoder td ctx size (sizeof tuint)
                                       Int.max_signed buf with
               | Some (r, c) => 
                 data_at Tsh asn_dec_rval_s (Vzero, Vint (Int.repr c)) res_p *
                 data_at Tsh (tarray tuint (Zlength r))
                         (map Vint r) (fst s) *
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
  LOCAL (gvars gv;
         temp _st p; 
         temp _t'19 st_p;
         lvar __res__1 (Tstruct _asn_dec_rval_s noattr) v__res__1;
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
               (map Vint buf) buf_p;
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
     LOCAL (
      gvars gv;
       temp _st (fst v); temp _t'19 st_p;
     lvar __res__1 (Tstruct _asn_dec_rval_s noattr) v__res__1;
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
     data_at Tsh (tarray tuchar (Zlength buf)) (map Vint buf)
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
          rewrite Heqo.
          destruct buf. entailer!.  
          simpl. entailer!. } 
        { inversion H0.
          subst. rewrite_if_b.
          unfold primitive_decoder.
          rewrite Heqo.
          destruct buf. entailer!.  
          simpl. entailer!. 
        }  
      }
      { (* If ber_check_tags succeded *)
        rename Heqo into BCT; cbn in Size; subst.
        autorewrite with norm.
        Intros.
        deadvars!.
        change_compspecs CompSpecs.
        repeat forward.
        forward_if; [congruence|].
        forward_empty_loop.
        repeat forward.
        Ltac do_compute_expr_warning::=idtac.
        forward_if.
        { (* RC_FAIL case *)
          repeat forward.
          match goal with
          | [ _ : _ |- semax _ ?Pre _ _ ] =>
            forward_loop Pre break: Pre
          end. 
          entailer!.
          forward.
          entailer!.
          repeat forward.
          Exists p s.
          break_if.
          { rewrite if_false by assumption.
            unfold primitive_decoder.
            rewrite BCT.
            destruct buf. entailer!.  
            simpl. break_let. simpl. 
            replace (len (i0 :: buf) - z <? z0) with true.
            entailer!. 
            symmetry. Zbool_to_Prop.
            generalize H2.
            strip_repr.
            Require Import BCT.Exec.
            replace z with (fst (z, z0)) by auto.
            eapply ber_check_tags_primitive_bounds_fst.
            eassumption.
            (* need lemma
               Int.min_signed <= len (i0 :: buf) - z0 <= Int.max_signed
               with (z, z0) := ber_check_tags *) admit.
          } 
          { inversion H0.
            subst. rewrite_if_b.
            unfold primitive_decoder.
            rewrite BCT.
            destruct buf. entailer!.  
            simpl. break_let.
            replace (len (i0 :: buf) - z <? z0) with true.
            entailer!. 
            symmetry. Zbool_to_Prop.
            generalize H2.
            strip_repr.
            replace z with (fst (z, z0)) by auto.
            eapply ber_check_tags_primitive_bounds_fst.
            eassumption.
            (* need lemma
               Int.min_signed <= len (i0 :: buf) - z0 <= Int.max_signed
               with (z, z0) := ber_check_tags *) admit.
          }  
        }
        forward.
        break_if.
        * forward.
          forward_if [temp _t'2 Vfalse].
          congruence.
          forward; entailer!.
          forward_if True. 
          repeat forward.
          forward_empty_loop.
          repeat forward.
          forward.
          entailer!.
          forward.
          forward_call (tarray tuchar (fst p0 + 1),
                         gv). 
          strip_repr.
          (* Int.min_signed <= fst p0 + 1 <= Int.max_signed *)
          admit.
          eapply ber_check_tags_primitive_bounds_fst.
          eassumption.
          entailer!. cbn.
          do 3 f_equal. 
          erewrite Zmax0r. lia.
          (* 0 <= fst p0 + 1 *) admit.
          cbn. repeat split; auto.
          erewrite Zmax0r.  
          (* 0 <= fst p0 + 1 *) admit. admit.
           erewrite Zmax0r. admit. admit.
          Intros v.
          forward.
          forward.
          forward_if True.
          { break_if. subst. entailer!.
            entailer!. }
          ** repeat forward.
             forward_empty_loop.
             repeat forward.
             EExists. EExists.
             entailer!.
             rewrite_if_b.
             unfold primitive_decoder.
             rewrite BCT.
             destruct buf. entailer!.  
             simpl. break_let. simpl. 
             replace (len (i0 :: buf) - z <? z0) with false.
             simpl.
             entailer!.
             simpl.
             Search data_at nullval.
             (* ??? *)
             admit.
             symmetry. Zbool_to_Prop.
             generalize H2.
             strip_repr.
             Require Import BCT.Exec.
             replace z with (fst (z, z0)) by auto.
             eapply ber_check_tags_primitive_bounds_fst.
             eassumption.
             (* Int.min_signed <= len (i0 :: buf) - z0 <= Int.max_signed *)
             admit.
          ** forward.
             entailer!.
          ** repeat forward.
             autorewrite with norm.
             forward_call (Tsh, Tsh, v,
                           (Vptr b (i + Ptrofs.repr
                           (Int.unsigned (Int.repr (snd p0))))%ptrofs),
                           fst p0,
                           ((sublist (snd p0) (Zlength buf) buf))). 
             unfold Frame.
             instantiate (1 :=
                            [mem_mgr gv *
  (if eq_dec v nullval
   then emp
   else
    malloc_token Ews (tarray tuchar (fst p0 + 1)) v *
    data_at_ Ews (tarray tuchar (fst p0 + 1)) v) *
  data_at Tsh (tarray tuchar (len buf)) (map Vint buf) (Vptr b i) *
  field_at Tsh (Tstruct ber_decoder._asn_TYPE_descriptor_s noattr)
    (DOT ber_decoder._tags) tags_p td_p *
  field_at Tsh (Tstruct ber_decoder._asn_TYPE_descriptor_s noattr)
    (DOT ber_decoder._tags_count) (Vint (Int.repr (len (tags td)))) td_p *
  data_at Tsh (tarray tuint (len (tags td)))
    (map Vint (map Int.repr (tags td))) tags_p *
  data_at Tsh (Tstruct ber_decoder._asn_codec_ctx_s noattr)
    (Vint (Int.repr ctx)) ctx_p *
  data_at Tsh asn_dec_rval_s (mk_dec_rval 0 (snd p0)) v__res__1 *
  data_at Tsh tint (Vint (Int.repr (fst p0))) v_length *
  data_at_ Tsh (Tstruct _asn_dec_rval_s noattr) v_tmp_error *
  data_at Tsh (Tstruct _asn_dec_rval_s noattr)
    (Vint (Int.repr 0), Vint (Int.repr (snd p0))) v_rval * 
  valid_pointer st_p * data_at Tsh (tptr tvoid) p st_pp *
  data_at_ Tsh asn_dec_rval_s res_p *
  data_at Ews (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)
    (v, Vint (Int.repr (fst p0))) p]%logic).
             simpl.
             entailer!.
          (* TODO *)
          admit.
          cbn. 
          split. auto. split. auto.
          assert (Int.min_signed <= fst p0 <= Int.max_signed) as I.
          eapply ber_check_tags_primitive_bounds_fst.
          eassumption. strip_repr. 
          (* 0 <= fst p0 <= 4294967295 *)
          admit. 
          Intros.
          repeat forward.
          entailer!. 
          (* UNPROVABLE *) 
          admit.
          forward_empty_loop.
          repeat forward.
          EExists. EExists.
          entailer!.
          break_if.
          ++ 
          repeat rewrite_if_b.
          unfold primitive_decoder.
          rewrite BCT.
          destruct buf. entailer!.  
          admit.
          simpl. break_let. simpl. 
          replace (len (i0 :: buf) - z <? z0) with false.
          simpl.
          entailer!.
          admit.
          admit.
          ++ 
          repeat rewrite_if_b.
          unfold primitive_decoder.
          rewrite BCT.
          destruct buf. entailer!.  
          admit.
          simpl. break_let. simpl. 
          replace (len (i0 :: buf) - z <? z0) with false.
          simpl.
          entailer!.
          admit.
          admit.
        * inversion H0.
          subst.
          forward.
          forward_if [temp _t'2 Vfalse].
          congruence.
          forward; entailer!.
          forward_if True. 
          repeat forward.
          match goal with
          | [ _ : _ |- semax _ ?Pre _ _ ] =>
            forward_loop Pre break: Pre
          end. 
          entailer!. congruence.
          congruence.
          forward.
          entailer!.
          forward.
Admitted.
End Ber_decode_primitive.
