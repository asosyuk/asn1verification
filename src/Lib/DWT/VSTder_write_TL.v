Require Import Core.Core Core.VstTactics Core.StructNormalizer VstLib
        ErrorWithWriter.
Require Import Core.Tactics 
        VST.floyd.proofauto Clight.der_encoder
        Core.Notations Core.SepLemmas.
Require Import Clight.dummy Lib.Callback.Dummy ExecDer_write_TL.
Require Import VSTber_tlv_length_serialize
        VSTber_tlv_tag_serialize.
Require Import ExecBer_tlv_tag_serialize
        ExecBer_tlv_length_serialize.

Definition composites :=
  composites ++ (match find_cs dummy._dummy dummy.composites with
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

Instance Change1 : change_composite_env Callback.Dummy.CompSpecs CompSpecs.
Proof. make_cs_preserve Dummy.CompSpecs CompSpecs. Defined.

Instance Change2 : change_composite_env CompSpecs Dummy.CompSpecs.
Proof. make_cs_preserve CompSpecs Dummy.CompSpecs. Defined.

Instance Change3 : change_composite_env CompSpecs  VSTber_tlv_tag_serialize.CompSpecs.
Proof. make_cs_preserve CompSpecs  VSTber_tlv_tag_serialize.CompSpecs. Defined.

Instance Change4 : change_composite_env  VSTber_tlv_tag_serialize.CompSpecs CompSpecs.
Proof. make_cs_preserve  VSTber_tlv_tag_serialize.CompSpecs CompSpecs. Defined.

Instance Change5 : change_composite_env CompSpecs  VSTber_tlv_length_serialize.CompSpecs.
Proof. make_cs_preserve CompSpecs VSTber_tlv_length_serialize.CompSpecs. Defined.

Instance Change6 : change_composite_env VSTber_tlv_length_serialize.CompSpecs CompSpecs.
Proof. make_cs_preserve  VSTber_tlv_length_serialize.CompSpecs CompSpecs. Defined.

Definition der_write_TL_spec : ident * funspec :=
  DECLARE _der_write_TL
  WITH gv: globals, tag : int, len : int, 
       cb : val, app_key : val, constructed : int
  PRE[tuint, tint, tptr cb_type, tptr tvoid, tint]
    PROP()
    PARAMS(Vint tag; Vint len; cb; app_key; Vint constructed)
    GLOBALS()
    SEP(func_ptr dummy_callback_spec cb;
        data_at_ Tsh enc_key_s app_key;
        valid_pointer cb)
  POST[tint]
    let size := if Val.eq cb nullval then 0 else 32 in
    let (_, z) := der_write_TL tag len size in
    PROP() 
    LOCAL(temp ret_temp (Vint (Int.repr z)))
    SEP(func_ptr dummy_callback_spec cb;
        data_at_ Tsh enc_key_s app_key;
        valid_pointer cb).

Definition Gprog := ltac:(with_library prog [der_write_TL_spec;
                                             ber_tlv_tag_serialize_spec; 
                                             der_tlv_length_serialize_spec;
                                             dummy_callback]).

Open Scope Z.

Theorem der_write_TL_serialize_correct: 
  semax_body Vprog Gprog (normalize_function f_der_write_TL composites)
             der_write_TL_spec.
Proof.
  start_function.
  pose proof (tag_serialize_bounds tag (Int.repr 32)) as BT.
  pose proof
       (length_serialize_bounds len
       (Int.repr (32 - snd ((tag_serialize tag (Int.repr 32)))))) as BL.
  forward.
  forward_if 
 (PROP (isptr v_buf;
        Z_of_val v_buf + 32 < Ptrofs.modulus)
  LOCAL (temp der_encoder._t'1 
              (if Val.eq cb nullval 
               then Vzero
               else (Vint (Int.repr (sizeof (tarray tuchar 32)))));
         temp der_encoder._size (Vint (Int.repr 0)); 
         lvar _buf (tarray tuchar 32) v_buf; 
         temp _tag (Vint tag); temp _len (Vint len);
         temp _cb cb; temp _app_key app_key;
         temp _constructed (Vint constructed))
  SEP (data_at_ Tsh (tarray tuchar 32) v_buf;
       data_at_ Tsh enc_key_s app_key; valid_pointer cb;
       func_ptr dummy_callback_spec cb)).
  - forward.
    unfold isptr in H.
    repeat break_match;
    entailer!.
    discriminate.
    edestruct HPv_buf.
    subst. cbv. auto.
  - forward.
    entailer!.
  - repeat forward.
    unfold isptr in *.
    destruct v_buf; try contradiction.
    cbn in H.
   
    break_if.
    (* cb = nullval *)
    +  destruct (tag_serialize tag (Int.repr (0))) as [tl zt] eqn : TS. 
      forward_call (tag, b, i, 0%Z, 32).
      repeat split; try rep_omega.      
      forward_if ((temp _t'3 (if eq_dec (Int.repr zt) (Int.repr (-1)) 
                    then Vint (Int.one)
                    else
           (force_val
         (sem_cast_i2bool
            (Val.of_bool
               (Int.repr 32 < Int.repr 
                                (snd (tag_serialize tag (Int.repr 0))))%int)))))). 
      1-2: repeat forward;
           entailer!;
           rewrite_if_b;
           auto;
           break_if; entailer!. 
      assert (zt = -1) as Z. 
      { generalize TS.
        unfold tag_serialize.
            break_if;
              rewrite_if_b; intro HH; inversion HH;
                auto. }
      break_if; try congruence.
      forward_if.
      unfold POSTCONDITION.
      unfold abbreviate.
      rewrite TS.
      assert (tag_serialize tag (Int.repr 0) = ([], -1)) as B.
      { unfold tag_serialize.
        break_if;
          rewrite_if_b;
          reflexivity. }
      assert (der_write_TL tag len 0 = ([], -1)) as L.
      { unfold der_write_TL.
        repeat break_let.
        inversion B.
        cbn. auto. }  
      rewrite L in *.
      rewrite_if_b.
      forward.     
      discriminate. 
    + (* cb <> nullval *)
      unfold POSTCONDITION.
      unfold abbreviate.
      destruct (der_write_TL tag len 32) as [ls z] eqn : DWT.
      assert (fst (der_write_TL tag len 32) = ls) as FDWT by
             (unfold fst; break_let; inversion DWT; auto).
      assert (snd (der_write_TL tag len 32) = z) as SDWT by
             (unfold snd; break_let; inversion DWT; auto).
      destruct (tag_serialize tag (Int.repr (32))) as [tl zt] eqn : TS. 
      destruct (length_serialize len (Int.repr (32 - zt))) as [ll zl] eqn : LS. 
      assert ((snd (length_serialize len (Int.repr (32 - zt)))) = zl) as SLS
          by (unfold snd; break_let; inversion LS; auto).
      assert ((snd (tag_serialize tag (Int.repr 32)) = zt)) as TLS
          by (unfold snd; break_let; inversion TS; auto).
      pose proof (length_serialize_bounds len (Int.repr (32 - zt))) as L.
      pose proof (tag_serialize_bounds tag (Int.repr 32)) as TL.
     repeat forward.
     forward_call (tag, b, i, 32, 32).
     repeat split; try rep_omega.             
     forward_if ((temp _t'3
                       (if eq_dec (Int.repr (snd (tag_serialize tag (Int.repr 32))))
                                            (Int.repr (-1)) 
                        then Vint (Int.one)
                        else
           (force_val
         (sem_cast_i2bool
            (Val.of_bool
               (Int.repr 32 
                < Int.repr 
                    (snd (tag_serialize tag (Int.repr 32))))%int)))))).
     1-2: repeat forward;
           entailer!;
           rewrite_if_b;
           auto;
           break_if; entailer!.      
      break_if.
      * assert ((snd (tag_serialize tag (Int.repr 32))) = -1) as Z. 
      { eapply repr_inj_signed;
          try rep_omega; auto. }
        forward_if; try discriminate.
        forward.
       assert (der_write_TL tag len 32 = ([], -1)) as K.
        { unfold der_write_TL.
          repeat break_let.
          cbn in Z.
          subst. cbn. auto. }  
        assert (tag_serialize tag (Int.repr 32) = ([], -1)) as T.
        { unfold tag_serialize.
          break_if.
          rewrite if_false.
          cbn in Z.
          subst. cbn. auto. }  

        (* Exists (Vptr b i). *)
        rewrite K in *.
        subst. 
        break_if.
        entailer!.
       (* erewrite data_at_zero_array_eq.
        all: auto.
        entailer!.
        erewrite data_at_zero_array_eq.
        all: auto. *)
        admit.
        entailer!. *)
        admit.
      * (* pose proof (length_serialize_req_size 
                    len (Int.repr (32 - 
                                   snd ((tag_serialize tag (Int.repr 32)))))) as LL. *)
        
        rewrite TLS in *.
        assert (zt <> -1) as Z. 
        { eapply repr_neq_e. auto. }
        clear n0.
        forward_if.
        repeat forward.
        normalize in H0.
        eapply typed_true_of_bool in H0.
        clear H1.
        unfold Int.lt in H0.
        destruct zlt; try congruence.
        do 2 rewrite Int.signed_repr in l; try rep_omega.
        normalize in H0.
        eapply typed_false_of_bool in H0.
        unfold Int.lt in H0.
        destruct zlt; try congruence.
        do 2 rewrite Int.signed_repr in g; try rep_omega.
        normalize.
        rewrite if_false.
        repeat forward.
        normalize.
        deadvars.
        forward_if (temp _t'4 (Vint (Int.repr (32 - zt))));
          try congruence.
        repeat forward.
        entailer!.
        discriminate.
        erewrite data_at_app_gen 
          with (j1 := zt)
               (j2 := 32 - zt)
               (ls1 := map Vint (fst (tag_serialize tag (Int.repr 32))))
               (ls2 := (default_val (tarray tuchar (32 - zt))));
          (autorewrite with sublist list norm; try rep_omega; auto).
        forward_call (len, b, (i + Ptrofs.repr zt)%ptrofs, (32 - zt), (32 - zt)).
        entailer!.
        repeat split; try rep_omega.
        1-2: ptrofs_compute_add_mul; try rep_omega.
        repeat forward.
        forward_if.
        ** assert (zl = -1) as Z0. 
           { eapply repr_inj_signed;
               try rep_omega; subst; auto. }
           assert (((zt =? -1) || (32 <? zt))%bool= false) as BC.
           { eapply orb_false_intro;
               Zbool_to_Prop; try nia. }
           repeat forward.
           (*Exists (Vptr b i). *)
           entailer!.
           unfold der_write_TL.
           erewrite TS, LS.
           remember (snd (tag_serialize tag (Int.repr 32))) as zt.
           remember (snd (length_serialize len (Int.repr (32 - zt)))) as zl. 
           do 2 f_equal.
           rewrite BC, Z0. auto.
           remember (snd (tag_serialize tag (Int.repr 32))) as zt.
           remember (snd (length_serialize len (Int.repr (32 - zt)))) as zl. 
           remember (fst (der_write_TL tag len 32)) as l.
           erewrite LS.
           break_if.
           +++ 
             assert (l = tl ++ ll) as L0.
             { erewrite e.
               erewrite <- app_nil_end.
               assert (fst (der_write_TL tag len 32) = l) as FDWT by
                     (unfold fst; break_let; inversion DWT; auto).
               erewrite <- FDWT.
               unfold der_write_TL.
               erewrite TS.
               erewrite LS.
               erewrite BC, Z0.
               cbn. rewrite e.
               erewrite <- app_nil_end.
               auto.  }
            (* rewrite L0. *)
             erewrite sepcon_comm.
             erewrite <- data_at_app_gen.
             entailer!.
             auto.
             {  subst; unfold default_val;
                  simpl;
                  try erewrite Zlength_list_repeat;
                  try nia; auto. } 
             nia.
             reflexivity.
            (* rewrite e.
             erewrite <- app_nil_end.
             erewrite Zlength_map in *.
             assert ((fst (tag_serialize tag (Int.repr 32)) = tl)) as TLS
          by (unfold fst; break_let; inversion TS; auto).
             rewrite TLS in *. *)
             f_equal. setoid_rewrite H4. 
             unfold default_val.
             simpl.
             try erewrite Zlength_list_repeat.                   
            (* erewrite <- sublist_list_repeat with (k := 32).
             auto. *)
             all: try nia.
            (* setoid_rewrite H4.
             unfold tarray.
             erewrite Zlength_default_val_Tarray_tuchar.
             all: rep_omega. *)
           +++  erewrite sepcon_comm.
                change_compspecs CompSpecs.
                erewrite <- data_at_app_gen.
                entailer!.
                auto.
                erewrite Zlength_app.
                autorewrite with sublist norm.
                admit.
                nia.
                reflexivity.
           (*     replace (fst (der_write_TL tag len 32)) 
                  with (tl ++ ll).
                assert ((fst (tag_serialize tag (Int.repr 32)) = tl)) as TLS
          by (unfold fst; break_let; inversion TS; auto).
                rewrite TLS.
                erewrite map_app.
                erewrite app_assoc.
                f_equal.
                autorewrite with sublist.
                admit. (* sublist lemmas *)
                admit. (* use der_write_TL_serialize_sum *) *)
                unfold tarray. 
                setoid_rewrite H4.
                erewrite Zlength_app.
                autorewrite with sublist.
                erewrite Zlength_sublist_correct.
                all: try rep_omega.
                admit.
                erewrite Zlength_default_val_Tarray_tuchar.
                all: rep_omega. 
         ** repeat forward.
            forward_if.
            ***
              unfold POSTCONDITION.
              unfold abbreviate.
              rewrite <- SDWT.
              unfold der_write_TL.
              erewrite TS, LS.
              forward.
              (* Exists (Vptr b i). *)
              entailer!.
              do 2 f_equal.
              remember (snd (tag_serialize tag (Int.repr 32))) as z0.
              remember (snd (length_serialize len (Int.repr (32 - z0)))) as z1.
              remember (fst (tag_serialize tag (Int.repr 32))) as ls.
              replace ((z0 =? -1) || (32 <? z0))%bool with false.
              assert (z1 <> -1) as Z0. 
              { eapply repr_neq_e. auto. }
              replace (z1 =? -1) with false.
              replace (32 <? z1 + z0) with true.
              auto.
              symmetry.
              Zbool_to_Prop; try rep_omega.
              rewrite Int.unsigned_repr in *; try rep_omega.
              symmetry.
              Zbool_to_Prop. nia.
              symmetry.
              eapply orb_false_intro;
                Zbool_to_Prop; try nia.
              break_if.
              ---
                erewrite sepcon_comm.
                erewrite <- data_at_app_gen.
                entailer!.
                auto.
                {  subst; unfold default_val;
                  simpl;
                  try erewrite Zlength_list_repeat;
                  try nia; auto. } 
                nia.
                reflexivity.
                setoid_rewrite H5.
                unfold tarray.
                erewrite Zlength_default_val_Tarray_tuchar.
                all: try rep_omega.
                admit.
              ---
                erewrite sepcon_comm.
                change_compspecs CompSpecs. 
                erewrite <- data_at_app_gen.
                entailer!.
                all: try reflexivity; auto.
               all: admit.
            *** 
              erewrite LS.
              erewrite SLS in *.
              assert (zl <> -1) as Z0. 
              { eapply repr_neq_e. auto. }
              forward_if True; try congruence.
        -- erewrite TLS in *. 
           forward_if True.
           remember ((fst (tag_serialize tag (Int.repr 32)))) as ls'.
           replace zt with (Notations.len (map Vint ls')).
           erewrite split_data_at_sublist_tuchar with (j := 1%Z).
           erewrite sublist_one with (lo := 0).
           erewrite data_at_tuchar_singleton_array_eq.
           Intros.
           assert (0 <= 0 < Notations.len ls') by admit.
           forward.
           entailer!.
           admit.
           forward.
           replace (Notations.len (map Vint ls')) with zt.
           entailer!.
           remember (snd (tag_serialize tag (Int.repr 32))) as zt.
           remember (fst (tag_serialize tag (Int.repr 32))) as ls'.
           normalize.
           1-8 : admit.
           forward.
           entailer!.
           Intros.
           eapply make_func_ptr with (id := _dummy) (gv := gv) (p := gv _dummy);
             try reflexivity.
           cbn.
           admit.
           forward_call ((Vptr b i), (zt + zl), app_key).
           cbn in BT, BL.
           rep_omega.
           forward_if.
           replace (zt + zl <? 0) with false in H4.
           cbn in H4.
           eapply typed_true_of_bool in H4.
           eapply lt_inv in H4.
           rewrite Int.signed_repr in H4.
           autorewrite with norm in H4.
           replace ( Int.signed 0%int) with 0 in * by auto with ints.
           rep_omega.
           rep_omega.
           symmetry.
           Zbool_to_Prop.
           cbn in BT, BL.
           rewrite Int.unsigned_repr in *.
           nia.
           rep_omega.          
           forward.
           entailer!.
           entailer!.
           admit.
        -- forward.
           (* Exists (Vptr b i). *)
           entailer!.
           do 2 f_equal.
           pose proof (der_write_TL_serialize_sum tag len 32) as N.
           rewrite TS, LS in N.
           erewrite N.
           all: try rep_omega; auto.
           rewrite if_false.
           erewrite sepcon_comm.
           change_compspecs CompSpecs. 
           erewrite <- data_at_app_gen.
           entailer!.
           admit.
           all: auto; try nia.
           autorewrite with sublist list norm.
           erewrite Zlength_sublist_correct.
           all: try rep_omega.
           admit.
           unfold tarray.
           erewrite Zlength_default_val_Tarray_tuchar.
           nia.
           nia.
           (* replace (fst (der_write_TL tag len 32)) 
              with (tl ++ ll).
                assert ((fst (tag_serialize tag (Int.repr 32)) = tl)) as TLS
          by (unfold fst; break_let; inversion TS; auto).
                rewrite TLS.
                erewrite map_app.
                erewrite app_assoc.
                f_equal.
                admit.
                admit. *)
                
                setoid_rewrite H5.
                erewrite Zlength_app.
                autorewrite with sublist.
                erewrite Zlength_sublist_correct.
                all: try rep_omega.
                admit.
                 {  subst; unfold default_val;
                  simpl;
                  try erewrite Zlength_list_repeat;
                  try nia; auto. } 
                 admit.
                 
                 ** admit. (* add lemma *)
Admitted.


