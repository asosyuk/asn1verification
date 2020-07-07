Require Import Core.Core Core.VstTactics Core.StructNormalizer VstLib
        ErrorWithWriter.
Require Import Core.Tactics.
               
Require Import VST.floyd.proofauto.
Require Import Clight.der_encoder.
Require Import Core.Notations Core.SepLemmas.
Require Import Clight.dummy Lib.Callback.Dummy ExecBer_tlv_tag_serialize
        ExecBer_tlv_length_serialize.
Require Import VSTber_tlv_length_serialize
        VSTber_tlv_tag_serialize.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Instance Change1 : change_composite_env CompSpecs  VSTber_tlv_tag_serialize.CompSpecs.
Proof. make_cs_preserve CompSpecs  VSTber_tlv_tag_serialize.CompSpecs. Defined.

Instance Change2 : change_composite_env  VSTber_tlv_tag_serialize.CompSpecs CompSpecs.
Proof. make_cs_preserve  VSTber_tlv_tag_serialize.CompSpecs CompSpecs. Defined.

Instance Change3 : change_composite_env CompSpecs  VSTber_tlv_length_serialize.CompSpecs.
Proof. make_cs_preserve CompSpecs VSTber_tlv_length_serialize.CompSpecs. Defined.

Instance Change4 : change_composite_env  VSTber_tlv_length_serialize.CompSpecs CompSpecs.
Proof. make_cs_preserve  VSTber_tlv_length_serialize.CompSpecs CompSpecs. Defined.

Open Scope Z.

Definition der_write_TL tag len size := 
  let (_, t) := ber_tlv_tag_serialize tag (Int.repr size) in
  let (_, l) := ber_tlv_length_serialize len (Int.repr (size - t)) in
  if ((t =? -1) || (t >? 32))%bool 
  then -1
  else if l =? -1 
       then -1 
       else let s := l + t in
            if s >? 32 
            then -1
            else s.

Lemma tag_serialize_bounds : forall t l, -1 <= snd (ber_tlv_tag_serialize t l) <= 6.
      { unfold ber_tlv_tag_serialize.
        intros.
        cbn.
        repeat break_if; autorewrite with norm; try nia. } 
Qed.

Lemma length_serialize_bounds : forall t l, -1 <= snd (ber_tlv_length_serialize t l) <= 6.
      { unfold ber_tlv_length_serialize.
        intros.
        cbn.
        repeat break_if; autorewrite with norm; try nia. } 
Qed.
  
Definition der_write_TL_spec : ident * funspec :=
  DECLARE _der_write_TL
  WITH tag : int, len : int, cb : val, app_key : val, constructed : int
  PRE[tuint, tint, tptr cb_type, tptr tvoid, tint]
    PROP()
    PARAMS(Vint tag; Vint len; cb; app_key; Vint constructed)
    GLOBALS()
    SEP(data_at_ Tsh enc_key_s app_key;
        valid_pointer cb)
  POST[tint]
    let size := if Val.eq cb nullval then 0 else 32 in
    let r := der_write_TL tag len size in
    PROP() 
    LOCAL(temp ret_temp (Vint (Int.repr r)))
    SEP(data_at_ Tsh enc_key_s app_key;
        valid_pointer cb).

Definition Gprog := ltac:(with_library prog [der_write_TL_spec;
                         ber_tlv_tag_serialize_spec; der_tlv_length_serialize_spec]).

Open Scope Z.

Definition Z_of_val v := 
  match v with
  | Vptr b i => Ptrofs.unsigned i 
  | _ => 0
  end.

Theorem der_write_TL_serialize_correct : 
  semax_body Vprog Gprog (normalize_function f_der_write_TL composites)
             der_write_TL_spec.
Proof.
  start_function.
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
       data_at_ Tsh enc_key_s app_key; valid_pointer cb)).
  - forward.
    unfold isptr in H.
    repeat break_match;
    entailer!.
    discriminate.
    edestruct HPv_buf.
    subst. cbv. auto.
  - forward.
    entailer!.
    edestruct HPv_buf.
    subst. cbv. auto.
  - repeat forward.
    unfold isptr in *.
    destruct v_buf; try contradiction.
    cbn in H.
    break_if.
    (* cb = nullval *)
    + forward_call (tag, b, i, 0%Z, 32).
      repeat split; try rep_omega.      
      remember (snd (ber_tlv_tag_serialize tag (Int.repr 0))) as z.
      forward_if ((temp _t'3 (if eq_dec (Int.repr z) (Int.repr (-1)) 
                    then Vint (Int.one)
                    else
           (force_val
         (sem_cast_i2bool
            (Val.of_bool
               (Int.repr 32 < Int.repr 
                                (snd (ber_tlv_tag_serialize tag (Int.repr 0))))%int)))))). 
      1-2: repeat forward;
           entailer!;
           rewrite_if_b;
           auto;
           break_if; entailer!. 
      assert (z = -1) as Z. 
      {  unfold ber_tlv_tag_serialize in *.
            break_if;
              rewrite_if_b; auto. }
      break_if; try congruence.
      forward_if.
      repeat forward.
      rewrite if_true.
      entailer!.
      unfold der_write_TL.
      repeat break_let.     
      cbn in Z. subst.
      do 2 f_equal.
      unfold ber_tlv_tag_serialize.
      break_if;
        rewrite_if_b;
        reflexivity.
      discriminate.
    + (* cb <> nullval *)
     pose proof (tag_serialize_bounds tag (Int.repr 32)) as TL.
     repeat forward.
     forward_call (tag, b, i, 32, 32).
     repeat split; try rep_omega.      
     remember (snd (ber_tlv_tag_serialize tag (Int.repr 32))) as z.
     forward_if ((temp _t'3 (if eq_dec (Int.repr z) (Int.repr (-1)) 
                    then Vint (Int.one)
                    else
           (force_val
         (sem_cast_i2bool
            (Val.of_bool
               (Int.repr 32 
                < Int.repr 
                    (snd (ber_tlv_tag_serialize tag (Int.repr 32))))%int)))))). 
      1-2: repeat forward;
           entailer!;
           rewrite_if_b;
           auto;
           break_if; entailer!. 
      break_if.
      * assert (z = -1) as Z. 
      { eapply repr_inj_signed;
           try rep_omega; auto. }
        forward_if; try discriminate.
        forward.
        entailer!.
        unfold der_write_TL.
        repeat break_let.     
        cbn in Z. subst.
        do 2 f_equal. 
        break_if.
        entailer!.
        admit. (* can be singleton  - fix forward_if *)
      *  assert (z <> -1) as Z. 
        { eapply repr_neq_e. auto. }
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
        forward_if (temp _t'4 (Vint (Int.repr (32 - z)))); try congruence.
        repeat forward.
        entailer!. 
        discriminate.
        remember (fst (ber_tlv_tag_serialize tag (Int.repr 32))) as ls.         
        erewrite data_at_app_gen 
          with (j1 := z)
               (j2 := 32 - z)
               (ls1 := map Vint ls)
               (ls2 := (default_val (tarray tuchar (32 - z))));
          (autorewrite with sublist list norm; try rep_omega; auto).
        forward_call (len, b, (i + Ptrofs.repr z)%ptrofs, (32 - z), (32 - z)).
        unfold Frame.
        instantiate
          (1 := [valid_pointer cb;  data_at_ Tsh enc_key_s app_key;
          data_at Tsh (tarray tuchar z) (map Vint ls) (Vptr b i)]). 
        unfold fold_right_sepcon.
        entailer!.
        repeat split; try rep_omega.
        1-2: ptrofs_compute_add_mul; try rep_omega.
        repeat forward.
        forward_if.
         ** repeat forward.
            entailer!.
            unfold der_write_TL.
            repeat break_let.
            cbn in *.
            do 2 f_equal.
            replace ((z =? -1) || (z >? 32))%bool with false.
            assert ((snd (ber_tlv_length_serialize len (Int.repr (32 - z)))) = z0) as B.
            { unfold snd.
              break_let.
              auto.
              inversion Heqp0.
              auto. }
            rewrite B in *.
            pose proof (length_serialize_bounds len (Int.repr (32 - z))) as L.
            assert (z0 = -1) as Z0. 
            { eapply repr_inj_signed;
                try rep_omega; auto. }
            rewrite Z0.
            auto.
            symmetry.
            eapply orb_false_intro;
            Zbool_to_Prop; try nia.
            erewrite Z.gtb_ltb.
            Zbool_to_Prop. nia.
            remember (snd (ber_tlv_tag_serialize tag (Int.repr 32))) as z.
            remember (fst (ber_tlv_tag_serialize tag (Int.repr 32))) as ls.
            break_let.
            break_if. 
            admit. (* fix SPE spec *)
            admit.
         ** repeat forward.
            forward_if.
            *** forward.
                entailer!.
                unfold der_write_TL.
                repeat break_let.
                cbn in *.
                do 2 f_equal.
                replace ((z =? -1) || (z >? 32))%bool with false.
                assert ((snd (ber_tlv_length_serialize len (Int.repr (32 - z)))) = z0) as B.
                { unfold snd.
                  break_let.
                  auto.
                  inversion Heqp0.
                  auto. }
                rewrite B in *.
                pose proof (length_serialize_bounds len (Int.repr (32 - z))) as L.
                assert (z0 <> -1) as Z0. 
                 { eapply repr_neq_e. auto. }
                replace (z0 =? -1) with false.
                replace (z0 + z >? 32) with true.
                auto.
                symmetry.
                erewrite Z.gtb_ltb.
                Zbool_to_Prop; try rep_omega.
                rewrite Int.unsigned_repr in *; try rep_omega.
                symmetry.
                Zbool_to_Prop. nia.
                symmetry.
                eapply orb_false_intro;
                  Zbool_to_Prop; try nia.
                erewrite Z.gtb_ltb.
                Zbool_to_Prop. nia.

                remember (snd (ber_tlv_tag_serialize tag (Int.repr 32))) as z.
                remember (fst (ber_tlv_tag_serialize tag (Int.repr 32))) as ls.
                break_let.
                break_if. 
                admit. (* fix SEP spec *)
                admit.
            *** forward_if True; try congruence.
                -- forward_if True.
                ++
                (* store - add to spec *)
                admit.
                ++
                forward.
                entailer!.
                ++ 
                (* forward call *)
                admit.
                --
                forward.
                entailer!.
                do 2 f_equal.
                admit. (* spec proof *)
                admit. (* changes in memory from serialize tag and length *)
     ** admit. (* add lemma *)
Admitted.


