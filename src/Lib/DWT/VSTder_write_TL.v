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

Definition composites := composites ++ (match find_cs 
                                            dummy._dummy
                                            dummy.composites with
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

(* Callback compspecs *)
Instance Change3 : change_composite_env Dummy.CompSpecs CompSpecs.
Proof. make_cs_preserve Dummy.CompSpecs CompSpecs. Defined.

Instance Change4 : change_composite_env CompSpecs Dummy.CompSpecs.
Proof. make_cs_preserve CompSpecs Dummy.CompSpecs. Defined.

Instance Change5 : change_composite_env  VSTber_tlv_length_serialize.CompSpecs
                                         VSTber_tlv_tag_serialize.CompSpecs.
Proof. make_cs_preserve  VSTber_tlv_length_serialize.CompSpecs 
       VSTber_tlv_tag_serialize.CompSpecs. Defined.

Instance Change6: change_composite_env VSTber_tlv_tag_serialize.CompSpecs
                                       VSTber_tlv_length_serialize.CompSpecs.
Proof. make_cs_preserve VSTber_tlv_tag_serialize.CompSpecs
                        VSTber_tlv_length_serialize.CompSpecs. Defined.

Instance Change1 : change_composite_env CompSpecs  VSTber_tlv_tag_serialize.CompSpecs.
Proof. make_cs_preserve CompSpecs  VSTber_tlv_tag_serialize.CompSpecs. Defined.

Instance Change2 : change_composite_env  VSTber_tlv_tag_serialize.CompSpecs CompSpecs.
Proof. make_cs_preserve  VSTber_tlv_tag_serialize.CompSpecs CompSpecs. Defined.

Instance Change33 : change_composite_env CompSpecs  VSTber_tlv_length_serialize.CompSpecs.
Proof. make_cs_preserve CompSpecs VSTber_tlv_length_serialize.CompSpecs. Defined.

Instance Change44 : change_composite_env  VSTber_tlv_length_serialize.CompSpecs CompSpecs.
Proof. make_cs_preserve  VSTber_tlv_length_serialize.CompSpecs CompSpecs. Defined.

Open Scope Z.

Definition der_write_TL tag len size := 
  let (tl, t) := ber_tlv_tag_serialize tag (Int.repr size) in
  let (ll, l) := ber_tlv_length_serialize len (Int.repr (size - t)) in
  let ls := tl ++ ll in
  if ((t =? -1) || (t >? 32))%bool 
  then ([], -1)
  else if l =? -1 
       then (ls, -1) 
       else let s := l + t in
            if s >? 32 
            then ([], -1)
            else (tl ++ ll, s).

Lemma tag_serialize_bounds : forall t l, -1 <= snd (ber_tlv_tag_serialize t l) <= 6.
  { unfold ber_tlv_tag_serialize.
    intros.
    cbn.
    repeat break_if; autorewrite with norm; try nia. } 
Qed.

Lemma length_serialize_bounds : 
  forall t l, -1 <= snd (ber_tlv_length_serialize t l) <= 6.
  { unfold ber_tlv_length_serialize.
    intros.
    cbn.
    repeat break_if; autorewrite with norm; try nia. } 
Qed.

Definition Z_of_val v := 
  match v with
  | Vptr b i => Ptrofs.unsigned i 
  | _ => 0
  end.
  
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
    let (ls, z) := der_write_TL tag len size in
    EX buf : val,
    PROP() 
    LOCAL(temp ret_temp (Vint (Int.repr z)))
    SEP(data_at Tsh 
                (tarray tuchar 32)
                (map Vint ls ++ sublist (Zlength ls) 32
                (default_val (tarray tuchar 32))) buf;
        data_at_ Tsh enc_key_s app_key;
        valid_pointer cb).

Definition Gprog := ltac:(with_library prog [der_write_TL_spec;
                                             ber_tlv_tag_serialize_spec; 
                                             der_tlv_length_serialize_spec;
                                             dummy_callback]).


Open Scope Z.

Theorem der_write_TL_serialize_correct : 
  semax_body Vprog Gprog (normalize_function f_der_write_TL composites)
             der_write_TL_spec.
Proof.
  start_function.
  unfold MORE_COMMANDS.
  unfold abbreviate.
  forward.
  unfold POSTCONDITION.
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
      unfold POSTCONDITION.
      unfold abbreviate.
      break_let.
      repeat forward.
      Exists (Vptr b i).
      assert (ber_tlv_tag_serialize tag (Int.repr 0) = ([], -1)) as B.
      { unfold ber_tlv_tag_serialize.
        break_if;
          rewrite_if_b;
          reflexivity. }
      assert (der_write_TL tag len 0 = ([], -1)) as L.
      { generalize Heqp.
        unfold der_write_TL.
        repeat break_let.
        cbn in Z.
        subst. cbn. auto. }  
      rewrite L in *.
      inversion Heqp.
      rewrite if_true by (unfold fst; break_let; inversion B; auto).
      entailer!.
      admit.
      discriminate.
    + (* cb <> nullval *)
      pose proof (tag_serialize_req_size tag (Int.repr 32)) as TT.
      pose proof (tag_serialize_req_size 
                    len (Int.repr (32 - 
                                   snd ((ber_tlv_tag_serialize tag (Int.repr 32)))))) as LL.
      break_let.
      break_let.
      cbn in Heqp.
     pose proof (tag_serialize_bounds tag (Int.repr 32)) as TL.
     repeat forward.
     forward_call (tag, b, i, 32, 32).
     repeat split; try rep_omega.      
     assert (snd (ber_tlv_tag_serialize tag (Int.repr 32)) = z0) as MM. 
     { unfold snd; break_let. inversion Heqp0. auto. }
     rewrite MM.
     forward_if ((temp _t'3
                       (if eq_dec (Int.repr z0) (Int.repr (-1)) 
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
      * assert (z0 = -1) as Z. 
      { eapply repr_inj_signed;
          try rep_omega; auto. }
        forward_if; try discriminate.
        unfold POSTCONDITION.
        unfold abbreviate.
        break_let.
        forward.
        assert (der_write_TL tag len 32 = ([], -1)) as L.
        { unfold der_write_TL.
          repeat break_let.
          cbn in Z.
          subst. cbn. auto. }  
        Exists (Vptr b i).
        rewrite L in *.
        inversion Heqp1.
        subst. 
        break_if.
        entailer!.
       (* erewrite data_at_zero_array_eq.
        all: auto.
        entailer!.
        erewrite data_at_zero_array_eq.
        all: auto. *)
        admit.
        entailer!.
        admit.
      * assert (z0 <> -1) as Z. 
        { eapply repr_neq_e. auto. }
        forward_if.
        unfold POSTCONDITION.
        unfold abbreviate.
        break_let.
        repeat forward.
        normalize in H0.
        eapply typed_true_of_bool in H0.
        clear H1.
        unfold Int.lt in H0.
        destruct zlt; try congruence.
        do 2 rewrite Int.signed_repr in l2; try rep_omega.
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
        forward_if (temp _t'4 (Vint (Int.repr (32 - z0)))); try congruence.
        repeat forward.
        entailer!.
        discriminate.
        remember (fst (ber_tlv_tag_serialize tag (Int.repr 32))) as ls.         
        erewrite data_at_app_gen 
          with (j1 := z0)
               (j2 := 32 - z0)
               (ls1 := map Vint ls)
               (ls2 := (default_val (tarray tuchar (32 - z0))));
          (autorewrite with sublist list norm; try rep_omega; auto).
        forward_call (len, b, (i + Ptrofs.repr z0)%ptrofs, (32 - z0), (32 - z0)).
        unfold Frame.
        instantiate
          (1 := [valid_pointer cb;  data_at_ Tsh enc_key_s app_key;
          data_at Tsh (tarray tuchar z0) (map Vint ls) (Vptr b i)]). 
        unfold fold_right_sepcon.
        entailer!.
        repeat split; try rep_omega.
        1-2: ptrofs_compute_add_mul; try rep_omega.
        repeat forward.
        forward_if.
         ** 
           unfold POSTCONDITION.
           unfold abbreviate.
           
           repeat break_let. 
           repeat forward.
           Exists (Vptr b i).
           entailer!.
           replace z2 with (snd (der_write_TL tag len 32)).
           unfold der_write_TL.
           repeat break_let.
           cbn in *.
           do 2 f_equal.
           replace ((z0 =? -1) || (z0 >? 32))%bool with false.
           assert ((snd (ber_tlv_length_serialize len (Int.repr (32 - z0)))) = z1) as B.
           { unfold snd.
             break_let.
             auto.
             inversion Heqp1.
             auto. }
           assert (z1 = z3) as F.
           rewrite Heqp4 in Heqp1.
           inversion Heqp1. auto.
           pose proof (length_serialize_bounds len (Int.repr (32 - z0))) as L.
           assert (z3 = -1) as Z0. 
           { eapply repr_inj_signed;
               try rep_omega; subst; auto. }
           rewrite Z0.
           auto.
           symmetry.
           eapply orb_false_intro;
             Zbool_to_Prop; try nia.
           erewrite Z.gtb_ltb.
           Zbool_to_Prop. nia.
           unfold snd.
           break_let.
           congruence.
           remember (snd (ber_tlv_tag_serialize tag (Int.repr 32))) as z0.
           remember (fst (ber_tlv_tag_serialize tag (Int.repr 32))) as ls.
           break_if. 
           +++ 
             assert (l2 = ls ++ l1) as L0.
             { subst.
               replace l2 with (fst (der_write_TL tag len 32)).
               erewrite <- app_nil_end.
               unfold der_write_TL.
               repeat break_let.
               cbn in *.
               replace ((z0 =? -1) || (z0 >? 32))%bool with false.
               assert ((snd (ber_tlv_length_serialize len (Int.repr (32 - z0)))) = z3) as B.
               { unfold snd.
                 break_let.
                 auto.
                 inversion Heqp4.
                 auto. }
               assert (z3 = z1) as F.
               rewrite Heqp4 in Heqp1.
               inversion Heqp1. auto.
               pose proof (length_serialize_bounds len (Int.repr (32 - z0))) as L.
               assert (z3 = -1) as Z0. 
               { eapply repr_inj_signed;
                   try rep_omega; subst; auto. }
               rewrite Z0.
               cbn.
               rewrite Heqp4 in Heqp1.
               inversion Heqp1.
               erewrite <- app_nil_end.
               auto.                  
               symmetry.
               eapply orb_false_intro;
                 Zbool_to_Prop; try nia.
               erewrite Z.gtb_ltb.
               Zbool_to_Prop. nia.
               unfold fst.
               break_let.
               congruence. }
             rewrite L0.
             erewrite sepcon_comm.
             erewrite <- data_at_app_gen.
             entailer!.
             admit. 
             auto.
             {  subst; unfold default_val;
                  simpl;
                  try erewrite Zlength_list_repeat;
                  try nia; auto. } 
             nia.
             rewrite <- Heqls.
             rewrite e.
             erewrite <- app_nil_end.
             erewrite Zlength_map in *.
             erewrite H4.
             autorewrite with sublist list norm.
             f_equal.
             unfold default_val.
             simpl.
             try erewrite Zlength_list_repeat.                   
             erewrite <- sublist_list_repeat with (k := 32).
             auto.
             all: try nia.
             setoid_rewrite H4.
             unfold tarray.
             erewrite Zlength_default_val_Tarray_tuchar.
             all: rep_omega.
           +++  admit. (* wrong data_at introduced automatically *)
         ** repeat forward.
            forward_if.
            ***
              unfold POSTCONDITION.
              unfold abbreviate.
              repeat break_let.
              clear Heqp.
              forward.
              Exists (Vptr b i).
              entailer!.
              replace z2 with (snd (der_write_TL tag len 32))
                by (unfold snd; break_let; inversion Heqp2; auto).
              unfold der_write_TL.
              erewrite Heqp0.
              erewrite Heqp1.
              cbn in *.
              do 2 f_equal.
                remember (snd (ber_tlv_tag_serialize tag (Int.repr 32))) as z0.
                remember (fst (ber_tlv_tag_serialize tag (Int.repr 32))) as ls.
                replace ((z0 =? -1) || (z0 >? 32))%bool with false.
                assert ((snd (ber_tlv_length_serialize 
                                len (Int.repr (32 - z0)))) = z1) as B.
              { unfold snd.
                rewrite Heqp1. auto. }
             (* rewrite B in *. *)
              pose proof (length_serialize_bounds len (Int.repr (32 - z0))) as L.
              assert (z1 <> -1) as Z0. 
              { eapply repr_neq_e. auto. }
              replace (z1 =? -1) with false.
              replace (z1 + z0 >? 32) with true.
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
              remember (snd (ber_tlv_tag_serialize tag (Int.repr 32))) as z0.
              remember (fst (ber_tlv_tag_serialize tag (Int.repr 32))) as ls.
              break_if.
              ---
                erewrite sepcon_comm.
                erewrite <- data_at_app_gen.
                entailer!.
                admit.
                auto.
                {  subst; unfold default_val;
                  simpl;
                  try erewrite Zlength_list_repeat;
                  try nia; auto. } 
                nia.
                f_equal.
                admit.
                admit.
                setoid_rewrite H5.
             unfold tarray.
             erewrite Zlength_default_val_Tarray_tuchar.
             all: rep_omega.
              ---
                erewrite sepcon_comm.
                (* erewrite <- data_at_app_gen. *)
                admit.
            *** forward_if True; try congruence.
               -- normalize. forward_if True.
                  replace z0 with (Notations.len (map Vint ls)).
                  erewrite split_data_at_sublist_tuchar with (j := 1%Z).
                  erewrite sublist_one.
                  erewrite data_at_tuchar_singleton_array_eq.
                  Intros.
                  assert ((0 <= 0 < Notations.len ls)) by admit.
                  forward.
                  entailer!.
                  admit.
                  forward.
                  replace (Notations.len (map Vint ls)) with z0.
                  entailer!.
                  remember (snd (ber_tlv_tag_serialize tag (Int.repr 32))) as z0.
                  remember (fst (ber_tlv_tag_serialize tag (Int.repr 32))) as ls.
                  normalize.
                  1-8 : admit.
                  forward.
                  entailer!.
                  hint.
                  Intros.
                  
                  forward_call ((Vptr b i), z, app_key).
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
          break_let.
          admit. (* changes in memory from serialize tag and length *)
          ** admit. (* add lemma *)
Admitted.


