Require Import StructTact.StructTactics.
Require Import Core Notations Tactics IntLemmas PtrLemmas.

Proposition addr_ge_to_sem_cmp_lt : forall b m b1 b2 i1 i2,
    addr_ge m (b1, i1) (b2, i2) = Some b ->
    sem_cmp Clt (Vptr b1 i1) (tptr tschar) (Vptr b2 i2) (tptr tschar) m = 
    Some (Val.of_bool (negb b)).
Proof.
  intros.
  eapply sem_Clt_Cge_ptr.
  eapply ptr_ge_to_sem_cmp;
    eassumption.
Qed.


Proposition distance_to_sem_cmp_lt : forall dist m b1 b2 i1 i2,
    distance m (b1, i1) (b2, i2) = Some (S dist) ->
    sem_cmp Clt (Vptr b1 i1) (tptr tschar)
            (Vptr b2 i2) (tptr tschar) m = Some Vtrue.
Proof.
  intros until i2; intro Dist.
  replace b1 with b2 in *.
  pose proof (dist_to_lt _ _ _ _ _ Dist) as LT.
  unfold distance, sem_cmp, cmp_ptr, addr_ge, ptr_ge,
  Val.cmplu_bool, Val.cmpu_bool, Ptrofs.cmpu,
  Val.cmp_different_blocks,
  classify_cmp in *.
  repeat break_match;
    try congruence; repeat destruct_andb_hyp;
      try congruence.
  all: try rewrite <- ptrofs_lt_signed_lt in LT;
    try bool_rewrite; try intuition.
  unfold sem_binarith.
  all: repeat break_match; simpl in *; try congruence.
  
  simpl in *.
  all: unfold classify_cmp in *.

  unfold distance, sem_cmp, cmp_ptr, addr_ge, ptr_ge,
  Val.cmplu_bool, Val.cmpu_bool, Ptrofs.cmpu,
  Val.cmp_different_blocks,
  classify_cmp in *.
  repeat break_match;
    try congruence; repeat destruct_andb_hyp;
      try congruence.
Qed.

Lemma dist_succ : forall m b b' ofs ofs' dist,
    distance m (b', ofs') (b, ofs) = Some (S dist) ->
    Mem.weak_valid_pointer m b' (Ptrofs.unsigned (ofs' + 1)%ptrofs) = true -> 
    distance m (b', (Ptrofs.add ofs' Ptrofs.one)) (b, ofs) = Some dist.
Proof.
  unfold distance, snd; intros.
  break_match_hyp; [| discriminate].
  break_if; subst; [| discriminate].
  inversion H; clear H.
  assert (Ptrofs.unsigned ofs' < Ptrofs.max_unsigned)%Z.
  {
    assert ((Ptrofs.unsigned ofs') < (Ptrofs.unsigned ofs))%Z.
    {
      assert ((Z.to_nat (Ptrofs.unsigned ofs') 
               < 
               Z.to_nat (Ptrofs.unsigned ofs))%nat) by lia.
      unfold Ptrofs.unsigned in *.
      destruct ofs, ofs'; simpl in *.
      pose proof (Z2Nat.inj_lt intval0 intval) as Inj.
      destruct Inj.
      all: try lia.
    }
    assert (Ptrofs.unsigned ofs <= Ptrofs.max_unsigned)%Z.
    pose proof (Ptrofs.unsigned_range_2 ofs).
    all: try lia.
  }
  replace (addr_ge m (b, ofs) (b', (ofs' + 1)%ptrofs))
    with (Some true).
  f_equal.
  enough (S (Z.to_nat (Ptrofs.unsigned (ofs')%ptrofs)) =
             Z.to_nat (Ptrofs.unsigned (ofs' + 1)%ptrofs)) by lia.
  rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr, <-Z2Nat.inj_succ.
  reflexivity.
  apply Ptrofs.unsigned_range.
  replace (Ptrofs.unsigned 1%ptrofs) with 1 by reflexivity.
  pose proof Ptrofs.unsigned_range ofs'.
  lia.

  unfold addr_ge, ptr_ge in *.
  simpl in *.
  repeat break_if; subst.
  all: try discriminate; unfold Mem.weak_valid_pointer in *.
  all: repeat destruct_andb_hyp.
  all: repeat destruct_orb_hyp.
  all: try congruence.
  all: clear - H H2 Heqo.

  all: assert (Z.to_nat (Ptrofs.unsigned ofs') + 1 <=
          Z.to_nat (Ptrofs.unsigned ofs))%nat
    by lia.
  all: unfold Ptrofs.ltu.
  all: break_if.
  all: rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr in *.
  all: replace (Ptrofs.unsigned 1%ptrofs) with 1 in * by reflexivity.
  all: replace (1)%nat with (Z.to_nat 1)%nat in H0 by reflexivity.
  all: rewrite <-Z2Nat.inj_add in H0.
  all: try rewrite <-Z2Nat.inj_le in H0.
  all: try apply Ptrofs.unsigned_range.
  all: try reflexivity.
  all: replace (Ptrofs.unsigned 1%ptrofs) with 1 by reflexivity.
  all: pose proof Ptrofs.unsigned_range ofs'.
  all: try lia.
Qed.

Proposition distance_succ_no_overflow :  forall m b b' ofs ofs' dist,
    distance m (b', ofs') (b, ofs) = Some (S dist) ->
    Ptrofs.unsigned (ofs' + 1)%ptrofs = Ptrofs.unsigned ofs' + 1.
Proof.
  intros.
  unfold distance, snd in *; intros.
  break_match_hyp; [| discriminate].
  break_if; subst; [| discriminate].
  inversion H; clear H.
  assert (Ptrofs.unsigned ofs' < Ptrofs.max_unsigned)%Z.
  {
    assert ((Ptrofs.unsigned ofs') < (Ptrofs.unsigned ofs))%Z.
    {
      assert ((Z.to_nat (Ptrofs.unsigned ofs') 
               < 
               Z.to_nat (Ptrofs.unsigned ofs))%nat) by lia.
      unfold Ptrofs.unsigned in *.
      destruct ofs, ofs'; simpl in *.
      pose proof (Z2Nat.inj_lt intval0 intval) as Inj.
      destruct Inj.
      all: try lia.
    }
    assert (Ptrofs.unsigned ofs <= Ptrofs.max_unsigned)%Z.
    pose proof (Ptrofs.unsigned_range_2 ofs).
    all: try lia.
  }
  
  all: rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr in *.
  all: replace (Ptrofs.unsigned 1%ptrofs) with 1 in * by reflexivity.
  auto.
  destruct ofs'; simpl in *.
  nia.
Qed.

Proposition distance_O : forall m b1 b2 i1 i2,
    distance m (b1,i1) (b2,i2) = Some O <->
    ((b1,i1) = (b2,i2))%ptrofs
    /\ Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i1) = true.
Proof.
  intros.
  split; unfold distance; intro.
  -  repeat break_match; try congruence.
     unfold addr_ge, ptr_ge,
     Val.cmplu_bool, Val.cmpu_bool, Ptrofs.cmpu in *.
     repeat break_match; simpl in *;
       try congruence.
     + inversion Heqo.
       assert ((Ptrofs.unsigned i1) <= (Ptrofs.unsigned i2))%Z.
       { eapply ptrofs_le_unsigned_le.
         eassumption.
       }
       erewrite <- Z2Nat.inj_sub in H.
       inversion H.
       rewrite <- Z2Nat.inj_0 in H3.
       assert (Ptrofs.unsigned i2 - Ptrofs.unsigned i1 = 0)%Z.
       { eapply Z2Nat.inj.
         all: try nia. }
       assert (i2 = i1)%ptrofs.
       assert (Ptrofs.unsigned i2 = Ptrofs.unsigned i1)%Z by nia.
       apply (ptrofs_to_unsigned_eq).
       eassumption.
       split.
       * f_equal.
         symmetry; eassumption.
         symmetry; eassumption.
       * rewrite H1. 
         destruct_andb_hyp. eassumption.
       * destruct i1; simpl; nia.
     + inversion Heqo.
       assert ((Ptrofs.unsigned i1) <= (Ptrofs.unsigned i2))%Z.
       { eapply ptrofs_le_unsigned_le.
         eassumption.
       }
       erewrite <- Z2Nat.inj_sub in H.
       inversion H.
       rewrite <- Z2Nat.inj_0 in H3.
       assert (Ptrofs.unsigned i2 - Ptrofs.unsigned i1 = 0)%Z.
       { eapply Z2Nat.inj.
         all: try nia. }
       assert (i1 = i2)%ptrofs.
       assert (Ptrofs.unsigned i1 = Ptrofs.unsigned i2)%Z by nia.
       apply (ptrofs_to_unsigned_eq).
       eassumption.
       split.
       * f_equal.
         symmetry; eassumption.
         eassumption.
       * rewrite H1. 
         destruct_andb_hyp. eassumption.
       * destruct i1; simpl; nia.
  - break_and.
    inversion H.
    rewrite <- H3.
    rewrite <- H2.
    repeat break_match.
    f_equal.
    nia.
    repeat break_match; try congruence.
    unfold addr_ge, ptr_ge,
    Val.cmplu_bool, Val.cmpu_bool, Ptrofs.cmpu,
    Ptrofs.ltu in *.
    repeat break_match; simpl in *;
      try congruence.
    all: try nia.
    
    repeat break_match; try congruence.
    unfold addr_ge, ptr_ge,
    Val.cmplu_bool, Val.cmpu_bool, Ptrofs.cmpu,
    Ptrofs.ltu in *.
    repeat break_match; simpl in *;
      try congruence.
    
    all: destruct_andb_hyp; try intuition.
    all:unfold Mem.weak_valid_pointer in *;
      congruence.
Qed.

Lemma dist_succ_load : forall dist c m b ofs b' ofs' v,
    Mem.loadv c m (Vptr b' ofs') = Some v ->
    distance m (b', ofs') (b, ofs) = Some (S dist) ->
    distance m (b', (Ptrofs.add ofs' Ptrofs.one)) (b, ofs) = Some dist.
Proof.
  intros until v;
    intros Load Dist.
  eapply loaded_is_valid in Load.
  eapply dist_succ.
  eassumption.
  unfold Mem.weak_valid_pointer.
  replace (Ptrofs.unsigned (ofs' + 1)%ptrofs - 1)%Z with
      (Ptrofs.unsigned ofs')%Z.
  rewrite Load.
  intuition.
  eapply distance_succ_no_overflow in Dist.
  rewrite Dist.
  nia.
Qed.

Proposition addr_lt_ge_eq : forall b m b1 b2 i1 i2 ,
    addr_ge m (b1, i1) (b2, i2) = Some b
    <-> addr_lt m (b1, i1) (b2, i2) = Some (negb b).
Proof.
  intros.
  unfold addr_lt.
  simpl.
  destruct b.
  * unfold option_map.
    break_match.
    destruct b.
    all: try (intuition || congruence).
    all: try congruence.
  * unfold option_map.
    break_match.
    destruct b.
    all: try (intuition || congruence).
    all: try congruence.  
Qed.

Proposition addr_lt_ge_eq' : forall b m b1 b2 i1 i2 ,
    addr_lt m (b1, i1) (b2, i2) = Some b
    <-> addr_ge m (b1, i1) (b2, i2) = Some (negb b).
Proof.
  intros.
  unfold addr_lt.
  simpl.
  destruct b.
  * unfold option_map.
    break_match.
    destruct b.
    all: try (intuition || congruence).
    all: try congruence.
  * unfold option_map.
    break_match.
    destruct b.
    all: try (intuition || congruence).
    all: try congruence.  
Qed.

Proposition addr_ge_to_ge : forall b m b1 b2 i1 i2 ,
    addr_ge m (b1, i1) (b2, i2) = Some b
    -> (i2 <=u i1)%ptrofs = b.
Proof.
  intros.
  unfold distance, sem_cmp, cmp_ptr, addr_lt, addr_ge, ptr_ge,
  Val.cmplu_bool, Val.cmpu_bool, Ptrofs.cmpu,
  Val.cmp_different_blocks,
  classify_cmp in *.
  repeat break_match;
    try congruence;
      simpl in *;
      try congruence.
Qed.

Proposition addr_lt_to_lt : forall b m b1 b2 i1 i2 ,
    addr_lt m (b1, i1) (b2, i2) = Some b
    -> (i1 <u i2)%ptrofs = b.
Proof.
  intros.
  unfold addr_lt in *.
  Locate addr_lt.
  unfold distance, sem_cmp, cmp_ptr, addr_lt, addr_ge, ptr_ge,
  Val.cmplu_bool, Val.cmpu_bool, Ptrofs.cmpu,
  Val.cmp_different_blocks,
  classify_cmp in *.
  repeat break_match;
    try congruence;
      simpl in *;
      try congruence;
      try intuition.
  unfold Ptrofs.ltu in *.
  repeat break_match;
    simpl in *;
    try congruence;
    try nia.
Qed.

Proposition addr_lt_to_sem_cmp_lt : forall b m b1 b2 i1 i2,
  addr_lt m (b1, i1) (b2, i2) = Some b ->
     (sem_cmp Clt (Vptr b1 i1) (tptr tschar)
              (Vptr b2 i2) (tptr tschar) m = Some (Val.of_bool b)).
Proof.
  intros until i2; intro Addr.
  eapply sem_Clt_Cge_ptr'.
  eapply addr_lt_ge_eq' in Addr.
   eapply ptr_ge_to_sem_cmp;
     eassumption.
Qed.

Proposition addr_lt_trans : forall m b1 b2 i1 i2,
    addr_lt m (b1, (i1 + 1)%ptrofs) (b2, i2) = Some true ->
    Ptrofs.unsigned (i1 + 1)%ptrofs = Ptrofs.unsigned i1 + 1 ->
    Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i1) = true ->
    addr_lt m (b1, i1) (b2, i2) = Some true.
Proof.
  intros until i2;
    intro Addr; intro OF;
      intro Ptr.
  unfold addr_lt, Mem.weak_valid_pointer in *.
  unfold distance, sem_cmp, cmp_ptr, addr_lt, addr_ge, ptr_ge,
  Val.cmplu_bool, Val.cmpu_bool, Ptrofs.cmpu,
  Val.cmp_different_blocks,
  classify_cmp in *.
  repeat break_match;
    try congruence;
    simpl in *;
    try congruence;
    try intuition.
  unfold Ptrofs.ltu in *.
  repeat break_match;
    simpl in *;
    try congruence;
    rewrite OF in *;
    simpl in *;
    try nia.
  repeat destruct_andb_hyp;
    repeat destruct_orb_hyp;
    try congruence.
  Qed.
  
Proposition addr_lt_succ_to_sem_cmp : forall m b1 b2 i1 i2,
    addr_lt m (b1, (i1 + 1)%ptrofs) (b2, i2) = Some true ->
    Ptrofs.unsigned (i1 + 1)%ptrofs = Ptrofs.unsigned i1 + 1 ->
    Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i1) = true ->
    (sem_cmp Clt (Vptr b1 i1) (tptr tschar)
             (Vptr b2 i2) (tptr tschar) m = Some (Val.of_bool true)).
Proof.
  intros until i2;
    intro Addr; intro OF; intro Ptr.
  eapply addr_lt_trans in Addr.
  eapply addr_lt_to_sem_cmp_lt.
  all: eassumption.
Qed.

Proposition mem_load_inj_ptr : forall m b1 b2 b3 i1 i2 i3,
    Mem.load Mptr m b1 (Ptrofs.unsigned i1) = Some (Vptr b2 i2) ->
    Mem.load Mptr m b1 (Ptrofs.unsigned i1) = Some (Vptr b3 i3) ->
    b2 = b3 /\ i2 = i3.
Proof.
  intros until i3;
    intros Mem1 Mem2.
  split; rewrite Mem1 in Mem2;
    inversion Mem2; auto.
Qed.

Lemma ptr_ge_is_valid : forall m b1 b2 i1 i2 ,
  ptr_ge m b1 b2 i1 i2 = Some false ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i1) = true.
Proof.
  unfold Mem.weak_valid_pointer.
  intros.
  unfold distance, sem_cmp, cmp_ptr, addr_ge, ptr_ge,
  Val.cmplu_bool, Val.cmpu_bool, Ptrofs.cmpu,
  Val.cmp_different_blocks,
  classify_cmp in *.
  repeat break_match;
    try congruence; repeat destruct_andb_hyp;
      try congruence;
      repeat destruct_orb_hyp;
      try congruence.
  Qed.

Lemma ptrofs_le_unsigned_le_neg : forall a b,
  (a <=u b)%ptrofs = false <->
  not (Ptrofs.unsigned a <= Ptrofs.unsigned b)%Z.
Proof.
  split; intros; unfold not; intros.
  - unfold Ptrofs.ltu in H.
    destruct zlt; [nia | intuition].
  - unfold Ptrofs.ltu.
    destruct zlt; intuition.
Qed.

