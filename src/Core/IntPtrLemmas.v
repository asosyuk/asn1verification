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

Proposition addr_lt_ge_eq : forall b m b1 b2 i1 i2 ,
    addr_ge m (b1, i1) (b2, i2) = Some b
    <-> addr_lt m (b2, i2) (b1, i1) = Some (negb b).
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

Proposition addr_lt_to_sem_cmp_lt : forall m b1 b2 i1 i2,
  addr_lt m (b1, i1) (b2, i2) = Some false ->
     (sem_cmp Clt (Vptr b1 i1) (tptr tschar)
              (Vptr b2 i2) (tptr tschar) m = Some (Val.of_bool false)).
Proof.
Admitted.

Proposition addr_lt_succ_to_sem_cmp_lt : forall m b1 b2 i1 i2,
  addr_lt m (b1,(i1 + 1)%ptrofs) (b2, i2) = Some true ->
     (sem_cmp Clt (Vptr b1 i1) (tptr tschar)
              (Vptr b2 i2) (tptr tschar) m = Some Vtrue).
Admitted.

Proposition dist_succ_to_sem_cmp_lt : forall dist m b1 b2 i1 i2,
    distance m (b1, i1) (b2, i2) = Some (S dist) ->
     (sem_cmp Clt (Vptr b1 i1) (tptr tschar)
              (Vptr b2 i2) (tptr tschar) m = Some Vtrue).
  Admitted.
