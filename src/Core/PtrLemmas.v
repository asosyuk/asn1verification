Require Import Core Notations.
Require Import StructTact.StructTactics.

(* Address [b,ofs] *)
Definition addr : Type := (block * ptrofs).
Definition vptr (a : addr) := match a with (b,ofs) => Vptr b ofs end.
Definition load_addr (chunk : memory_chunk) (m : mem) (a : addr) :=
  match a with (b,ofs) => Mem.loadv chunk m (Vptr b ofs) end.
Definition next_addr (a : addr) := match a with (b,ofs) => (b, Ptrofs.add ofs Ptrofs.one) end.
Definition add_addr (a : addr) (i : ptrofs) := match a with (b,ofs) => (b, Ptrofs.add ofs i) end.
Notation "a ++" := (next_addr a) (at level 20).

(* Pointer comparison *)
(* Abstract spec : [b1,ofs1] >= [b2,ofs2] *)
Definition ptr_ge_spec (b1 b2 : block) (ofs1 ofs2 : ptrofs) :=
  if eq_block b1 b2 then Some (ofs2 <=u ofs1)%ptrofs else None.
(* Spec using Compcert semantic values *)
Definition ptr_ge (m : mem) (b1 b2 : block) (ofs1 ofs2 : ptrofs) :=
  if Archi.ptr64
  then Val.cmplu_bool (Mem.valid_pointer m) Cge (Vptr b1 ofs1) (Vptr b2 ofs2)
  else Val.cmpu_bool (Mem.valid_pointer m) Cge (Vptr b1 ofs1) (Vptr b2 ofs2).

Definition addr_ge (m : mem) (a1 a2 : addr) :=
  match a1, a2 with (b1, ofs1), (b2, ofs2) => ptr_ge m b1 b2 ofs1 ofs2 end.

(* Both specs can be used interchangeably *)
Proposition ptr_ge_refine : forall (m : mem) (b1 b2 : block) (ofs1 ofs2 : ptrofs),
    Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
    Mem.weak_valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
    ptr_ge_spec b1 b2 ofs1 ofs2 = ptr_ge m b1 b2 ofs1 ofs2.
Proof.
  intros.
  unfold ptr_ge.
  simpl; unfold Mem.weak_valid_pointer in *.
  destruct Archi.ptr64 eqn: A; simpl.
  all: rewrite H; rewrite H0; simpl;
    destruct (Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) &&
                                Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2)); auto.
Qed.

Proposition ptr_ge_to_sem_cmp_true : forall m b1 b2 i1 i2,
    ptr_ge m b1 b2 i1 i2 = Some true ->
    sem_cmp Cge (Vptr b1 i1) (tptr tschar) (Vptr b2 i2) (tptr tschar) m = Some Vtrue.
Proof.
  intros.
  assert ((option_map Val.of_bool (ptr_ge m b1 b2 i1 i2)) =
          (option_map Val.of_bool (Some true))) by (f_equal; assumption).
  eassumption.
Qed.

Proposition ptr_ge_to_sem_cmp_false : forall m b1 b2 i1 i2,
    ptr_ge m b1 b2 i1 i2 = Some false ->
    sem_cmp Cge (Vptr b1 i1) (tptr tschar) (Vptr b2 i2) (tptr tschar) m = Some Vfalse.
Proof.
  intros.
  assert ((option_map Val.of_bool (ptr_ge m b1 b2 i1 i2)) =
          (option_map Val.of_bool (Some false))) by (f_equal; assumption).
  eassumption.
Qed.

(* distance between addresses *)
Definition distance (a1 a2 : addr) : nat :=
  ((Z.to_nat (Ptrofs.unsigned (snd a2))) - (Z.to_nat (Ptrofs.unsigned (snd a1))))%nat.

Lemma dist_succ : forall b b' ofs ofs' dist,
    distance (b', ofs') (b, ofs) = S dist ->
    distance (b', (Ptrofs.add ofs' Ptrofs.one)) (b, ofs) = dist.
Proof.
  intros b b' ofs ofs' dist Dist.
  unfold distance, snd.
  rewrite <-Z2Nat.inj_sub by (apply Ptrofs.unsigned_range).
  assert ((distance (b', ofs') (b, ofs) = S dist) 
          <-> 
          ((distance (b', ofs') (b, ofs) - 1)%nat = dist)) by lia.
  unfold distance, snd in Dist.
  assert ( (Ptrofs.unsigned ofs') < (Ptrofs.unsigned ofs))%Z.
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
  rewrite H in Dist.
  unfold distance, snd in Dist.
  rewrite <-Z2Nat.inj_sub in Dist by (apply Ptrofs.unsigned_range).
  rewrite <-Dist.
  replace ((1)%nat) with ((Z.to_nat (1)%Z)) by reflexivity.
  rewrite <-Z2Nat.inj_sub; [| lia].
  f_equal.
  assert (Ptrofs.unsigned (Ptrofs.add ofs' Ptrofs.one) 
          = (Ptrofs.unsigned ofs' + 1)%Z); [|lia].
  replace (1%Z) with (Ptrofs.unsigned Ptrofs.one) by reflexivity.
  rewrite Ptrofs.add_unsigned.
  assert (Ptrofs.unsigned ofs' < Ptrofs.max_unsigned)%Z.
  {
    assert (Ptrofs.unsigned ofs <= Ptrofs.max_unsigned)%Z.
    pose proof (Ptrofs.unsigned_range_2 ofs).
    all: try lia.
  }
  rewrite Ptrofs.unsigned_repr.
  reflexivity.
  pose proof Ptrofs.unsigned_range ofs.
  assert (Ptrofs.unsigned ofs' + 1 <= Ptrofs.max_unsigned)%Z by lia.
  replace (Ptrofs.unsigned Ptrofs.one)%Z with (1)%Z by reflexivity.
  assert (0 <= Ptrofs.unsigned ofs')%Z 
    by (apply Ptrofs.unsigned_range).
  lia.
Qed.

Lemma if_some (c x : bool) :
    (if c then Some x else None) = Some false ->
    x = false.
Proof.
  intros; break_if; congruence.
Qed.

Lemma if_none (c : bool) :
    (if c then None else None) = Some false ->
    None = Some false.
Proof.
  intros; break_if; congruence.
Qed.

Lemma dist_pred: 
  forall (m : mem) (str_b : block) (str_ofs : ptrofs) (b : block) (i : ptrofs), 
    addr_ge m (str_b, str_ofs) (b, i) = Some false -> 
    addr_ge m ((str_b, str_ofs) ++) (b, i) = Some false -> 
    (distance (str_b, str_ofs) (b, i) - 1)%nat = 
    distance (str_b, (str_ofs + 1)%ptrofs) (b, i).
Proof.
  intros m str_b str_ofs b i Heqo0 Heqo2.
  remember (distance (str_b, str_ofs) (b, i) - 1)%nat as
      dist.
  symmetry.
  apply dist_succ.
  rewrite Heqdist.
  unfold distance; simpl.
  rewrite <-Nat.add_1_l.
  repeat replace 1%nat with (Z.to_nat 1)%Z by reflexivity.
  repeat rewrite <-Z2Nat.inj_sub;
    [| lia | apply Ptrofs.unsigned_range].
  rewrite <-Z2Nat.inj_add; [| lia |].
  f_equal; lia.
  unfold addr_ge, ptr_ge in Heqo2, Heqo0.
  simpl in Heqo2, Heqo0.
  destruct Archi.ptr64 in Heqo2, Heqo0.
  all: destruct eq_block in Heqo2, Heqo0.
  1,3: apply if_some in Heqo0.
  1,2: rewrite negb_false_iff in Heqo0.
  1,2: apply Ptrofs.ltu_inv in Heqo0.
  1,2: lia.
  all: apply if_none in Heqo2.
  all: discriminate.
Qed.

Lemma dist_to_lt : forall b b' ofs ofs' dist, 
  distance (b', ofs') (b, ofs) = S dist ->
  (Ptrofs.unsigned ofs' < Ptrofs.unsigned ofs)%Z.
Proof.
  intros;
  unfold distance in *; simpl in *.
  assert ((Z.to_nat (Ptrofs.unsigned ofs') 
             < 
             Z.to_nat (Ptrofs.unsigned ofs))%nat) by lia.
  unfold Ptrofs.unsigned in *.
  destruct ofs, ofs'; simpl in *.
  pose proof (Z2Nat.inj_lt intval0 intval) as Inj.
  destruct Inj.
  all: try lia.
Qed.  
  
Lemma dist_to_lt_or_ge : forall b b' ofs ofs' dist, 
    distance (b', ofs') (b, ofs) = dist ->
    (Ptrofs.unsigned ofs' <= Ptrofs.unsigned ofs)%Z.
Proof.
  destruct dist; intros.
  - unfold distance in *; simpl in *.
    assert ((Z.to_nat (Ptrofs.unsigned ofs) <= 
             Z.to_nat (Ptrofs.unsigned ofs'))%nat) by lia.
    unfold Ptrofs.unsigned in *.
    destruct ofs, ofs'; simpl in *.
    pose proof (Z2Nat.inj_le intval0 intval) as Inj.
    destruct Inj.
    all: try lia.
    eapply H2.
Admitted.

Lemma int_ptrofs_mod_eq : (Int.modulus = Ptrofs.modulus).
Proof.
  reflexivity.
Qed.

Hint Resolve Ptrofs.mul_one Ptrofs.add_zero int_ptrofs_mod_eq : ptrofs.
