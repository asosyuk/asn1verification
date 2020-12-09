Require Import Core Notations Tactics.

(* Address: [b,ofs] *)
Definition addr : Type := (block * ptrofs).
Definition vptr (a : addr) := match a with (b, ofs) => Vptr b ofs end.
Definition load_addr (chunk : memory_chunk) (m : mem) (a : addr) :=
  match a with (b,ofs) => Mem.loadv chunk m (Vptr b ofs) end.
Definition next_addr (a : addr) := match a with 
                                     (b, ofs) => (b, Ptrofs.add ofs Ptrofs.one) 
                                   end.
Definition add_addr (a : addr) (i : ptrofs) := 
  match a with (b, ofs) => (b, Ptrofs.add ofs i) end.
Definition store_addr (chunk : memory_chunk) (m : mem) (a : addr) :=
  match a with (b,ofs) => Mem.storev chunk m (Vptr b ofs) end.
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

Definition addr_lt (m : mem) (a1 a2 : addr) := 
  option_map negb (addr_ge m a1 a2).

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
                                Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2));
    auto.
Qed.

(*
Proposition ptr_ge_to_sem_cmp : forall b m b1 b2 i1 i2,
    ptr_ge m b1 b2 i1 i2 = Some b ->
    sem_cmp Cge  (tptr tschar)  (tptr tschar) (Vptr b1 i1) (Vptr b2 i2) = 
    Some (Val.of_bool b).
Proof.
  intros.
  assert ((option_map Val.of_bool (ptr_ge m b1 b2 i1 i2)) =
          (option_map Val.of_bool (Some b))) by (f_equal; assumption).
  cbn.
  eassumption.
Qed.

Lemma sem_Clt_Cge_ptr : forall b b1 b2 i1 i2 m,
  sem_cmp Cge (Vptr b1 i1) (tptr tschar)
          (Vptr b2 i2) (tptr tschar) m
  = Some (Val.of_bool b)
  <->
  sem_cmp Clt (Vptr b1 i1) (tptr tschar)
          (Vptr b2 i2) (tptr tschar) m = 
  Some (Val.of_bool (negb b)).
Proof.
  intros.
  unfold sem_cmp, sem_binarith, sem_cast,
         classify_cmp, classify_cast, binarith_type, cmp_ptr;
    simpl.
  all: destruct Archi.ptr64; simpl.
  all: unfold Val.of_bool.
  all: split; intros.
  all: repeat break_match.
  all: try reflexivity.
  all: try discriminate.
  all: destruct (i2 <=u i1)%ptrofs eqn: S;
    simpl in *; destruct (i1 <u i2)%ptrofs eqn: D.
  all: try intuition.
Qed.

Lemma sem_Clt_Cge_ptr' : forall b b1 b2 i1 i2 m,
  sem_cmp Cge (Vptr b1 i1) (tptr tschar)
          (Vptr b2 i2) (tptr tschar) m
  = Some (Val.of_bool (negb b))
  <->
  sem_cmp Clt (Vptr b1 i1) (tptr tschar)
          (Vptr b2 i2) (tptr tschar) m = 
  Some (Val.of_bool b).
Proof.
  intros.
  unfold sem_cmp, sem_binarith, sem_cast,
         classify_cmp, classify_cast, binarith_type, cmp_ptr;
    simpl.
  all: destruct Archi.ptr64; simpl.
  all: unfold Val.of_bool.
  all: split; intros.
  all: repeat break_match.
  all: try reflexivity.
  all: try discriminate.
  all: destruct (i2 <=u i1)%ptrofs eqn: S;
    simpl in *; destruct (i1 <u i2)%ptrofs eqn: D.
  all: try intuition.
Qed.

(* distance between addresses *)
Definition distance (m : mem) (a1 a2 : addr) : option nat :=
  match addr_ge m a2 a1 with
  | Some true => Some ((Z.to_nat (Ptrofs.unsigned (snd a2))) -
                      (Z.to_nat (Ptrofs.unsigned (snd a1))))%nat
  | _ => None
  end.

Lemma ptrofs_le_unsigned_le : forall a b,
  (a <=u b)%ptrofs = true <->
  Ptrofs.unsigned a <= Ptrofs.unsigned b.
Proof.
  split; intros.
  - unfold Ptrofs.ltu in H.
    destruct zlt; [discriminate | lia].
  - unfold Ptrofs.ltu.
    destruct zlt; [lia | reflexivity].
Qed.

Lemma ptrofs_le_unsigned_le_neg : forall a b,
  (a <=u b)%ptrofs = false <->
  not (Ptrofs.unsigned a <= Ptrofs.unsigned b).
Proof.
  split; intros; unfold not; intros.
  - unfold Ptrofs.ltu in H.
    destruct zlt; [nia | intuition].
  - unfold Ptrofs.ltu.
    destruct zlt; intuition.
Qed.

Lemma ptrofs_lt_signed_lt : forall a b,
  (a <u b)%ptrofs = true <->
  Ptrofs.unsigned a < Ptrofs.unsigned b.
Proof.
  split; intros.
  - unfold Ptrofs.ltu in H.
    destruct zlt; [lia | discriminate].
  - unfold Ptrofs.ltu.
    destruct zlt; [reflexivity | lia].
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

Proposition addr_ge_false_distance :
  forall (b : bool) (m : mem) (b1 b2 : block) (i1 i2 : ptrofs) (dist : nat),
    addr_ge m (b1, i1) (b2, i2) = Some false ->
    distance m (b1, i1) (b2, i2) = Some dist -> (0 < dist)%nat.
Proof.
  intros until dist;
    intros Addr Dist.
  unfold distance, sem_cmp, cmp_ptr, addr_ge, ptr_ge,
  Val.cmplu_bool, Val.cmpu_bool, Ptrofs.cmpu,
  Val.cmp_different_blocks,
  classify_cmp in *.
  repeat break_match;
    try congruence; repeat destruct_andb_hyp;
      try congruence.
  simpl in *.
  all: inversion Heqo; clear Heqo;
  rewrite ptrofs_le_unsigned_le in H4;
  inversion Addr; clear Addr;
  rewrite ptrofs_le_unsigned_le_neg in H5;
  destruct i1; destruct i2; simpl in *;
  inversion Dist; clear Dist;
  try rewrite <- Z2Nat.inj_sub;
  try rewrite <- Z2Nat.inj_0;
  try rewrite <- Z2Nat.inj_lt;
  nia.
Qed.

Lemma dist_pred: 
  forall (b : bool) (m : mem) (b1 b2 : block) (ofs : ptrofs) (i : ptrofs) (dist : nat), 
    addr_ge m (b1, ofs) (b2, i) = Some false ->
    distance m (b1, ofs) (b2, i) = Some (dist)%nat ->
    Mem.weak_valid_pointer m b1 (Ptrofs.unsigned (ofs + 1)%ptrofs) = true ->
    distance m (b1, (ofs + 1)%ptrofs) (b2, i) = Some (dist - 1)%nat.
Proof.
intros until dist;
    intros Dist VP1 VP2.
apply dist_succ.
replace (S (dist - 1))%nat with ((dist - 1) + 1)%nat
  by omega.
replace (dist - 1 + 1)%nat with dist.
all: try eassumption.
assert (0 < dist)%nat.
{ eapply addr_ge_false_distance; eassumption. } 
nia.
Qed.


Lemma dist_to_lt : forall m b ofs ofs' dist, 
  distance m (b, ofs) (b, ofs') = Some (S dist) ->
  (Ptrofs.unsigned ofs < Ptrofs.unsigned ofs')%Z.
Proof.
  intros;
  unfold distance in *; simpl in *.
  break_match_hyp; [| discriminate].
  break_if; [| discriminate].
  inversion H; clear H; rename H1 into H.
  assert ((Z.to_nat (Ptrofs.unsigned ofs) 
             < 
             Z.to_nat (Ptrofs.unsigned ofs'))%nat) by lia.
  unfold Ptrofs.unsigned in *.
  destruct ofs, ofs'; simpl in *.
  apply Z2Nat.inj_lt; lia.
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

Lemma int_ptrofs_mod_eq : (Int.modulus = Ptrofs.modulus).
Proof.
  reflexivity.
Qed.


Lemma loaded_is_valid : forall c m b ofs v,
  Mem.load c m b ofs = Some v ->
  Mem.valid_pointer m b ofs = true.
Proof.
  intros.
  apply Mem.valid_pointer_nonempty_perm.
  apply Mem.load_valid_access in H.
  apply Mem.valid_access_perm with (k := Cur) in H.
  apply Mem.perm_implies with (p2 := Nonempty) in H; [| constructor].
  assumption.
Qed.

Lemma ptrofs_to_unsigned_eq : forall i j, i = j <-> Ptrofs.unsigned i = Ptrofs.unsigned j.
Proof.
  intros.
  destruct i.
  destruct j.
  split.
  * congruence.
  * apply Ptrofs.mkint_eq.
Qed.


Hint Resolve Ptrofs.mul_one Ptrofs.add_zero int_ptrofs_mod_eq : ptrofs.
*)
