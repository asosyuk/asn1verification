Require Import StructTact.StructTactics.
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
  option_map negb (addr_ge m a2 a1).

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

Proposition ptr_ge_to_sem_cmp_true : forall m b1 b2 i1 i2,
    ptr_ge m b1 b2 i1 i2 = Some true ->
    sem_cmp Cge (Vptr b1 i1) (tptr tschar) (Vptr b2 i2) (tptr tschar) m = 
    Some Vtrue.
Proof.
  intros.
  assert ((option_map Val.of_bool (ptr_ge m b1 b2 i1 i2)) =
          (option_map Val.of_bool (Some true))) by (f_equal; assumption).
  eassumption.
Qed.

Proposition ptr_ge_to_sem_cmp_false : forall m b1 b2 i1 i2,
    ptr_ge m b1 b2 i1 i2 = Some false ->
    sem_cmp Cge (Vptr b1 i1) (tptr tschar) (Vptr b2 i2) (tptr tschar) m = 
    Some Vfalse.
Proof.
  intros.
  assert ((option_map Val.of_bool (ptr_ge m b1 b2 i1 i2)) =
          (option_map Val.of_bool (Some false))) by (f_equal; assumption).
  eassumption.
Qed.

(* distance between addresses *)
Definition distance (m : mem) (a1 a2 : addr) : option nat :=
  match addr_ge m a2 a1 with
  | Some true => Some ((Z.to_nat (Ptrofs.unsigned (snd a2))) -
                      (Z.to_nat (Ptrofs.unsigned (snd a1))))%nat
  | _ => None
  end.

Lemma dist_succ : forall m b b' ofs ofs' dist,
    distance m (b', ofs') (b, ofs) = Some (S dist) ->
    Mem.valid_pointer m b' (Ptrofs.unsigned (ofs' + 1)%ptrofs) = true ->
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
  all: try discriminate.
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

Lemma dist_pred: 
  forall (m : mem) (b : block) (ofs : ptrofs) (i : ptrofs) (dist : nat), 
    addr_ge m (b, ofs) (b, i) = Some false -> 
    addr_ge m ((b, ofs) ++) (b, i) = Some false -> 
    distance m (b, ofs) (b, i) = Some (dist - 1)%nat ->
    Mem.valid_pointer m b (Ptrofs.unsigned (ofs + 1)%ptrofs) = true ->
    distance m (b, (ofs + 1)%ptrofs) (b, i) = Some dist.

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

Hint Resolve Ptrofs.mul_one Ptrofs.add_zero int_ptrofs_mod_eq : ptrofs.
