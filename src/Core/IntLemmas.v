Require Import StructTact.StructTactics.
Require Import Core.Core.


(** * Some lemmas about integers *)

Definition IntMax := Int.repr Int.max_unsigned.

Lemma int_to_unsigned_eq : forall i j, i = j -> Int.unsigned i = Int.unsigned j.
Proof.
  intros.
  congruence.
Qed.

Lemma int_to_unsigned_neq : forall i j, i <> j -> Int.unsigned i <> Int.unsigned j.
Proof.
  intros.
  destruct (zeq (Int.unsigned i) (Int.unsigned j)) eqn : G.
  pose (Int.eq_false _ _ H).
  unfold Int.eq in e0.
  rewrite G in e0.
  congruence.
  assumption.
Qed.

Lemma non_zero_surj :
  forall i, Int.add i Int.one <> Int.zero ->
       Int.unsigned (Int.add i Int.one) = Int.unsigned i + 1.
Proof.
  intros.
  destruct (Z.eq_dec (Int.unsigned (Int.add i Int.one)) (Int.unsigned i + 1)).
  intuition.
  unfold Int.add in n.
  assert (i <> IntMax).
  destruct (Int.eq_dec i IntMax).
  rewrite e in H.
  
  assert (Int.add IntMax Int.one = Int.zero).
  { unfold IntMax.
    unfold Int.add.
    unfold Int.zero.
    simpl; unfold Int.add; unfold Int.mul;
      repeat rewrite Int.unsigned_repr_eq;
      repeat rewrite Int.unsigned_repr_eq;
      repeat rewrite Zmod_small.
    replace (Int.max_unsigned + Int.unsigned Int.one) with (Int.modulus) by (auto with ints).
    pose (Int.mkint_eq).
    destruct  (Int.repr Int.modulus) eqn : IM.
    destruct (Int.repr 0) eqn : S0.
    apply Int.mkint_eq.
    assert (Int.repr Int.modulus =
            Int.mkint (Int.Z_mod_modulus Int.modulus) (Int.Z_mod_modulus_range' Int.modulus))
      by (auto with ints).
    rewrite H0 in IM.
    inversion IM.
    inversion S0.
    replace (match Int.repr 0 with
             | {| Int.intval := intval1 |} => intval1
             end) with 0 by (auto with ints).
    auto.
    cbv.
    split; congruence.
  }
  congruence.
  assumption.
  simpl; unfold Int.add; unfold Int.mul;
    repeat rewrite Int.unsigned_repr_eq;
    repeat rewrite Int.unsigned_repr_eq;
    repeat rewrite Zmod_small.
  auto with ints.
  assert (Int.unsigned i < Int.max_unsigned).
  assert (Int.unsigned i <> Int.unsigned IntMax) by (eapply (int_to_unsigned_neq _ _ H0)).
  destruct i; simpl in *.
  unfold IntMax in *.
  replace (Int.unsigned (Int.repr Int.max_unsigned)) with (Int.max_unsigned) in H1 by (auto with ints).
  unfold Int.max_unsigned in *.
  nia.
  unfold Int.max_unsigned in *.
  replace (Int.unsigned Int.one) with 1 by (auto with ints). 
  pose (Int.unsigned_range i).
  nia.
Qed.

Lemma int_overflow_unsigned_to_add :
  forall z, 0 < Int.unsigned z + 1 < Int.modulus ->
       Int.add z Int.one <> Int.zero.
Proof.
  intros.
  unfold Int.zero.
  destruct (Int.eq (Int.add z Int.one) (Int.repr 0)) eqn: Sz.
  pose (Int.eq_spec (Int.add z Int.one) (Int.repr 0)) as E.
  unfold Int.eq in Sz.
  destruct (zeq (Int.unsigned (Int.add z Int.one))
                (Int.unsigned (Int.repr 0))).
  unfold Int.add in e.
  repeat rewrite Int.unsigned_repr_eq in e.
  rewrite Zmod_small in e.
  rewrite  Zmod_small in e.
  replace (Int.unsigned Int.one) with 1 in e by (auto with ints).  nia.
  nia.
  replace (Int.unsigned Int.one) with 1 by (auto with ints).  nia.
  congruence.
  pose (Int.eq_spec (Int.add z Int.one)  (Int.repr 0)).
  rewrite Sz in y.
  assumption. 
Qed.

(* Induction principle for integers *)

Lemma int_induction :
  forall (P : int -> Prop),
    P Int.zero ->
    (forall i, P i -> P (Int.add i Int.one))
    -> forall i, P i.
Proof.
  induction i.
  eapply (natlike_ind (fun intval => forall intrange : -1 < intval < Int.modulus,
                           P {| Int.intval := intval; Int.intrange := intrange |})).
  (* Base case *)
  - intro.
    unfold Int.zero in H.
    assert ((Int.repr 0) = {| Int.intval := 0; Int.intrange := intrange0 |}).
    assert (Int.unsigned {| Int.intval := 0; Int.intrange := intrange0 |} =
            Int.unsigned (Int.repr (0))).
    { simpl.
      rewrite Int.unsigned_repr.
      auto.
      unfold Int.max_unsigned.
      nia. }    
    destruct (Int.repr 0) eqn: S0.
    apply Int.mkint_eq.
    simpl in H1.
    nia.
    rewrite  H1 in H.
    assumption.
  - intros.
    assert (X: -1 < x < Int.modulus) by nia.
    pose (p := H2 X).
    pose (H0 {| Int.intval := x; Int.intrange := X |} p).
    assert ({| Int.intval := Z.succ x; Int.intrange := intrange0 |} =
            (Int.add {| Int.intval := x; Int.intrange := X |} Int.one)).
    unfold Int.add.
    unfold Int.one.
    unfold Int.unsigned.
    replace (Int.intval (Int.repr 1)) with 1 by (auto with ints).
    simpl.
    replace (x + 1) with (Z.succ x) by nia.
    assert (Int.unsigned {| Int.intval := Z.succ x; Int.intrange := intrange0 |} =
            Int.unsigned (Int.repr (Z.succ x))).
    simpl.
    rewrite Int.unsigned_repr.
    auto.
    unfold Int.max_unsigned.
    nia.
    destruct (Int.repr (Z.succ x)) eqn: Sa.
    apply Int.mkint_eq.
    simpl in H3.
    assumption.
    rewrite <- H3 in p0.
    assumption.
  - nia.
Qed.

Lemma intval_eq : forall (n i : int),
    match n with | {| Int.intval := intval |} => intval end =
    match i with | {| Int.intval := intval |} => intval end ->
    (n = i).
Proof.
  intros.
  destruct (n) eqn: Sn.
  destruct (i) eqn: Si. 
  apply Int.mkint_eq.
  assumption.
Qed.
  
Lemma signed_le_int_le : forall a b,
  Int.signed a <= Int.signed b <->
  (a <= b)%int = true.
Proof.
  split; intros.
  - unfold Int.lt.
    destruct zlt; [lia | reflexivity].
  - unfold Int.lt in H.
    destruct zlt; [discriminate | lia].
Qed.

Lemma signed_le_sem_Cle {is1 is2 : intsize} : forall a b m,
  (Int.signed a <= Int.signed b)%Z <->
  sem_cmp Cle (Vint a) (Tint is1 Signed noattr)
              (Vint b) (Tint is2 Signed noattr) m
  = Some Vtrue.
Proof.
  intros.
  unfold sem_cmp, sem_binarith, sem_cast, classify_cmp; simpl.
  split; intros.
  - all: destruct is1, is2; simpl.
    all: destruct Archi.ptr64; simpl.
    all: rewrite signed_le_int_le in H.
    all: rewrite H; reflexivity.
  - all: destruct is1, is2; simpl.
    all: unfold classify_cast, binarith_type in H.
    all: destruct Archi.ptr64; simpl in H.
    all: unfold Val.of_bool in H.
    all: break_match; try discriminate.
    all: rewrite signed_le_int_le; assumption.
Qed.

Lemma int_le_trans : forall a b c,
    (a <= b)%int = true ->
    (b <= c)%int = true ->
    (a <= c)%int = true.
Proof.
  intros.
  unfold Int.lt in *.
  repeat break_match.
  all: try discriminate.
  lia.
  reflexivity.
Qed.
