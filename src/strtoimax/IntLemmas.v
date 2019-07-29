From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.

Lemma  int_to_unsigned_neq  : forall i j, i <> j -> Int.unsigned i <> Int.unsigned j.
Proof.
  intros.
  destruct (zeq (Int.unsigned i) (Int.unsigned j)) eqn : G.
  pose (Int.eq_false _ _ H).
  unfold Int.eq in e0.
  rewrite G in e0.
  congruence.
  assumption.
Qed.

Proposition char_not_zero : forall c, c <> Int.zero -> true = (negb (Int.eq c Int.zero)).
Proof.
  intros.
  replace (Int.eq c Int.zero) with false.
  auto.
  rewrite Int.eq_false; intuition.
Qed.

Hint Resolve char_not_zero : ints.
