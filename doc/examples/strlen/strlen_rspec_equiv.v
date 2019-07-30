From Coq Require Import String List ZArith Lia.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events Memory.

Inductive strlen (m : mem) (b : block) (ofs : ptrofs) : nat -> Prop :=
| LengthZero: Mem.loadv Mint8signed m (Vptr b ofs) = Some (Vint Int.zero) -> strlen m b ofs 0
| LengthSucc: forall n c,
    Z.of_nat (S n) < Int.modulus -> (* no int overflow *)
    Ptrofs.unsigned ofs + 1 < Ptrofs.modulus -> (* no ofs overflow *)
    strlen m b (Ptrofs.add ofs Ptrofs.one) n ->
    Mem.loadv Mint8signed m (Vptr b ofs)  = Some (Vint c) ->
    c <> Int.zero ->
    strlen m b ofs (S n).

Inductive strlen_rspec' (m : mem) (b : block) (ofs : ptrofs) : nat -> Prop :=
| LengthZero':
    Mem.loadv Mint8signed m (Vptr b ofs) = Some (Vint Int.zero) ->
    strlen_rspec' m b ofs 0
| LengthSucc':
    forall n c,
    Z.of_nat (S n) < Int.modulus ->
    Ptrofs.unsigned ofs + 1 < Ptrofs.modulus ->
    Mem.loadv Mint8signed m (Vptr b ofs)  = Some (Vint c) ->
    Int.eq c Int.zero = false ->
    strlen_rspec' m b (Ptrofs.add ofs Ptrofs.one) n ->
    strlen_rspec' m b ofs (S n).

Lemma intzero_zero (c : int) :
  c <> Int.zero ->
  Int.eq c Int.zero = false.
Proof.
  intro Z.
  unfold Int.eq.
  destruct zeq; [exfalso | reflexivity].
  rewrite Int.unsigned_zero in e.
  contradict Z.
  

Theorem rspec_equiv (m : mem) (b : block) (ofs : ptrofs) (l : nat) :
  strlen m b ofs l
  <->
  strlen_rspec' m b ofs l.
Proof.
  split; intro S.
  - induction S.
    + constructor; assumption.
    + econstructor; try eassumption.
      apply intzero_zero; assumption.
  - induction S.
    + constructor; assumption.
    + econstructor; try eassumption.
      intro C; contradict H2.
      rewrite C, Int.eq_true.
      discriminate.
Qed.
