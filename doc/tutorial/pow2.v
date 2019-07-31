From Coq Require Import String List ZArith Lia.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events.

Require Import Clight.pow2.

Open Scope Z_scope.


(** aliases for clarity **)
Definition Vnat (n : nat) := Vint (Int.repr (Z.of_nat n)).
Definition Mset' := Maps.PTree.set.
Definition Mset := Mset' val.

Ltac gso_simpl := rewrite PTree.gso by discriminate.
Ltac gss_simpl := rewrite PTree.gss.


(** functional specification **)
Definition pow2_fspec (n : nat) := Nat.pow 2 n.


(** aux arithmetic lemmas **)
Lemma pow2_fspec_positive (n : nat) :
  (1 <= pow2_fspec n)%nat.
Proof.
  unfold pow2_fspec.
  assert (1 = 2^0)%nat by trivial; rewrite H at 1; clear H.
  apply Nat.pow_le_mono_r; lia.
Qed.

Lemma pow2_fspec_S (n : nat) :
  (pow2_fspec (S n) = 2 * pow2_fspec n)%nat.
Proof.
  unfold pow2_fspec.
  simpl.
  lia.
Qed.

Lemma succ_not_zero_int (n : nat) :
  Z.of_nat (S n) < Int.modulus ->
  Int.eq (Int.repr (Z.of_nat (S n))) Int.zero = false.
Proof.
  intro.
  apply Int.eq_false.
  intro H1.
  unfold Int.zero in H1.
  apply f_equal with (f := Int.unsigned) in H1.
  repeat rewrite Int.unsigned_repr_eq in H1.
  rewrite Zmod_small, Zmod_0_l in H1
    by (auto with zarith).
  inversion H1.
Qed.

Fact int_max_unsigned_lower_bound :
  4294967295 <= Int.max_unsigned.
Proof.
  unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize.
  cbn; lia.
Qed.

Lemma S_sub_1_int (n : nat) :
  Z.of_nat (S n) < Int.modulus ->
  Vint (Int.sub (Int.repr (Z.of_nat (S n))) (Int.repr 1)) = Vnat n.
Proof.
  intro.
  unfold Int.sub.
  repeat rewrite Int.unsigned_repr. replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
  reflexivity.
  pose proof int_max_unsigned_lower_bound; lia.
  unfold Int.max_unsigned; lia.
Qed.

Lemma sum_n_n_2n_int (n : nat) :
  Z.of_nat n < Int.modulus ->
  Vint (Int.add (Int.repr (Z.of_nat n)) (Int.repr (Z.of_nat n))) = Vnat (n * 2).
Proof.
  intro.
  unfold Int.add.
  repeat rewrite Int.unsigned_repr.
  replace (Z.of_nat n + Z.of_nat n) with (Z.of_nat (n * 2)) by lia.
  reflexivity.
  unfold Int.max_unsigned.
  lia.
Qed.



(** * correctness proofs *)
Definition f_pow2_statement := f_pow2.(fn_body).

(* pull out a part of the AST corresponding to the loop *)
Definition f_pow2_loop :=
  (Swhile
    (Etempvar _n tuint)
    (Ssequence
      (Sset _res
        (Ebinop Oadd (Etempvar _res tuint) (Etempvar _res tuint) tuint))
      (Sset _n
        (Ebinop Osub (Etempvar _n tuint) (Econst_int (Int.repr 1) tint)
          tuint)))).

(*
 * prove corretness of the loop * in isolation from other parts of the function
 * If "res" is bound to an arbitrary value [res] at the beginning
 * then the return will be [res] multiplied by [2] [n] times.
 *
 * This is a generalization, since "res" is normally initially bound to [1],
 * but it actually allows for an easier proof, simplifying induction
 *)
Lemma f_pow2_loop_correct : forall n ge e ste m res,
  Z.of_nat n < Int.modulus ->
  Z.of_nat (res * (pow2_fspec n)) < Int.modulus ->
  
  ste ! _n = Some (Vnat n) ->
  ste ! _res = Some (Vnat res) ->
  
  exists t rte,
    exec_stmt ge e ste m f_pow2_loop t rte m Out_normal /\
    (rte ! _res) = Some (Vnat (res * (pow2_fspec n))).
Proof.
  induction n; intros.
  - (* iBase *)
    repeat eexists.

    (* the loop must stop *)
    eapply exec_Sloop_stop1.
    (* the sequence terminates on first (left) statement with a break *)
    eapply exec_Sseq_2.

    repeat econstructor.
    all: try eassumption.
    all: try econstructor.
    discriminate.
    unfold pow2_fspec; simpl Nat.pow; rewrite Nat.mul_1_r.
    assumption.
  - (* iStep *)

    (* this is the [te] after one iteration of the loop - the one to apply induction hypothesis on *)
    remember (PTree.set _n (Vint (Int.sub (Int.repr (Z.of_nat (S n))) (Int.repr 1)))
               (PTree.set _res (Vint (Int.add (Int.repr (Z.of_nat res)) (Int.repr (Z.of_nat res))))
                 ste))
      as sIte.

    (* prepare induction hypothesis *)
    pose proof IHn ge e sIte m (res * 2)%nat as IH.
    destruct IH as [t IH];
      [ lia
      | rewrite pow2_fspec_S in H0; lia
      | subst; gss_simpl; rewrite S_sub_1_int by assumption; reflexivity
      | subst; gso_simpl; gss_simpl;
          rewrite sum_n_n_2n_int by (pose proof pow2_fspec_positive (S n); nia);
          reflexivity
      |].
    destruct IH as [rIte IH]; destruct IH as [IH1 IH2].
    
    repeat eexists.
    + (* the loop continues for one iteration *)
      eapply exec_Sloop_loop.
      repeat econstructor.
      eassumption.
      econstructor.
      rewrite succ_not_zero_int. econstructor.
      assumption.
      eassumption.
      eassumption.
      econstructor.
      gso_simpl; eassumption.
      econstructor.
      constructor.
      econstructor.

      (** induction hypothesis applied here *)
      (* after some folding *)
      replace
        (Sloop
         (Ssequence (Sifthenelse (Etempvar _n tuint) Sskip Sbreak)
            (Ssequence (Sset _res (Ebinop Oadd (Etempvar _res tuint) (Etempvar _res tuint) tuint))
               (Sset _n (Ebinop Osub (Etempvar _n tuint) (Econst_int (Int.repr 1) tint) tuint)))) Sskip)
        with f_pow2_loop
        by reflexivity.
      rewrite <-HeqsIte.
      eassumption.
    + rewrite IH2; unfold pow2_fspec.
      rewrite Nat.pow_succ_r by lia; rewrite Nat.mul_assoc.
      reflexivity.
Qed.

(** full correctness statement *)
Theorem f_pow2_correct : forall n ge e ste m,
    Z.of_nat n < Int.modulus ->
    Z.of_nat (pow2_fspec n) < Int.modulus ->

    ste ! _n = Some (Vnat n) ->

    exists t rte,
      exec_stmt ge e ste m f_pow2_statement t rte m
        (Out_return (Some (Vnat (pow2_fspec n), tuint))).
Proof.
  intros.

  remember (PTree.set _res (Vint (Int.repr 1)) ste)
    as lte.
  pose proof f_pow2_loop_correct n ge e lte m 1 as LH.
  destruct LH as [t LH];
    [ assumption
    | nia
    | subst; gso_simpl; assumption
    | subst; gss_simpl; reflexivity
    |].
  destruct LH as [rte LH]; destruct LH as [LH1 LH2].

  repeat eexists.
  (*
   * deconstruct the program into three statements:
   * - [res] initialization
   * - loop
   * - return
   *)
  econstructor. 2: econstructor.
  - (* [res] init *)
    repeat econstructor.
  - (* loop. loop correctness lemma applied here *)
    fold f_pow2_loop; rewrite <-Heqlte.
    eassumption.
  - (* return *)
    repeat econstructor.
    rewrite Nat.mul_1_l in LH2.
    assumption.
Qed.

