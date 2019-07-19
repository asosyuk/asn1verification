From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events.
  
Require Import Lia.

Local Open Scope Z_scope.

Definition _n : ident := 53%positive.
Definition _res : ident := 54%positive.

Definition f_pow2 := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _res (Econst_int (Int.repr 1) tint))
  (Ssequence
    (Swhile
      (Etempvar _n tuint)
      (Ssequence
        (Sset _res
          (Ebinop Oadd (Etempvar _res tuint) (Etempvar _res tuint) tuint))
        (Sset _n
          (Ebinop Osub (Etempvar _n tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Sreturn (Some (Etempvar _res tuint)))))
|}.

Definition f_pow2_loop :=
  (Swhile
    (Etempvar _n tuint)
    (Ssequence
      (Sset _res
        (Ebinop Oadd (Etempvar _res tuint) (Etempvar _res tuint) tuint))
      (Sset _n
        (Ebinop Osub (Etempvar _n tuint) (Econst_int (Int.repr 1) tint)
          tuint)))).

Definition Vnat (n : nat) := Vint (Int.repr (Z.of_nat n)).
Definition Mset' := Maps.PTree.set.
Definition Mset := Mset' val.

Ltac gso := rewrite PTree.gso by discriminate.
Ltac gss := apply PTree.gss.

Lemma succ_not_zero_int (n : nat) :
  Z.of_nat (S n) < Int.modulus ->
  Int.repr (Z.of_nat (S n)) <> Int.repr (Z.of_nat O).
Proof.
  intros; intro H1.
  apply f_equal with (f := Int.unsigned) in H1.
  repeat rewrite Int.unsigned_repr_eq in H1.
  rewrite Zmod_small, Zmod_0_l in H1
    by (auto with zarith).
  inversion H1.
Qed.

Definition pow2_fspec (n : nat) := Nat.pow 2 n.

Lemma pow2_fspec_S_geq_2 (n : nat) :
  (2 <= pow2_fspec (S n))%nat.
Proof.
  unfold pow2_fspec.
  assert (2 = 2^1)%nat by trivial; rewrite H at 1; clear H.
  apply Nat.pow_le_mono_r; lia.
Qed.

Lemma pow2_fspec_S (n : nat) :
  (pow2_fspec (S n) = 2 * pow2_fspec n)%nat.
Proof.
  unfold pow2_fspec.
  simpl.
  lia.
Qed.

Lemma f_pow2_loop_correct : forall ge e m, forall n res le,
      Z.of_nat n < Int.modulus ->
      (* 1 <= *) Z.of_nat res < Int.modulus ->
      Z.of_nat (res * (pow2_fspec n)) < Int.modulus ->
      
      le!_n = Some (Vnat n) ->
      le!_res = Some (Vnat res) ->
      
      exists t le',
        exec_stmt ge e le m f_pow2_loop t le' m Out_normal
        /\ (le'!_res) = Some (Vnat (res * (pow2_fspec n))).
Proof.
  induction n; intros.
  - repeat eexists.
    + eapply exec_Sloop_stop1.
      eapply exec_Sseq_2.
      repeat econstructor.
      all: repeat econstructor.
      all: try eassumption; try discriminate.
      econstructor.
      econstructor.
    + replace (res * pow2_fspec 0)%nat with res
        by (rewrite Nat.mul_1_r; reflexivity).
      assumption.
  - assert
      (
        let step_le := (Mset _n (Vnat n)
                            (Mset _res (Vnat (res * 2))
                                  le)) in
        exists (t : trace) (le' : temp_env),
          exec_stmt ge e step_le m f_pow2_loop t le' m Out_normal
          /\
          le' ! _res =  Some (Vnat ((res * 2) * (pow2_fspec n) ))
      ).
    {
      intro; subst step_le.
      apply IHn.
      - lia.
      - pose proof pow2_fspec_S_geq_2 n.
        nia.
      - rewrite <-Nat.mul_assoc, <-pow2_fspec_S.
        assumption.
      - apply PTree.gss.
      - gso; gss.
    }
    destruct H4. destruct H4. destruct H4.
    repeat eexists;
     [| rewrite pow2_fspec_S, Nat.mul_assoc; eassumption].
    eapply exec_Sloop_loop.
    eapply exec_Sseq_1.
    2: eapply exec_Sseq_1.
    econstructor.
    econstructor.
    eassumption.
    econstructor.
    rewrite Int.eq_false
       by (apply succ_not_zero_int; assumption); simpl.
    econstructor.
    repeat econstructor.
    eassumption.
    eassumption.
    repeat econstructor.
    repeat econstructor.
    gso; eassumption.
    repeat econstructor.
    econstructor.
    econstructor.
    replace 
      (PTree.set _n (Vint (Int.sub (Int.repr (Z.of_nat (S n)))
                                       (Int.repr 1)))
        (PTree.set _res (Vint (Int.add (Int.repr (Z.of_nat res))
                                          (Int.repr (Z.of_nat res))))
          le))
      with
        (Mset _n (Vnat n)
                  (Mset _res (Vnat (res * 2))
                        le)).
    eassumption.
    unfold Mset, Mset', Vnat.
    repeat f_equal.
    1: unfold Int.sub.
    2: unfold Int.add.
    all: repeat rewrite Int.unsigned_repr_eq;
      f_equal; repeat rewrite Zmod_small; nia.
Qed.

Theorem f_pow2_correct : forall ge e m n le,
    Z.of_nat n < Int.modulus ->
    Z.of_nat (pow2_fspec n) < Int.modulus ->
    le!_n = Some (Vnat n) ->
    exists t le' out,
      exec_stmt ge e le m (fn_body f_pow2) t le' m out
      /\
      (le'!_res) = Some (Vnat (pow2_fspec n)).
Proof.
  intros.
  assert
    (
      exists t le',
        exec_stmt ge e (Mset _res (Vnat 1) le) m f_pow2_loop t le' m Out_normal
        /\
        le' ! _res = Some (Vnat (1 * (pow2_fspec n)))
    ).
  {
    eapply f_pow2_loop_correct.
    + apply H.
    + split.
    + nia.
    + rewrite PTree.gso. apply H1. cbv. congruence.
    + apply PTree.gss.
  }
  destruct H2. destruct H2.  destruct H2.
  eexists. eexists.
  exists (Out_return (Some (Vnat (pow2_fspec n), tuint))).
  split.
  + eapply exec_Sseq_1.
    econstructor. econstructor.
    eapply exec_Sseq_1.
    apply H2.
    repeat econstructor; rewrite Nat.mul_1_l in H3; assumption.
  + rewrite Nat.mul_1_l in H3.
    assumption.
Qed.
