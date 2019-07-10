From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events.

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

Definition f_pow2_iteration :=
  (Ssequence
    (Sset _res
      (Ebinop Oadd (Etempvar _res tuint) (Etempvar _res tuint) tuint))
    (Sset _n
      (Ebinop Osub (Etempvar _n tuint) (Econst_int (Int.repr 1) tint)
        tuint))).

Definition f_pow2_loop :=
  (Swhile
    (Etempvar _n tuint)
    f_pow2_iteration).

Definition pow2_fspec (n : nat) := Nat.pow 2 n.

Definition Vint_of_nat (n : nat) := Vint (Int.repr (Z_of_nat n)).

Lemma pow2_iteration_correct : forall ge e m res, forall n le,
      0 <= Z.of_nat res <= Int.max_unsigned ->

      le!_n = Some (Vint_of_nat n) ->
      le!_res = Some (Vint_of_nat res) ->
      
      exists t le',
        exec_stmt ge e le m f_pow2_iteration t le' m Out_normal
        /\ (le'!_res) = Some (Vint_of_nat (res + res)).
Admitted.


Lemma pow2_loop_correct : forall ge e m, forall le, forall n res,
      Z.of_nat n < Int.modulus ->
      (* 1 <= *) Z.of_nat res < Int.modulus ->
      Z.of_nat (res * (pow2_fspec n)) < Int.modulus ->
      
      le!_n = Some (Vint_of_nat n) ->
      le!_res = Some (Vint_of_nat res) ->
      
      exists t le',
        exec_stmt ge e le m f_pow2_loop t le' m Out_normal
        /\ (le'!_res) = Some (Vint_of_nat (res * (pow2_fspec n))).
Proof.
  induction n; intros.
  - repeat eexists.
    + eapply exec_Sloop_stop1.
      * eapply exec_Sseq_2.
        repeat econstructor.
        eassumption.
        econstructor.
        econstructor.
        discriminate.
      * constructor.
    + replace (res * pow2_fspec 0)%nat with res.
      assumption.
      rewrite Nat.mul_1_r; reflexivity.
  - repeat eexists.
    + unfold f_pow2_loop.
      unfold Swhile.
      eapply exec_Sloop_loop.
      * repeat econstructor.
        all: try eassumption.
        all: try econstructor.
        -- replace (negb (Int.eq (Int.repr (Z.of_nat (S n))) Int.zero)) with true by admit.
           econstructor.
        -- rewrite PTree.gso by discriminate.
           eassumption.
        -- econstructor.
      * constructor.
      * econstructor.
      * (* time to apply induction hypothesis here? *)
        admit.
    +  (* and here? *)
      admit.
Abort.

Lemma pow2_iteration_correct' : forall ge e m res n le t le',
      0 <= Z.of_nat res <= Int.max_unsigned ->

      le!_n = Some (Vint_of_nat n) ->
      le!_res = Some (Vint_of_nat res) ->
      
      exec_stmt ge e le m f_pow2_iteration t le' m Out_normal ->
      (le'!_res) = Some (Vint_of_nat (res + res)).
Proof.
  intros.
  inversion H2; subst; [| contradict H13; reflexivity].
  inversion H8; subst.
  inversion H13; subst.
  rewrite PTree.gso by discriminate.
  rewrite PTree.gss.
  f_equal.
  clear H2 H8 H11 H13 H14.
  inversion H12; subst.
  - simpl in H9.
    admit.
  - admit.
Admitted.

Lemma pow2_loop_correct_alt : forall ge e m le n res t le',
      Z.of_nat n < Int.modulus ->
      (* 1 <= *) Z.of_nat res < Int.modulus ->
      Z.of_nat (res * (pow2_fspec n)) < Int.modulus ->
      
      le!_n = Some (Vint_of_nat n) ->
      le!_res = Some (Vint_of_nat res) ->
      
      exec_stmt ge e le m f_pow2_loop t le' m Out_normal ->
      (le'!_res) = Some (Vint_of_nat (res * (pow2_fspec n))).
Proof.
  induction n.
  intros.
  - inversion H4; subst.
    inversion H10; subst.
Admitted.
