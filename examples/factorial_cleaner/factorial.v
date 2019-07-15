From Coq Require Import String List ZArith Arith Lia.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events.

Local Open Scope Z_scope.

Definition _input : ident := 53%positive.
Definition _output : ident := 54%positive.

Definition f_factorial := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_input, tuint) :: nil);
  fn_vars := nil; 
  fn_temps := ((_output, tuint) :: nil);
  fn_body :=
  (Ssequence
    (Sset _output (Econst_int (Int.repr 1) tuint))
    (Ssequence 
      (Swhile 
        (Etempvar _input tuint)
        (Ssequence  
          (Sset _output
            (Ebinop Omul (Etempvar _output tuint) (Etempvar _input tuint) tuint))
          (Sset _input
            (Ebinop Osub (Etempvar _input tuint) (Econst_int (Int.repr 1) tuint)
              tuint))))
      (Sreturn (Some (Etempvar _output tuint)))))
|}.

Fixpoint fact_fspec (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * fact n'
  end.

Definition factorial_loop :=
  (Swhile 
    (Etempvar _input tuint)
    (Ssequence  
      (Sset _output
        (Ebinop Omul (Etempvar _output tuint) (Etempvar _input tuint) tuint))
      (Sset _input
        (Ebinop Osub (Etempvar _input tuint) (Econst_int (Int.repr 1) tuint)
          tuint)))).

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

(* req *)
Lemma fact_succ_geq (n : nat) :
    (S n <= fact (S n))%nat.
Proof.
  induction n; simpl in *; lia.
Qed.

Definition Vnat (n : nat) := Vint (Int.repr (Z.of_nat n)).
Definition Mset' := Maps.PTree.set.
Definition Mset := Mset' val.

Ltac gso := rewrite PTree.gso by discriminate.
  
Theorem factorial_loop_correct : forall ge e m, forall inp outp le,
      Z.of_nat inp < Int.modulus ->
      1 <= Z.of_nat outp < Int.modulus ->
      Z.of_nat ((fact inp) * outp) < Int.modulus ->
      
      le ! _input = Some (Vnat inp) ->
      le ! _output = Some (Vnat outp) ->
      
      exists t le',
        exec_stmt ge e le m factorial_loop t le' m Out_normal
        /\
        le' ! _output = Some (Vnat ((fact inp) * outp)).
Proof.
  induction inp;
    intros outp le H Hout Hloop H2 H3.
  - (** iBase **)
    repeat eexists.
    + eapply exec_Sloop_stop1.
      eapply exec_Sseq_2.
      repeat econstructor.
      all: try eassumption; try econstructor.
      discriminate.
    + simpl.
      rewrite Nat.add_0_r.
      assumption.
  - (** iStep *)
    assert (
        let res_le := (Mset _input (Vnat inp)
                            (Mset _output (Vnat (outp * S inp))
                                  le)) in
        exists (t : trace) (le' : temp_env),
          exec_stmt ge e res_le m factorial_loop t le' m Out_normal
          /\
          le' ! _output =  Some (Vnat ((fact inp) * (outp * S inp)))).
    {
      intro; subst res_le.
      apply IHinp.
      + lia.
      + pose proof fact_succ_geq inp.
        nia.
      + simpl in Hloop. nia. 
      + apply PTree.gss.
      + gso.
        apply PTree.gss.
    }
    destruct H0. destruct H0. destruct H0. 
    repeat eexists;
      [| rewrite H1; simpl; f_equal; f_equal; nia].
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
      (PTree.set _input (Vint (Int.sub (Int.repr (Z.of_nat (S inp)))
                                       (Int.repr 1)))
        (PTree.set _output (Vint (Int.mul (Int.repr (Z.of_nat outp))
                                          (Int.repr (Z.of_nat (S inp)))))
          le))
      with
        (Mset _input (Vnat inp)
                  (Mset _output (Vnat (outp * S inp))
                        le)).
    eassumption.
    unfold Mset, Mset', Vnat.
    repeat f_equal.
    1: unfold Int.sub.
    2: unfold Int.mul.
    all: repeat rewrite Int.unsigned_repr_eq;
      f_equal; repeat rewrite Zmod_small; nia.
Qed.

Theorem factorial_correct : forall ge e m n le,
    Z.of_nat n < Int.modulus ->
    Z.of_nat (fact n) < Int.modulus ->
    le!_input = Some (Vnat n) ->
    exists t le' out,
      exec_stmt ge e le m f_factorial.(fn_body) t le' m out
      /\
      (le'!_output) = Some (Vnat (fact n)).
Proof.
  intros.
  assert (
      exists t le',
        exec_stmt ge e (Mset _output (Vnat 1) le) m factorial_loop t le' m Out_normal
        /\
        le' ! _output = Some (Vnat (fact n * 1))
    ).
  {
    eapply factorial_loop_correct.
    + apply H.
    + simpl. split; auto with zarith. cbv. auto. 
    + nia.      
    + rewrite PTree.gso. apply H1. cbv. congruence.
    + apply PTree.gss.
  }
  destruct H2. destruct H2.  destruct H2.
  eexists. eexists.
  exists (Out_return (Some (Vnat (fact n), tuint))).
  split.
  + eapply exec_Sseq_1.
    econstructor. econstructor.
    eapply exec_Sseq_1.
    apply H2.
    repeat econstructor; rewrite Nat.mul_1_r in H3; exact H3.
  + rewrite Nat.mul_1_r in H3.
    exact H3.
Qed.
