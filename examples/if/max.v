From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events.
Require Import Lia.

Local Open Scope Z_scope.

Definition _res : ident := 55%positive.
Definition _s1 : ident := 53%positive.
Definition _s2 : ident := 54%positive.

Definition f_max := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s1, tint) :: (_s2, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ogt (Etempvar _s1 tint) (Etempvar _s2 tint) tint)
    (Sset _res (Etempvar _s1 tint))
    (Sset _res (Etempvar _s2 tint)))
  (Sreturn (Some (Etempvar _res tint))))
|}.

Theorem f_max_correct (any_genv : genv) (any_env : env) (any_mem : Memory.Mem.mem) :
  forall (tenv : temp_env) (s1 s2 : Z),
    tenv!_s1 = Some (Vint (Int.repr s1)) ->
    tenv!_s2 = Some (Vint (Int.repr s2)) ->
    Int.min_signed <= s1 <= Int.max_signed ->
    Int.min_signed <= s2 <= Int.max_signed ->
    exists (res_tr : trace) (res_te : temp_env),
      exec_stmt
        any_genv
        any_env
        tenv
        any_mem
        f_max.(fn_body)
        res_tr
        res_te
        any_mem
        (Out_return (Some ((Vint (Int.repr (Z.max s1 s2)), tint)))).
Proof.
  intros.
  (* introduce existential variables *)
  destruct (Z_le_dec s1 s2).
  all: econstructor; econstructor.
  simpl.
  - econstructor. (* seq *)
    + (* seq1 *)
      econstructor. (* if *)
      * (* condition *)
        repeat econstructor.
        apply H.
        apply H0.
        simpl.
        econstructor.
      * (* condition bool *)
        simpl.
        unfold Int.lt.
        repeat rewrite Int.signed_repr by assumption.
        destruct zlt; try omega.
        econstructor.
      * (* set result *)
        destruct negb eqn:N; inversion_clear N.
        repeat econstructor.
        apply H0.
    + (* seq2 *)
      econstructor. (* return *)
      econstructor.
      rewrite PTree.gss.
      replace (Z.max s1 s2) with s2 by lia.
      reflexivity.
  - econstructor. (* seq *)
    + (* seq1 *)
      econstructor. (* if *)
      * (* condition *)
        repeat econstructor.
        apply H.
        apply H0.
        simpl.
        econstructor.
      * (* condition bool *)
        simpl.
        unfold Int.lt.
        repeat rewrite Int.signed_repr by assumption.
        destruct zlt.
        econstructor.
        contradict n.
        lia.
      * (* set result *)
        destruct negb eqn:N; inversion_clear N.
        repeat econstructor.
        apply H.
    + (* seq2 *)
      econstructor. (* return *)
      econstructor.
      rewrite PTree.gss.
      replace (Z.max s1 s2) with s1 by lia.
      reflexivity.
Qed.
