rom Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events.

Require Import Clight.sum.

Local Open Scope Z_scope.

Definition sum_statement := f_sum.(fn_body).

Definition sum_fspec (s1 s2 : Z) := s1 + s2.

Theorem f_sum_correct (ge : genv) (e : env) (m : Memory.Mem.mem) :
  forall (ste : temp_env) (s1 s2 : Z),
    ste ! _s1 = Some (Vint (Int.repr s1)) ->
    ste ! _s2 = Some (Vint (Int.repr s2)) ->
    Int.min_signed <= s1 <= Int.max_signed ->
    Int.min_signed <= s2 <= Int.max_signed ->
    exists (t : trace) (rte : temp_env),
      exec_stmt ge e ste m sum_statement t rte m
        (Out_return (Some ((Vint (Int.repr (sum_fspec s1 s2)), tint)))).
Proof.
  intros.
  repeat eexists.
  repeat econstructor.
  - eassumption.
  - eassumption.
  - cbn.
    unfold sem_binarith; simpl.
    repeat rewrite cast_val_casted by (econstructor; auto).
    repeat rewrite Int.add_signed.
    repeat rewrite Int.signed_repr.
    reflexivity.
    assumption.
    assumption.
Qed.

Definition sum_fspec_int (s1 s2 : int) := Int.add s1 s2.

Theorem f_sum_correct_int (ge : genv) (e : env) (m : Memory.Mem.mem) :
  forall (ste : temp_env) (s1 s2 : int),
    ste ! _s1 = Some (Vint s1) ->
    ste ! _s2 = Some (Vint s2) ->
    exists (t : trace) (rte : temp_env),
      exec_stmt ge e ste m sum_statement t rte m
        (Out_return (Some (Vint (sum_fspec_int s1 s2), tint))).
Proof.
  intros.
  repeat eexists.
  repeat econstructor.
  - eassumption.
  - eassumption.
  - unfold sum_fspec_int.
    econstructor.
Qed.
