From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events.

Local Open Scope Z_scope.

Definition _n : ident := 53%positive.

Definition f_identity := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_n, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Etempvar _n tint)))
|}.

Definition identity_statement := fn_body f_identity.

Definition identity_fspec (n : Z) := n.

Theorem f_identity_correct_ex (ge : genv) (e : env) (m : Memory.Mem.mem)
        (te : temp_env) (n : Z) :
    te!_n = Some (Vint (Int.repr n)) ->
    exists (t : trace) (te' : temp_env),
      exec_stmt ge e te m identity_statement t te' m
      (Out_return (Some ((Vint (Int.repr (identity_fspec n)), tint)))).
Proof.
  intros.
  repeat eexists.
  repeat constructor.
  assumption.
Qed.

(*
 * this statement is stronger, proving that
 * memory does not change and trace is nil
 *)
Theorem f_identity_correct_impl (ge : genv) (e : env) (m : Memory.Mem.mem)
        (te : temp_env) (n : Z) :
    te!_n = Some (Vint (Int.repr n)) ->
      exec_stmt ge e te m identity_statement nil te m
      (Out_return (Some ((Vint (Int.repr (identity_fspec n)), tint)))).
Proof.
  intros.
  repeat constructor.
  assumption.
Qed.
