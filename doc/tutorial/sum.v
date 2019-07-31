From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events.

Require Import Clight.sum.

Local Open Scope Z_scope.

(* statement to be verified extracted from clightgen output *)
Definition sum_statement := f_sum.(fn_body).


(** Specification using CompCert Int **)
Section Int_spec.
  
  (* function specification of correctness *)
  Definition sum_fspec_int (s1 s2 : int) := Int.add s1 s2.
  
  (* 
   * if the starting temporary environment [ste] has values [s1] and [s2]
   * assigned to identifiers "s1" and "s2", then there exist
   * resulting trace [t] and resulting environment [rte], such that
   * execution of [sum_statement] on [ste] results in a return with the correct value
   *)
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
      constructor.
  Qed.

End Int_spec.


(** specification using Coq Z **)
Section Z_spec.

  (* specification now using Z instead of int *)
  Definition sum_fspec_Z (s1 s2 : Z) := s1 + s2.
  
  (*
   * the theorem is very similar, only with boundaries on Z values
   * set (so that they fit int)
   *)
  Theorem f_sum_correct_Z (ge : genv) (e : env) (m : Memory.Mem.mem) :
    forall (ste : temp_env) (s1 s2 : Z),
      ste ! _s1 = Some (Vint (Int.repr s1)) ->
      ste ! _s2 = Some (Vint (Int.repr s2)) ->

      Int.min_signed <= s1 <= Int.max_signed ->
      Int.min_signed <= s2 <= Int.max_signed ->

      exists (t : trace) (rte : temp_env),
        exec_stmt ge e ste m sum_statement t rte m
          (Out_return (Some ((Vint (Int.repr (sum_fspec_Z s1 s2)), tint)))).
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

End Z_spec.
