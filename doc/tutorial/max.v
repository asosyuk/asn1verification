From Coq Require Import String List ZArith Lia.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events.

Require Import Clight.max.

Open Scope Z_scope.

Definition max_fspec := Z.max.

Theorem f_max_correct (ge : genv) (e : env) (m : Memory.Mem.mem) :
  forall (ste : temp_env) (n1 n2 : Z),
    (* starting environment *)
    ste ! _n1 = Some (Vint (Int.repr n1)) ->
    ste ! _n2 = Some (Vint (Int.repr n2)) ->

    (* bounds on coq representation *)
    Int.min_signed <= n1 <= Int.max_signed ->
    Int.min_signed <= n2 <= Int.max_signed ->

    (* correct return *)
    exists (t : trace) (rte : temp_env),
      exec_stmt ge e ste m f_max.(fn_body) t rte m
        (Out_return (Some ((Vint (Int.repr (max_fspec n1 n2)), tint)))).
Proof.
  (* the two branches of this proof are exactly the same,
     but have been left as is for simplicity *)
  intros.
  (* introduce existential variables *)
  destruct (Z_le_dec n1 n2).
  all: repeat eexists.
  - econstructor. (* seq *)
    + (* seq1 - ifthenelse *)
      econstructor. (* if *)
      * (* condition *)
        repeat econstructor.
        eassumption.
        eassumption.
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
        eassumption.
    + (* seq2 - return *)
      econstructor.
      econstructor.
      rewrite PTree.gss.
      try rewrite Z.max_l by lia.
      try rewrite Z.max_r by lia.
      reflexivity.
  - econstructor. (* seq *)
    + (* seq1 - ifthenelse *)
      econstructor. (* if *)
      * (* condition *)
        repeat econstructor.
        eassumption.
        eassumption.
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
        eassumption.
    + (* seq2 - return *)
      econstructor.
      econstructor.
      rewrite PTree.gss.
      try rewrite Z.max_l by lia.
      try rewrite Z.max_r by lia.
      reflexivity.
Qed.
