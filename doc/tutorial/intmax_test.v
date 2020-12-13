From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight.
From compcert Require Import Maps Values ClightBigstep Events Clightdefs.

Require Import Clight.intmax_test.

Open Scope Z_scope.

Definition spec := 2.

Theorem f_intmax_test_correct (ge : genv) (e : env) (m : Memory.Mem.mem) :
  forall (ste : temp_env) (n1 n2 : Z),
    (* starting environment *)
    ste ! _a = Some (Vlong (Int64.repr 1)) ->
    ste ! _b = Some (Vlong (Int64.repr 1)) ->

    (* correct return *)
    exists (t : trace) (rte : temp_env),
      exec_stmt ge e ste m f_long_test.(fn_body) t rte m
        (Out_return (Some (Vundef, tvoid))).
