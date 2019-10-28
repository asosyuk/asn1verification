Require Import Clight.switch.
Require Import StructTact.StructTactics.
Require Import VST.floyd.proofauto.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.


Open Scope program_scope.

Definition switch_spec : ident * funspec :=
  DECLARE _switch_test
    WITH i : int
    PRE [_i OF tint]
      PROP()
      LOCAL(temp _i (Vint (Int.repr (Int.signed i))))
      SEP()
    POST [ tint ]
      PROP()
      LOCAL(temp ret_temp (Vint (Int.repr (Int.signed i))))
      SEP().

Definition Gprog := ltac:(with_library prog [switch_spec]).

Lemma body_max: semax_body Vprog Gprog f_switch_test switch_spec.
Proof.
  start_function.
  forward_if True.
  forward.
  forward_if.
  admit.
  forward.
  entailer!.
  forward_if (i = 0 \/ i = 1 \/ (i <> 0 /\ i <> 1)).
  forward.
  forward_if.
  
  
