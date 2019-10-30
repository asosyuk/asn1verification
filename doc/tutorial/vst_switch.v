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
      LOCAL(temp ret_temp (Vint (Int.repr 0)))
      SEP().

Definition Gprog := ltac:(with_library prog [switch_spec]).

Lemma body_switch_test: semax_body Vprog Gprog f_switch_test switch_spec.
 Proof.
   start_function.
   forward_if True.
   repeat forward.
   forward.
   forward.
   entailer!.
   forward.
Qed.

Definition switch_fail_spec : ident * funspec :=
  DECLARE _switch_test_fail
    WITH i : int
    PRE [_i OF tint]
      PROP()
      LOCAL(temp _i (Vint (Int.repr (Int.signed i))))
      SEP()
    POST [ tint ]
      PROP()
      LOCAL(temp ret_temp (Vint (Int.repr 0)))
      SEP().

Definition Gprog_switch := ltac:(with_library prog [switch_fail_spec]).

Lemma body_switch_fail_test: semax_body Vprog Gprog_switch f_switch_test_fail switch_fail_spec.
 Proof.
   start_function.
   forward_if True.
   repeat forward.
   forward.
   forward.
   entailer.
Abort.

Definition twice_spec :=
  DECLARE _twice
    WITH n : Z
    PRE [ _n OF tint ]
      PROP  (Int.min_signed <= n+n <= Int.max_signed)
      LOCAL (temp _n (Vint (Int.repr n)))
      SEP ()
    POST [ tint ]
      PROP ()
      LOCAL (temp ret_temp (Vint (Int.repr (n+n))))
      SEP ().

Definition Gprog' : funspecs :=   ltac:(with_library prog [twice_spec]).

Lemma body_twice: semax_body Vprog Gprog' f_twice twice_spec.
Proof.
start_function.
forward_if (PROP() LOCAL(temp _n (Vint (Int.repr (n + n)))) SEP()).
repeat forward; entailer!.
repeat forward; entailer!.
repeat forward; entailer!.
repeat forward; entailer!.
repeat forward; entailer!.
repeat forward; entailer!.
Qed.

Definition twice_fail_spec :=
  DECLARE _twice_fail
    WITH n : Z
    PRE [ _n OF tint ]
      PROP  (Int.min_signed <= n+n <= Int.max_signed)
      LOCAL (temp _n (Vint (Int.repr n)))
      SEP ()
    POST [ tint ]
      PROP ()
      LOCAL (temp ret_temp (Vint (Int.repr (n+n))))
      SEP ().

Definition Gprog'' : funspecs :=   ltac:(with_library prog [twice_fail_spec]).

Lemma body_twice_fail: semax_body Vprog Gprog'' f_twice_fail twice_fail_spec.
Proof.
start_function.
forward_if (PROP() LOCAL(temp _n (Vint (Int.repr (n)))) SEP()).
repeat forward; entailer!.
repeat forward; entailer!.
repeat forward; entailer!.
forward.
entailer.
Abort.
