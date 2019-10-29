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
      LOCAL(temp ret_temp (if Int.eq i Int.zero
                           then Vint Int.zero
                           else if Int.eq i Int.one
                                then Vint Int.one
                                else Vint (Int.repr 2)))
                 SEP().

Definition Gprog := ltac:(with_library prog [switch_spec]).

     
Lemma body_max: semax_body Vprog Gprog f_switch_test switch_spec.
Proof.
  start_function.
  forward_if ((@FF (environ->mpred) _));
    forward; try entailer!.  
  - replace (Int.eq i Int.zero) with true.
    auto.
    rewrite Int.signed_eq.
    destruct zeq; intuition.
  - repeat rewrite Int.signed_eq.
    destruct zeq; intuition; simpl.
    replace (Int.signed Int.zero) with 0 in * by auto with ints.
    intuition.
    destruct zeq; intuition.
  - admit.
Admitted.

Require Import Clight.switch.

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


Definition f_spec :=
  DECLARE _f
    WITH x : Z
    PRE [ _x OF tuint ]
      PROP  (0 <= x <= Int.max_unsigned)
      LOCAL (temp _x (Vint (Int.repr x)))
      SEP ()
    POST [ tint ]
      PROP ()
      LOCAL (temp ret_temp (if (x =? 1) 
                            then Vint (Int.repr 2) 
                            else Vint (Int.repr 1)))
      SEP ().


Definition Gprog' : funspecs :=   ltac:(with_library prog [twice_spec]).

Lemma body_twice: semax_body Vprog Gprog' f_twice twice_spec.
Proof.
start_function.
forward_if (PROP() LOCAL(temp _n (Vint (Int.repr (n)))) SEP()).
repeat forward; entailer!.
repeat forward; entailer!.
repeat forward; entailer!.
repeat forward; entailer!.
repeat forward; entailer!.
repeat forward; entailer!.
Qed.

Lemma body_f: semax_body Vprog Gprog f_f f_spec.
Proof.
start_function.
forward_if (@FF (environ->mpred) _).
forward.
forward.
forward.
forward.
forward.
Qed.
