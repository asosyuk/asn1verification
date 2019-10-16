Require Import Coq.Program.Basics Psatz.
Require Import StructTact.StructTactics.
Require Import Clight.factorial1.
Require Import VST.floyd.proofauto.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope program_scope.

Fixpoint fact (n : nat) : Z :=
  match n with
  | O => 1
  | S n' => (Z.of_nat n' + 1) * fact n'
  end.

Definition factZ (z : Z) : Z :=  fact (Z.to_nat z).

Definition factorial1_spec : ident * funspec :=
  DECLARE _factorial1
    WITH n : Z
    PRE [_input OF tuint]
      PROP(0 <= n <= Int.max_unsigned;
           0 <= factZ n <= Int.max_unsigned)
      LOCAL(temp _n ((Vint ∘ Int.repr) n))
      SEP()
    POST [tuint]
      PROP()
      LOCAL(temp ret_temp ((Vint ∘ Int.repr) (factZ n)))
      SEP().

Definition Gprog := ltac:(with_library prog [factorial1_spec]).

Lemma body_factorial1: semax_body Vprog Gprog f_factorial1 factorial1_spec.
Proof.
  start_function.
  abbreviate_semax.
  unfold compose in *; simpl.
  forward.
  forward.
  forward_while (
      EX i : Z,
        PROP( 0 <= i <= n)
        LOCAL(temp _i (Vint (Int.repr i));
              temp _n (Vint (Int.repr n));
              temp _out (Vint (Int.repr (factZ i))))
        SEP()).
  entailer.
  Exists 0.
  entailer!.
  entailer!.
  repeat forward.
  entailer!.
  repeat autorewrite with norm.
  Exists ((i + 1))%Z.
  entailer!.
  repeat f_equal.
  unfold factZ.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i))%nat.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i.                                      
  nia.
  rewrite Z2Nat.id; auto.
  nia.
  rewrite Z2Nat.inj_add.
  replace (Z.to_nat 1) with 1%nat by auto with zarith.
  all: try omega.
  forward.
  replace i with n by nia.
  entailer!.
Qed.

Require Import Clight.factorial.

Definition factorial_spec : ident * funspec :=
  DECLARE _factorial
    WITH n : Z
    PRE [_input OF tuint]
      PROP(0 <= n <= Int.max_unsigned;
           0 <= factZ n <= Int.max_unsigned)
      LOCAL(temp _input ((Vint ∘ Int.repr) n))
      SEP()
    POST [tuint]
      PROP()
      LOCAL(temp ret_temp ((Vint ∘ Int.repr) (factZ n)))
      SEP().

Definition Gprog' := ltac:(with_library prog [factorial_spec]).

Lemma body_factorial: semax_body Vprog Gprog' f_factorial factorial_spec.
Proof.
  start_function.
  abbreviate_semax.
  unfold compose in *; simpl.
  forward.
  forward_while (
      EX i : Z,
        PROP( 0 <= i <= n)
        LOCAL(temp _input (Vint (Int.repr (n - i)));
              temp _output (Vint (Int.divu (Int.repr (factZ n)) 
                                           (Int.repr (factZ (n - i))))))
        SEP()).
  entailer.
  Exists 0.
  entailer!.
  replace (n - 0) with n by Lia.nia.
  split.
  easy.
  f_equal.
  unfold Int.divu.
  f_equal.
  autorewrite with norm.
  assert (0 < factZ n).
  unfold factZ.
  induction (Z.to_nat n).
  1,2: simpl; try nia.
  eapply Z_div_same.
  nia.
  entailer!.
  forward.
  forward.
  repeat autorewrite with norm.
  entailer.
  Exists ((i + 1))%Z.
  entailer.
  entailer!.
  split.
  f_equal.
  f_equal.
  nia.
  f_equal.
  admit.
  forward.
  entailer!.
  replace i with n.
  replace (n - n) with 0 by nia.
  f_equal.
  unfold factZ.
  simpl.
  eapply Int.divu_one.  assert (n - i = 0).
   {
    replace (n - i) with (Int.unsigned (Int.repr (n - i))).
    replace (0) with (Int.unsigned Int.zero).
    f_equal.
    assumption.
    reflexivity.
    rewrite Int.unsigned_repr.
    reflexivity.
    Lia.lia.
  }
nia.
Admitted.
