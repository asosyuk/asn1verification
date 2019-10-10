Require Import Coq.Program.Basics.
Require Import pow2.
Require Import VST.floyd.proofauto.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope program_scope.

Definition pow2_spec : ident * funspec :=
  DECLARE _pow2
    WITH n : Z
    PRE [_n OF tuint]
      PROP(0 <= n <= Int.max_unsigned;
           0 <= two_p n <= Int.max_unsigned)
      LOCAL(temp _n ((Vint ∘ Int.repr) n))
      SEP()
    POST [tuint]
      PROP()
      LOCAL(temp ret_temp ((Vint ∘ Int.repr) (two_p n)))
      SEP().

Definition Gprog := ltac:(with_library prog [pow2_spec]).

Lemma body_max: semax_body Vprog Gprog f_pow2 pow2_spec.
Proof.
  start_function.
  unfold compose in *; simpl.
  forward.
  forward_while (
      EX i : Z,
        PROP(0 <= i; i <= n; 0 <= two_p n <= Int.max_unsigned)
        LOCAL(temp _n (Vint (Int.repr (n - i)));
              temp _res (Vint (Int.repr (two_p i))))
        SEP()).
  entailer!.
  Exists 0.
  entailer!.
  now (replace (n - 0) with n by Lia.lia).
  entailer!.
  forward.
  autorewrite with norm.
  forward.
  autorewrite with norm.
  entailer!.
  Exists (i + 1).
  entailer!.
  rewrite Z.sub_add_distr.
  replace (two_p (i + 1)) with ((two_p i) + (two_p i)).
  easy.
  rewrite two_p_is_exp.
  replace (two_p 1) with 2 by reflexivity.
  rewrite Z.mul_comm; rewrite <-Z.add_diag.
  reflexivity.
  assumption.
  Lia.lia.
  forward.
  entailer!.
  assert (n - i = 0).
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
  apply Zminus_eq in H4.
  rewrite  H4.
  reflexivity.
Qed.
