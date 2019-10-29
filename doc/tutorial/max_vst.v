Require Import Coq.Program.Basics.
Require Import Clight.max.
Require Import VST.floyd.proofauto.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope program_scope.

Definition max_spec : ident * funspec :=
  DECLARE _max
    WITH n1 : Z, n2 : Z
    PRE [_n1 OF tint, _n2 OF tint]
      PROP(Int.min_signed <= n1 <= Int.max_signed;
           Int.min_signed <= n2 <= Int.max_signed)
      LOCAL(temp _n1 ((Vint ∘ Int.repr) n1); 
            temp _n2 ((Vint ∘ Int.repr) n2))
      SEP()
    POST [ tint ]
      PROP()
      LOCAL(temp ret_temp ((Vint ∘ Int.repr) (Z.max n1 n2)))
      SEP().

Definition Gprog := ltac:(with_library prog [max_spec]).

Lemma body_max: semax_body Vprog Gprog f_max max_spec.
Proof.
  start_function.
  unfold compose in *; simpl.
  forward_if (
      PROP(Z.max n1 n2 = n1 \/ Z.max n1 n2 = n2)
      LOCAL(temp _res (Vint (Int.repr (Z.max n1 n2))))
      SEP()).
  1,2: forward; entailer!.
  rewrite Z.max_comm.
  unfold Z.max.
  apply Fcore_Zaux.Zcompare_Lt in H1.
  rewrite H1.
  auto.
  apply Z.ge_le in H1.
  rewrite Z.max_r.
  auto.
  assumption.
  Intros.
  forward.
Qed.
