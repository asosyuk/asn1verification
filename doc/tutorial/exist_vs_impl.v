Parameter A : Type.
Parameter P : A -> Prop.
Parameter Q : A -> Prop.

Definition spec__exist := exists a, P a /\ Q a.
Definition spec__impl  := forall a, P a -> Q a.

Section Exist_Impl.

  Hypothesis P_functional :
    forall a1 a2, P a1 -> P a2 -> a1 = a2.

  Goal spec__exist -> spec__impl.
  Proof.
    cbv.
    intros.
    destruct H as [a' H]; destruct H as [H1 H2].
    rewrite (P_functional a a') by assumption.
    assumption.
  Qed.

End Exist_Impl.


Section Impl_Exist.

  Hypothesis P_total :
    exists a, P a.

  Goal spec__impl -> spec__exist.
  Proof.
    cbv.
    intros.
    destruct P_total as [a H1].
    specialize (H a). exists a.
    split.
    - assumption.
    - apply H.
      assumption.
  Qed.

End Impl_Exist.
