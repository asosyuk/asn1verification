Require Import StructTact.StructTactics.
Require Import Core Notations Tactics IntLemmas PtrLemmas.

Proposition ptr_ge_to_sem_cmp_lt_false : forall m b1 b2 i1 i2,
    ptr_ge m b1 b2 i1 i2 = Some true ->
    sem_cmp Clt (Vptr b1 i1) (tptr tschar) (Vptr b2 i2) (tptr tschar) m = 
    Some Vfalse.
Proof.
  intros.
  apply sem_Clt_Cge_ptr.
  eapply ptr_ge_to_sem_cmp_true;
    assumption.
  Qed.

Proposition addr_lt_to_sem_cmp_lt : forall m b1 b2 i1 i2,
  addr_lt m (b1, i1) (b2, i2) = Some false ->
     (sem_cmp Clt (Vptr b1 i1) (tptr tschar)
              (Vptr b2 i2) (tptr tschar) m = Some Vfalse).
Admitted.

Proposition addr_lt_succ_to_sem_cmp_lt : forall m b1 b2 i1 i2,
  addr_lt m (b1,(i1 + 1)%ptrofs) (b2, i2) = Some false ->
     (sem_cmp Clt (Vptr b1 i1) (tptr tschar)
              (Vptr b2 i2) (tptr tschar) m = Some Vtrue).
Admitted.

Proposition dist_succ_to_sem_cmp_lt : forall dist m b1 b2 i1 i2,
    distance m (b1, i1) (b2, i2) = Some (S dist) ->
     (sem_cmp Clt (Vptr b1 i1) (tptr tschar)
              (Vptr b2 i2) (tptr tschar) m = Some Vtrue).
  Admitted.
