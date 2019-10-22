Require Import Coq.Program.Basics.
Require Import Clight.easy_ptr.
Require Import VST.floyd.proofauto.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope program_scope.

Definition ptr_leb (ptr1 ptr2 : ptrofs) := 
  Ptrofs.unsigned ptr1 <=? Ptrofs.unsigned ptr2.

Definition ptr_spec : ident * funspec :=
  DECLARE _ptr_test
    WITH b : block, ptr1 : ptrofs, ptr2 : ptrofs,
         sh : share, ch1 : Z, ch2 : Z
    PRE [_ptr1 OF (tptr tschar), _ptr2 OF (tptr tschar)]
      PROP(readable_share sh)
      LOCAL(temp _ptr1 (Vptr b ptr1);
            temp _ptr2 (Vptr b ptr2))
      SEP(data_at sh tschar (Vint (Int.repr ch1)) (Vptr b ptr1);
          data_at sh tschar (Vint (Int.repr ch2)) (Vptr b ptr2))
    POST [tint]
      PROP()
      LOCAL(temp ret_temp (Vint (Int.repr (if ptr_leb ptr1 ptr2 then 1 else 2))))
      SEP(data_at sh tschar (Vint (Int.repr ch1)) (Vptr b ptr1);
          data_at sh tschar (Vint (Int.repr ch2)) (Vptr b ptr2)).

Definition Gprog := ltac:(with_library prog [ptr_spec]).

Lemma typed_true_ptr_le : forall b ptr1 ptr2, 
        typed_true tint (force_val (sem_cmp_pp Cle (Vptr b ptr1) (Vptr b ptr2))) ->
        Ptrofs.unsigned ptr1 <=? Ptrofs.unsigned ptr2 = true.
Proof.
  intros.
  unfold typed_true, force_val, sem_cmp_pp in H.
  unfold Archi.ptr64, strict_bool_val in H.
  simpl in H.
  destruct eq_block in H; [simpl in H|contradiction].
  unfold negb, Ptrofs.ltu in H.
  destruct zlt in H; simpl in H; try discriminate.
  apply Z.ge_le in g.
  apply Zle_imp_le_bool.
  assumption.
Qed.

Lemma typed_false_ptr_le : forall b ptr1 ptr2, 
        typed_false tint (force_val (sem_cmp_pp Cle (Vptr b ptr1) (Vptr b ptr2))) ->
        Ptrofs.unsigned ptr2 <? Ptrofs.unsigned ptr1 = true.
Proof.
  intros.
  unfold typed_false, force_val, sem_cmp_pp in H.
  unfold Archi.ptr64, strict_bool_val in H.
  simpl in H.
  destruct eq_block in H; [simpl in H|contradiction].
  unfold negb, Ptrofs.ltu in H.
  destruct zlt in H; simpl in H; try discriminate.
  apply Fcore_Zaux.Zlt_bool_true.
  assumption.
Qed.

Lemma body_max: semax_body Vprog Gprog f_ptr_test ptr_spec.
Proof.
  start_function.
  forward_if.
  unfold test_order_ptrs.
  unfold sameblock.
  destruct peq; [simpl|contradiction].
  apply andp_right.
  -
    assert (data_at sh tschar (Vint (Int.repr ch1)) (Vptr b ptr1) * 
            data_at sh tschar (Vint (Int.repr ch2)) (Vptr b ptr2) 
                    |-- valid_pointer (Vptr b ptr1)) by entailer!.
    pose proof (valid_pointer_weak (Vptr b ptr1)).
    apply derives_trans with (Q := valid_pointer (Vptr b ptr1)); assumption.
  -
    assert (data_at sh tschar (Vint (Int.repr ch1)) (Vptr b ptr1) * 
            data_at sh tschar (Vint (Int.repr ch2)) (Vptr b ptr2) 
                    |-- valid_pointer (Vptr b ptr2)) by entailer!.
    pose proof (valid_pointer_weak (Vptr b ptr2)).
    apply derives_trans with (Q := valid_pointer (Vptr b ptr2)); assumption.
  - forward.
    pose proof typed_true_ptr_le b ptr1 ptr2 H.
    unfold ptr_leb.
    rewrite H4.
    entailer!.
  - forward.
    pose proof typed_false_ptr_le b ptr1 ptr2 H.
    unfold ptr_leb.
    rewrite Z.leb_antisym.
    rewrite H4.
    simpl.
    entailer!.
Qed.
    
