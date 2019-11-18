Require Import VST.floyd.proofauto Psatz.
Require Import StructTact.StructTactics Psatz.

Proposition sublist_first : forall (A : Type) j (ls : list A),
    Inhabitant A ->
    0 <= j < Zlength ls ->
    0 < Zlength (sublist j (Zlength ls) ls) ->
    exists i : A, (sublist j (Zlength ls) ls) = 
             i :: (sublist (j + 1) (Zlength ls) ls). 
Proof.
  intros.
  eexists.
  rewrite sublist_split with (mid := j + 1).
  erewrite sublist_len_1.
  reflexivity.
  eassumption.
  nia.
  nia.
Qed.

Lemma split2_data_at_Tarray_tschar {cs: compspecs} sh n n1 (v: list val) p:
   0 <= n1 <= n ->
   Zlength v = n ->
   data_at sh (Tarray tschar n noattr) v p =
    data_at sh (Tarray tschar n1 noattr) (sublist 0 n1 v) p *
    data_at sh (Tarray tschar (n - n1) noattr) (sublist n1 n v) (field_address0 (Tarray tschar n noattr) (ArraySubsc n1::nil) p).
Proof. intros.
 eapply split2_data_at_Tarray; auto.
 symmetry in H0.
 list_solve.
 rewrite sublist_same; try omega; auto.
Qed.


Lemma split_data_at_sublist_tschar : forall (cs : compspecs) sh ls b ofs j,
    Ptrofs.unsigned ofs + Zlength ls < Ptrofs.modulus ->
    0 <= j <= Zlength ls ->

    data_at sh (tarray tschar (Zlength ls)) (map Vbyte ls) (Vptr b ofs) =
    data_at sh (tarray tschar j) (map Vbyte (sublist 0 j ls))
            (Vptr b ofs) *
    data_at sh (tarray tschar (Zlength ls - j)) (map Vbyte (sublist j (Zlength ls) ls))
            (Vptr b (Ptrofs.add ofs (Ptrofs.repr j))).
Proof.
  intros.
  unfold tarray.
  erewrite  split2_data_at_Tarray_tschar with (n1 := j).
  replace (field_address0 (Tarray tschar (Zlength ls) noattr) [ArraySubsc j] (Vptr b ofs))
    with (Vptr b (Ptrofs.add ofs (Ptrofs.repr j))).
  repeat erewrite  sublist_map.
  easy.
  { 
    rewrite field_address0_offset.
    simpl.
    normalize.
    econstructor.
    easy.
    repeat split.
    simpl; autorewrite with norm.
    eassumption.
    constructor.
    intros.
    repeat econstructor.
    simpl; autorewrite with norm.
    reflexivity.
    all: try Lia.nia || auto with zarith. }
  eassumption.
  autorewrite with sublist; reflexivity.
Qed.


Arguments valid_pointer p : simpl never.

Proposition split_non_empty_list (cs : compspecs) i ls' ls sh b ofs:
      ls = i::ls'  -> Ptrofs.unsigned ofs + Zlength ls < Ptrofs.modulus -> 
      data_at sh (tarray tschar (Zlength ls)) (map Vbyte ls) (Vptr b ofs) =
      data_at sh tschar (Vbyte i) (Vptr b ofs) *
      data_at sh (tarray tschar (Zlength ls')) (map Vbyte ls')
              (Vptr b (Ptrofs.add ofs Ptrofs.one)).
Proof.
  intros LEN MOD.
  rewrite LEN.
  rewrite semax_lemmas.cons_app with (x := i).
  rewrite map_app. 
  rewrite split2_data_at_Tarray_app with (mid := 1).
  assert (map Vbyte [i] = [Vbyte i]) as T by reflexivity.
  pose proof data_at_singleton_array_eq sh tschar (Vbyte i) 
       (map Vbyte [i]) (Vptr b ofs) T as T1; rewrite T1; clear T T1.

  assert (Vptr b (Ptrofs.add ofs Ptrofs.one) =
          field_address0 (tarray tschar (Zlength (app [i] ls'))) [ArraySubsc 1]
                         (Vptr b ofs))
    as J.
  { 
    rewrite field_address0_offset.
    reflexivity.
    econstructor.
    easy.
    repeat split.
    simpl; autorewrite with norm.
    rewrite <- LEN.
    eassumption.
    constructor.
    intros.
    repeat econstructor.
    simpl; autorewrite with norm.
    reflexivity.
    all: try nia || auto with zarith.
    autorewrite with sublist.
    simpl.
    pose proof (Zlength_nonneg ls').
    nia.
  }
  rewrite J.
  replace (Zlength (app [i] ls') - 1) with (Zlength ls').
  reflexivity.
  all: try autorewrite with sublist; auto.
Qed.


Lemma typed_true_ptr_ge : forall b ptr1 ptr2, 
    typed_true tint (force_val (sem_cmp_pp Cge (Vptr b ptr1) (Vptr b ptr2))) ->
    Ptrofs.unsigned ptr1 >=? Ptrofs.unsigned ptr2 = true.
Proof.
  intros.
  unfold typed_true, force_val, sem_cmp_pp in H; simpl in H.
  destruct eq_block in H; [simpl in H|discriminate].
  unfold Ptrofs.ltu in H.
  destruct zlt in H; [discriminate|simpl in H].
  rewrite Z.geb_le.
  Lia.lia.
Qed.

Lemma typed_false_ptr_ge : forall b ptr1 ptr2,
    typed_false tint (force_val (sem_cmp_pp Cge (Vptr b ptr1) (Vptr b ptr2))) ->
    Ptrofs.unsigned ptr2 >? Ptrofs.unsigned ptr1 = true.
Proof.
  intros.
  unfold typed_false, force_val, sem_cmp_pp in H; simpl in H.
  destruct eq_block in H; [simpl in H|discriminate].
  unfold Ptrofs.ltu in H.
  destruct zlt in H; [simpl in H|discriminate].
  rewrite Z.gtb_lt.
  Lia.lia.
Qed.


Lemma typed_true_ptr_lt : forall b ptr1 ptr2, 
    typed_true tint (force_val (sem_cmp_pp Clt (Vptr b ptr1) (Vptr b ptr2))) ->
    Ptrofs.unsigned ptr1 < Ptrofs.unsigned ptr2.
Proof.
  intros.
  unfold typed_true, force_val, sem_cmp_pp in H; simpl in H.
  destruct eq_block in H; [simpl in H|discriminate].
  unfold Ptrofs.ltu in H.
  destruct zlt in H; try (discriminate || simpl in H).
  auto.
Qed.

Lemma typed_false_ptr_lt : forall b ptr1 ptr2, 
    typed_false tint (force_val (sem_cmp_pp Clt (Vptr b ptr1) (Vptr b ptr2))) ->
    Ptrofs.unsigned ptr1 >= Ptrofs.unsigned ptr2.
Proof.
  intros.
  unfold typed_true, force_val, sem_cmp_pp in H; simpl in H.
  destruct eq_block in H; [simpl in H|discriminate].
  unfold Ptrofs.ltu in H.
  destruct zlt in H; try (discriminate || simpl in H).
  auto.
Qed.

Ltac rewrite_comparison :=
  match goal with 
  | [H : context[typed_true] |- _ ] => (eapply typed_false_ptr_lt in H||
                                           eapply typed_true_ptr_lt in H ||
                                           eapply typed_false_ptr_ge in H ||
                                           eapply typed_true_ptr_ge in H)
 | [H : context [typed_false] |- _ ] => (eapply typed_false_ptr_lt in H||
                                           eapply typed_true_ptr_lt in H ||
                                           eapply typed_false_ptr_ge in H ||
                                           eapply typed_true_ptr_ge in H)
  end.
                                    


Proposition Zge_bool_Intge : 
  forall i, (Byte.signed i <=? 57) = (negb (Int.lt (Int.repr 57)
                                              (Int.repr (Byte.signed i)))).
Proof.
  intros.
  unfold Int.lt.
  break_if; try easy.
  destruct (Byte.signed i <=? 57) eqn : I57.
  eapply Zle_bool_imp_le in I57.
  autorewrite with norm in l.
  nia.
  easy.
  destruct (Byte.signed i <=? 57) eqn : I57.
  eapply Zle_bool_imp_le in I57.
  autorewrite with norm in g.
  easy.

  eapply Z.leb_gt in I57.
  autorewrite with norm in g.
  nia.
Qed.

