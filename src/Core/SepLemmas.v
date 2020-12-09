Require Import VST.floyd.proofauto Psatz.
Require Import StructTact.StructTactics Psatz Core.Notations.


Lemma default_val_app :
  forall { cs : compspecs } t l1 l2, 
               (default_val (tarray t l1) ++
                default_val (tarray t l2)) = default_val (tarray t (l1 + l2)).
Admitted.  

Lemma valid_pointer_weak_minus:
 forall a, valid_pointer a |-- weak_valid_pointer (offset_val 1 a).
Proof.
intros.
unfold valid_pointer, weak_valid_pointer.
change predicates_hered.orp with orp. (* delete me *)
apply orp_right2.
Admitted.

Lemma upd_Znth_idem: forall {A} j ls (a b : A),
                 0 <= j < len ls ->           
                 
                 upd_Znth j (upd_Znth j ls b) a = upd_Znth j ls a.
Proof.
 intros.
 erewrite upd_Znth_unfold.
 erewrite sublist_upd_Znth_l.
 erewrite sublist_upd_Znth_r.
 erewrite upd_Znth_Zlength.
 erewrite upd_Znth_unfold.
 auto.
 all: try nia.
 erewrite upd_Znth_Zlength; try nia.
 erewrite upd_Znth_Zlength; try nia. 
Qed.

Lemma Zlength_default_val : forall {cs} n t, 
    0 <= n -> 
    len (@default_val cs (tarray t n)) = n.
Proof.
  intros.
  unfold default_val; simpl. rewrite Zlength_list_repeat; trivial. 
Qed.

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
Proof. 
  intros.
  eapply split2_data_at_Tarray; auto.
  rewrite <-H0.
  reflexivity.
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


Lemma split_data_at_sublist_tuchar : forall (cs : compspecs) sh ls b ofs j,
    Ptrofs.unsigned ofs + Zlength ls < Ptrofs.modulus ->
    0 <= j <= Zlength ls ->
    data_at sh (tarray tuchar (Zlength ls)) ls (Vptr b ofs) =
    data_at sh (tarray tuchar j) (sublist 0 j ls)
            (Vptr b ofs) *
    data_at sh (tarray tuchar (Zlength ls - j)) (sublist j (Zlength ls) ls)
            (Vptr b (Ptrofs.add ofs (Ptrofs.repr j))).
Proof.
  intros.
  unfold tarray.
  erewrite  split2_data_at_Tarray_tuchar with (n1 := j).
  replace (field_address0 (Tarray tuchar (Zlength ls) noattr) [ArraySubsc j] (Vptr b ofs))
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

Lemma combine_data_at_sublist_tuchar :
  forall (cs : compspecs) sh ls ls1 ls2 b ofs j,
    (Ptrofs.unsigned ofs + Zlength ls < Ptrofs.modulus)%Z ->
    0 <= j <= Zlength ls ->
    sublist 0 j ls = ls1 ->
    sublist j (Zlength ls) ls = ls2 ->
    Zlength ls1 = j ->
    data_at sh (tarray tuchar (Zlength ls)) ls (Vptr b ofs) =
    data_at sh (tarray tuchar j) ls1 (Vptr b ofs) *
     data_at sh (tarray tuchar (Zlength ls - j)) ls2
             (Vptr b (Ptrofs.add ofs (Ptrofs.repr j))).
Proof.
  intros.
  erewrite split_data_at_sublist_tuchar with (j := j).
  replace (sublist 0 j ls) with ls1.
  replace (sublist j (Zlength ls) ls) with ls2.
  all: auto.
Qed.

Arguments valid_pointer p : simpl never.

Proposition split_non_empty_list (cs : compspecs) i ls' ls sh b ofs j1 j2:
      ls = i::ls' -> 
      (Ptrofs.unsigned ofs + Zlength ls < Ptrofs.modulus)%Z ->
      j1 = Zlength ls ->
      j2 = Zlength ls' ->
      data_at sh (tarray tuchar j1) ls (Vptr b ofs) =
     (data_at sh tuchar i (Vptr b ofs) *
      data_at sh (tarray tuchar j2) ls' (Vptr b (ofs + 1)%ptrofs))%logic.
Proof.
  intros LEN MOD J1 J2.
  rewrite LEN.
  replace (i::ls') with ([i] ++ ls') by reflexivity.
  rewrite split2_data_at_Tarray_app with (mid := 1%Z).
  pose proof data_at_singleton_array_eq sh tuchar i 
       [i] (Vptr b ofs)  as T1; rewrite T1; clear T1.

  assert (Vptr b (ofs + 1)%ptrofs =
          field_address0 (tarray tuchar (Zlength (app [i] ls'))) [ArraySubsc 1]
                         (Vptr b ofs))
    as J.
  { 
    rewrite field_address0_offset.
    reflexivity.
    econstructor.
    easy.
    repeat split.
    simpl; autorewrite with norm.
    rewrite LEN in *.
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
    assert (1 <= 1 + len ls')%Z by nia.
    eassumption.
  }
  rewrite J.
  subst.
  replace (Zlength (i :: ls') - 1)%Z with (Zlength ls').
  reflexivity.
  all: try autorewrite with sublist; auto.
  nia.
  subst.
  try autorewrite with sublist.
  assert (len ls' = (Z.succ (len ls') - 1)%Z) by nia.
  eassumption.
Qed.

Proposition split_non_empty_list_tuchar (cs : compspecs) i ls' ls sh b ofs:
      ls = i::ls'  -> Ptrofs.unsigned ofs + Zlength ls < Ptrofs.modulus -> 
      data_at sh (tarray tuchar (Zlength ls)) (map Vbyte ls) (Vptr b ofs) =
      data_at sh tuchar (Vbyte i) (Vptr b ofs) *
      data_at sh (tarray tuchar (Zlength ls')) (map Vbyte ls')
              (Vptr b (Ptrofs.add ofs Ptrofs.one)).
Proof.
  intros LEN MOD.
  rewrite LEN.
  replace (i::ls') with ([i] ++ ls') by reflexivity.
  rewrite map_app. 
  rewrite split2_data_at_Tarray_app with (mid := 1).
  assert (map Vbyte [i] = [Vbyte i]) as T by reflexivity.
  pose proof data_at_singleton_array_eq sh tuchar (Vbyte i) 
       (map Vbyte [i]) (Vptr b ofs) T as T1; rewrite T1; clear T T1.

  assert (Vptr b (Ptrofs.add ofs Ptrofs.one) =
          field_address0 (tarray tuchar (Zlength (app [i] ls'))) [ArraySubsc 1]
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


Lemma data_at_app : forall (cs : compspecs) sh ls1 ls2 b ofs j1 j2,
    j1 = Zlength ls1 ->
    j2 = Zlength ls2 ->
    Ptrofs.unsigned ofs + (len ls1 + len ls2) < Ptrofs.modulus ->
    data_at sh (tarray tuchar (j1 + j2)) (ls1 ++ ls2) (Vptr b ofs) =
   (data_at sh (tarray tuchar j1) ls1 (Vptr b ofs) *
    data_at sh (tarray tuchar j2) ls2 (Vptr b (ofs + (Ptrofs.repr j1))%ptrofs))%logic.
Proof.
intros until j2.
intros J1 J2 Ptr.
assert (ls1 = sublist 0 (len ls1) (ls1 ++ ls2)) by (autorewrite with sublist; auto).
assert (ls2 = sublist (len ls1) (len (ls1 ++ ls2)) (ls1 ++ ls2)) 
  by (autorewrite with sublist; auto).
subst.
replace (len ls1 + len ls2)%Z with (len (ls1 ++ ls2)). 
erewrite combine_data_at_sublist_tuchar with (j := (len ls1))
                                             (ls1 := ls1)
                                             (ls2 := ls2)
                                             (ls := ls1 ++ ls2).
replace (len (ls1 ++ ls2) - len ls1)%Z with (len ls2).
auto.
all: try list_solve.
autorewrite with sublist; auto.
autorewrite with sublist; auto.
Qed.

Lemma data_at_app_gen : forall (cs : compspecs) sh ls1 ls2 ls b ofs j1 j2 j,
    j1 = Zlength ls1 ->
    j2 = Zlength ls2 ->
    j = j1 + j2 ->
    ls = ls1 ++ ls2 ->
    Ptrofs.unsigned ofs + (len ls1 + len ls2) < Ptrofs.modulus ->
    data_at sh (tarray tuchar j) ls (Vptr b ofs) =
   (data_at sh (tarray tuchar j1) ls1 (Vptr b ofs) *
    data_at sh (tarray tuchar j2) ls2 (Vptr b (ofs + (Ptrofs.repr j1))%ptrofs))%logic.
Proof.
intros until j.
intros J1 J2 J LS Ptr.
assert (ls1 = sublist 0 (len ls1) (ls1 ++ ls2)) by (autorewrite with sublist; auto).
assert (ls2 = sublist (len ls1) (len (ls1 ++ ls2)) (ls1 ++ ls2)) 
  by (autorewrite with sublist; auto).
subst.
replace (len ls1 + len ls2)%Z with (len (ls1 ++ ls2)). 
erewrite combine_data_at_sublist_tuchar with (j := (len ls1))
                                             (ls1 := ls1)
                                             (ls2 := ls2)
                                             (ls := ls1 ++ ls2).
replace (len (ls1 ++ ls2) - len ls1)%Z with (len ls2).
auto.
all: try list_solve.
autorewrite with sublist; auto.
autorewrite with sublist; auto.
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
                                    

