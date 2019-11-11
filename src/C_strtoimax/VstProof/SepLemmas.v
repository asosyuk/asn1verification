Require Import VST.floyd.proofauto.


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
    0 <= j <= Zlength ls ->
    Ptrofs.unsigned ofs + Zlength ls < Ptrofs.modulus ->

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

Lemma data_at_succ_sublist: forall (cs : compspecs) j i ls sh_str end'_b str_ofs,
data_at sh_str (tarray tschar j) (map Vbyte (sublist 0 j ls))
    (Vptr end'_b (Ptrofs.add str_ofs Ptrofs.one))
  |-- data_at sh_str (tarray tschar j) (map Vbyte (sublist 1 (j + 1) (i :: ls)))
  (Vptr end'_b (Ptrofs.add str_ofs Ptrofs.one)).
  Admitted.
