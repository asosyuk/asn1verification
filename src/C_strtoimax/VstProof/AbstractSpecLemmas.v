Require Import Core.Core Core.Tactics.
Require Import AbstractSpec.
Require Import VST.floyd.proofauto.
Require Import StructTact.StructTactics.

 Definition value_until j l := 
             (value (Z_of_string_loop (sublist 0 j l) 0 1)).

Definition ASN1_INTMAX_MAX := Int64.max_signed.
Definition upper_boundary := Z.div ASN1_INTMAX_MAX 10.
Definition last_digit_max := Zmod ASN1_INTMAX_MAX 10.
Definition last_digit_max_minus := last_digit_max + 1.

(* Lemmas about bounded *)
Ltac Zbool_to_Prop := try (rewrite Z.leb_le ||  rewrite Z.eqb_eq ||
                           rewrite Z.eqb_neq).

Lemma is_digit_to_Z : forall c, is_digit c = true -> 0 <= Z_of_char c <= 9.
Proof.
  unfold is_digit, Z_of_char.
  intro.
  rewrite andb_true_iff in *.
  repeat Zbool_to_Prop.
  unfold zero_char, nine_char.
  nia.
Qed.

Lemma sign_not_digit : forall  i, is_sign i = true -> is_digit i = false.
Proof.
  intros.
  unfold is_sign, is_digit in *.
  unfold zero_char, plus_char, minus_char, nine_char in *.
  rewrite andb_false_iff; do 2 rewrite Z.leb_gt.
  rewrite orb_true_iff in H; do 2 rewrite Z.eqb_eq in H.
  lia.
Qed.

Lemma digit_not_sign : forall i, is_digit i = true -> is_sign i = false.
Proof.
  intros.
  unfold is_sign, is_digit in *.
  unfold zero_char, plus_char, minus_char, nine_char in *.
  rewrite orb_false_iff; do 2 rewrite Z.eqb_neq.
  rewrite andb_true_iff in H; do 2 rewrite Z.leb_le in H.
  lia.
Qed.

Lemma bounded_bool_to_Prop :
  forall v, bounded v = true ->  
       Int64.min_signed <= v <= Int64.max_signed.
Proof.
  unfold bounded.
  intro.
  rewrite andb_true_iff in *.
  repeat Zbool_to_Prop.
  auto.
Qed.

Lemma lt_inv64:
 forall i j,
   Int64.lt i j = true -> (Int64.signed i < Int64.signed j)%Z.
Proof.
intros.
unfold Int64.lt in H. if_tac in H; inv H. auto.
Qed.


Lemma lt_ub_to_next_bounded_bool : forall v d,
    0 <= d <= 9 -> 
    0 <= v < upper_boundary -> 
    bounded (v*10 + d) = true /\
    bounded (v*10) = true /\
    bounded v = true.
Proof.
  unfold upper_boundary.
  unfold bounded.
  intros.
  repeat rewrite andb_true_iff in *.
  repeat Zbool_to_Prop.
  cbn in *.
  nia.
Qed.

Lemma lt_ub_to_bounded_Prop : forall v d,
    0 <= d <= 9 -> (* is digit *)
    0 <= v < upper_boundary -> 
    Int64.min_signed <= v <= Int64.max_signed.
Proof.
  unfold upper_boundary.
  unfold bounded.
  intros.
  cbn in *.
  nia.
Qed.

Lemma lt_ub_to_next_bounded_Prop : forall v d,
    0 <= d <= 9 -> (* is digit *)
    0 <= v < upper_boundary -> 
    Int64.min_signed <= v * 10 + d <= Int64.max_signed /\
    Int64.min_signed <= v * 10 <= Int64.max_signed. 
Proof.
  unfold upper_boundary.
  unfold bounded.
  intros.
  cbn in *.
  nia.
Qed.


Definition upper_boundary_int := (
         (Int64.divs
            (Int64.shru (Int64.not (Int64.repr (Int.signed (Int.repr 0))))
                        (Int64.repr (Int.unsigned (Int.repr 1))))
            (Int64.repr (Int.signed (Int.repr 10))))).

Lemma lt_ub_to_Z1 : forall v,
    Int64.min_signed <= v <= Int64.max_signed ->
    Int64.lt (Int64.repr v) upper_boundary_int = true ->
    v < upper_boundary.
  Proof.
    intros v B Lt.
    eapply lt_inv64 in Lt.
  rewrite Int64.signed_repr in *.
  replace (Int64.signed upper_boundary_int) with upper_boundary
   in Lt by normalize.
  all: eassumption.
Qed.

Lemma upper_boundary_int_repr:
  upper_boundary_int = 
  Int64.repr 922337203685477580.
Proof.
  reflexivity.
Qed.

Lemma lt_ub_to_Z2 :  forall v,
    Int64.min_signed <= v <= Int64.max_signed ->
    Int64.lt (Int64.repr v) upper_boundary_int = false ->
    v >= upper_boundary.
Proof.
  intros.
  cbn in *.
  unfold Int64.lt in H0.
  destruct zlt in H0; [discriminate|].
  rewrite upper_boundary_int_repr in g.
  do 2 rewrite Int64.signed_repr in g; cbn; lia.
Qed.

Lemma lt_ub_to_Z3 :  forall v,
    0 <= v <= Int64.max_unsigned ->
    Int64.eq (Int64.repr v) upper_boundary_int = true ->
    v = upper_boundary.
Proof.
  intros.
  unfold Int64.eq in H0.
  destruct zeq in H0; [|discriminate].
  rewrite upper_boundary_int_repr in e.
  replace (Int64.unsigned (Int64.repr 922337203685477580)) 
    with 922337203685477580 in e by reflexivity.
  rewrite Int64.unsigned_repr in e; cbn in *; lia.
Qed.

Definition last_digit_max_minus_int :=
   (Int64.add
      (Int64.mods (Int64.shru (Int64.not (Int64.repr 0)) 
                              (Int64.repr 1)) 
                  (Int64.repr 10)) 
      Int64.one).

Lemma last_digit_max_minus_int_repr :
  last_digit_max_minus_int =
  Int64.repr (8).
Proof.
  reflexivity.
Qed.

Lemma lt_ub_to_Z4 :  forall v i, 
    Int64.min_signed <= v <= Int64.max_signed -> 
    Int64.lt last_digit_max_minus_int 
             (Int64.repr (Int.signed (Int.sub (Int.repr (Byte.signed i)) 
                                              (Int.repr 48)))) = true -> 
    last_digit_max_minus < (Byte.signed i - 48).
Proof.
Admitted.

Lemma lt_ub_to_Z5 :  forall v,
    Int64.min_signed <= v <= Int64.max_signed ->
    Int64.eq (Int64.repr v) upper_boundary_int = false ->
    v <> upper_boundary.
Admitted.

Lemma eq_ub_not_bounded_minus : forall v d,
    0 <= v ->
    0 <= d <= 9 -> 
    v = upper_boundary ->
    d > last_digit_max_minus ->
    bounded (v*10 + d) = false.
Proof.
  intros.
  unfold bounded; cbn in *.
  rewrite andb_false_iff; do 2 rewrite Z.leb_gt.
  lia.
Qed.

Ltac lt_ub_to_Z H := try (eapply lt_ub_to_Z1 in H ||
                            eapply lt_ub_to_Z2 in H ||
                               eapply lt_ub_to_Z3 in H ||
                                 eapply lt_ub_to_Z4 in H ||
                                  eapply lt_ub_to_Z5 in H).

Lemma lt_ub_bounded_Prop : forall v d,
    0 <= d <= 9 ->
    0 <= v ->
    Int64.min_signed <= v <= Int64.max_signed ->
    Int64.lt (Int64.repr v) upper_boundary_int = true ->
    Int64.min_signed <= v * 10 + d <= Int64.max_signed /\ 
    Int64.min_signed <= v * 10 <= Int64.max_signed.
Proof.
  intros v d D V V' Lt.
  eapply lt_ub_to_next_bounded_Prop.
  eassumption.
  eapply lt_inv64 in Lt.
  rewrite Int64.signed_repr in *.
  replace (Int64.signed upper_boundary_int) with upper_boundary
   in Lt by normalize.
  all: nia.
Qed.

Lemma neg_bounded : forall v, 
    0 <= v -> 
    bounded v = true -> bounded (-1 * v) = true.
  Proof.
    unfold bounded.
    cbn.
    intros v H.
     repeat rewrite andb_true_iff in *.
     repeat rewrite Z.leb_le in *;
    try nia.
Qed.

                   
  Lemma lt_ub_not_bounded : forall v d,
      0 <= v ->
      0 <= d <= 9 -> 
      v > upper_boundary ->
      bounded (v*10 + d) = false.
  Admitted.          

  Lemma eq_ub_bounded_minus : forall v d,
      0 <= v ->
      0 <= d <= 9 -> 
      v = upper_boundary ->
      d <= last_digit_max_minus ->
      bounded (v*10 + d) = true.
  Admitted.


(* Lemmas about Spec *) 

(* ERROR RANGE *)

Lemma ERROR_RANGE_not_bounded_loop : forall ls v i,
  res (Z_of_string_loop ls v i) = ERROR_RANGE ->
  bounded (value (Z_of_string_loop ls v i)) = false.
Proof.
  induction ls; intros v i.
  - discriminate.
  - cbn.
 repeat break_match;
      simpl; try congruence.
    eapply IHls; intuition.
Qed.

 Lemma sublist_ERROR_RANGE : forall ls v k j i, 
     0 <= j < Zlength ls ->
     0 <= k < j ->
     res (Z_of_string_loop (sublist k j ls) v i) = ERROR_RANGE ->
     res (Z_of_string_loop ls v i) = ERROR_RANGE.
 Proof.
   induction ls; intros v k j  i.
   -  admit.
   - replace (sublist k j (a :: ls)) with (a :: sublist (k + 1) j ls). 
     simpl.
     repeat break_if;
       simpl; try congruence.
     
     intros. eapply IHls with (j := j) (k := k + 1).
     all: try nia.
     admit.
     admit.
     eassumption.
     admit.
 Admitted.

 Lemma ERROR_RANGE_index : forall ls v i j,
     0 <= j + 1 < Zlength ls ->
     res (Z_of_string_loop ls v i) = ERROR_RANGE -> 
     bounded (value_until j ls) = true ->
     bounded (value_until (j + 1) ls) = false -> 
     index (Z_of_string_loop ls v i) = j + i.
 Admitted.
 
(* OK *)

Lemma all_digits_OK_or_ERROR_RANGE_loop : forall ls v i,
    (forall i, 0 <= i < Zlength ls -> is_digit (Znth i ls)  = true) ->
    res (Z_of_string_loop ls v i) = OK \/
    res (Z_of_string_loop ls v i) = ERROR_RANGE.
Proof.
  induction ls; intros v i DIG.
  - autorewrite with sublist in *.
    auto.
  - simpl.
    + replace (is_digit a) with true.
      break_if.
      eapply IHls.
      (* from DIG *)
      admit.
      auto.
      (* from DIG *)
      admit.
Admitted.



Lemma OK_index_loop : forall ls v i,
  res (Z_of_string_loop ls v i) = OK -> index (Z_of_string_loop ls v i) = i + Zlength ls.
Proof.
   induction ls; intros v i.
  - intuition.
  - simpl.
    repeat break_match;
      autorewrite with sublist;
      simpl; try congruence.
    replace (i + Z.succ (Zlength ls)) with
        ((i+1) + Zlength ls) by nia.
    eapply IHls; intuition.
Qed.

Lemma OK_index : forall ls,
    res (Z_of_string ls) = OK -> index (Z_of_string ls) = Zlength ls.
  Proof.
    destruct ls.
    - intuition.
    - simpl.
      break_if.
      * repeat break_if;
        simpl;
        autorewrite with sublist;
        try congruence; try nia.
      * repeat break_if.
        all: replace (Zlength (i :: i0 :: l))
                     with (1 + Zlength (i0::l)).
        all: try eapply OK_index_loop.
        all: autorewrite with sublist;
        try nia; simpl; easy.
Qed.


Lemma bounded_to_OK_loop : forall ls v i,
  0 < Zlength ls ->
  bounded (value (Z_of_string_loop ls v i)) = true ->
  (forall i, 0 <= i < Zlength ls -> is_digit (Znth i ls)  = true) ->
  res (Z_of_string_loop ls v i) = OK.
Proof.
  intros.
  edestruct all_digits_OK_or_ERROR_RANGE_loop with (ls := ls)
  as [OK | ER];
    intuition;
    try eassumption.
  eapply ERROR_RANGE_not_bounded_loop in ER.
  congruence.
Qed.

 Lemma OK_bounded_loop : forall ls v i,
     bounded v = true ->
     res (Z_of_string_loop ls v i) = OK ->
     bounded (value (Z_of_string_loop ls v i)) = true.
 Proof.
   induction ls; intros v i.
   - simpl; congruence.
   - cbn.
     repeat break_match;
       simpl; try congruence.
     intros. eapply IHls.
     all: intuition.
 Qed.
 

Lemma app_char_to_OK_loop : forall ls i,
    0 < Zlength ls ->
    is_sign i = true ->
    res (Z_of_string_loop ls 0 1) = OK ->
    res (Z_of_string (i :: ls)) = OK.
Proof.
  intros until i. intros N S Ok.
  pose proof (sign_not_digit i S).
  unfold is_sign in S.
  destruct_orb_hyp.
  all:
  simpl;
    repeat break_if; autorewrite with sublist in *;
      try nia;
    try eapply sign_not_digit in S;
    intuition; try congruence.
  Qed.

         

(* EXTRA DATA *)

Lemma EXTRA_DATA_index :
  forall ls v k j i, 
    0 <= j < Zlength ls ->
    Znth j ls = i -> 
    is_digit i = false -> 
    bounded (value_until j ls) = true ->
    index (Z_of_string_loop ls v k) = j + k.
Proof.
   induction ls; intros v k j i N Dig Bound.
  - autorewrite with sublist in *.
    nia.
  - simpl.
    repeat break_if.

Admitted. (* FIX *)

Lemma EXTRA_DATA_ER_result :
  forall ls v k j i, 
    0 <= j < Zlength ls ->
    Znth j ls = i -> 
    is_digit i = false -> 
    res (Z_of_string_loop ls v k) = EXTRA_DATA \/
    res (Z_of_string_loop ls v k) = ERROR_RANGE.
Proof.
  induction ls; intros v k j i N Dig Bound.
  - autorewrite with sublist in *.
    nia.
  - simpl.
    repeat break_if.
    eapply IHls.
    instantiate (1 := j - 1).
    autorewrite with sublist in *.
    auto with zarith.
    admit.
    instantiate (1 := i).
    (* from DIG *)
    admit.
Admitted.
      
Lemma eq_ub_bounded_plus : forall v d, 
      0 <= v ->
      0 <= d <= 9 -> 
      v = upper_boundary ->
      d <= last_digit_max ->
      bounded (v*10 + d) = true.
Proof.
  intros.
  unfold bounded; cbn in *.
  rewrite andb_true_iff; do 2 rewrite Z.leb_le.
  lia.
Qed.

Lemma eq_ub_not_bounded_plus : forall v d, 
    0 <= v ->
    0 <= d <= 9 -> 
    v = upper_boundary ->
    d > last_digit_max ->
    bounded (v*10 + d) = false.
Proof.
  intros.
  unfold bounded; cbn in *.
  rewrite andb_false_iff; do 2 rewrite Z.leb_gt.
  lia.
Qed.

Lemma loop_non_neg : forall ls v i, 0 <= v -> 0 <= value (Z_of_string_loop ls v i).
  Proof.
    induction ls.
    - intuition.
    - intros.
      simpl;
        repeat break_if;
      simpl; try congruence;
         eapply is_digit_to_Z in Heqb.
      eapply IHls.
      all: nia.
Qed.
                                  
Lemma value_next_loop : forall ls v i b,
    is_digit b = true ->
    (res (Z_of_string_loop ls v i)) = OK ->
    is_digit b = true ->
    value (Z_of_string_loop (ls ++ [b]) v i) = 
    (value (Z_of_string_loop ls v i)) * 10 + (Z_of_char b).
Proof.
  induction ls; intros.
  * simpl in *.
    repeat bool_rewrite.
    break_if; easy.
  * simpl.
    break_if.
    break_if.
    erewrite IHls.
    reflexivity.
    eassumption.
    all: simpl in *;
    repeat break_if;
      try congruence; simpl in *;
    try congruence.
Qed.

Lemma next_value_lt_ub : forall ls j i,
     (forall i : Z, 0 <= i < j  ->
               is_digit (Znth i ls) = true) ->
     0 < j + 1 <= Zlength ls ->
     bounded (value_until j ls) = true -> 
     Znth j ls = i ->
     is_digit i = true ->
     (value_until (j + 1) ls) = (value_until j ls * 10 + (Z_of_char i)).
Proof.
  unfold value_until.
  intros.
  rewrite sublist_last_1.
  subst.
  eapply value_next_loop.
  eassumption.
  eapply bounded_to_OK_loop.
  admit.
  eassumption.
  admit.
  eassumption.
  all: nia.
Admitted.

Lemma ub_last_digit_error_range : forall j i ls,
  0 <= j < Zlength ls ->
  Znth j ls = i ->
  is_digit i = true ->
  (forall i0 : Z, 0 <= i0 < j -> is_digit (Znth i0 ls) = true) ->
  bounded (value_until j ls) = true ->
  (value_until j ls > upper_boundary \/
  (value_until j ls = upper_boundary /\
<<<<<<< HEAD
  last_digit_max_minus < (Byte.signed i - 48))) ->
  (res (Z_of_string_loop ls 0 1)) = ERROR_RANGE.
Proof.
  intros.
  inversion H4.
  - 
  inversion H3.
  eapply bounded_bool_to_Prop in H3.
  assert (bounded (value_until (j + 1) ls) = false) as Bound.
  { erewrite next_value_lt_ub.
    eapply lt_ub_not_bounded.
    eapply loop_non_neg; nia.
    eapply is_digit_to_Z; eassumption.
    all: unfold value_until, Z_of_char in *;
      try eassumption; try nia. }

  assert (res (Z_of_string_loop ls 0 1) = ERROR_RANGE) as Result_loop.

  { edestruct all_digits_OK_or_ERROR_RANGE_loop
      with (ls := sublist 0 (j + 1) ls) (v := 0) (i := 1)  as [Ok | Er].
    autorewrite with sublist.
    admit.
    unfold value_until in *.
    inversion Ok.
    eapply OK_bounded_loop in Ok.
    congruence.
    admit.
    eapply sublist_ERROR_RANGE in Er.
    rewrite Er.
    reflexivity.                  
    admit.
    nia.
  }
  eassumption.
  - 
    inversion H3.
  eapply bounded_bool_to_Prop in H3.
  assert (bounded (value_until (j + 1) ls) = false) as Bound.
  { erewrite next_value_lt_ub.
    eapply eq_ub_not_bounded_minus.
    eapply loop_non_neg; nia.
    eapply is_digit_to_Z; eassumption.
    all: unfold value_until, Z_of_char in *;
      try eassumption; try nia. }

  assert (res (Z_of_string_loop ls 0 1) = ERROR_RANGE) as Result_loop.

  { edestruct all_digits_OK_or_ERROR_RANGE_loop
      with (ls := sublist 0 (j + 1) ls) (v := 0) (i := 1)  as [Ok | Er].
    autorewrite with sublist.
    admit.
    unfold value_until in *.
    inversion Ok.
    eapply OK_bounded_loop in Ok.
    congruence.
    admit.
    eapply sublist_ERROR_RANGE in Er.
    rewrite Er.
    reflexivity.                  
    admit.
    nia.
  }
  eassumption.
                   
Lemma lt_ub_not_bounded : forall v d, 
      0 <= v ->
      0 <= d <= 9 -> 
      v > upper_boundary ->
      bounded (v*10 + d) = false.
Proof.
  intros.
  unfold bounded; cbn in *.
  rewrite andb_false_iff; do 2 rewrite Z.leb_gt.
  lia.
Qed.

Lemma extra_digit_error_range : forall j i ls,
  0 <= j + 1 < Zlength ls ->
  Znth (j + 1) ls = i ->
  is_digit i = true ->
  (forall i0 : Z, 0 <= i0 < j + 1 -> is_digit (Znth i0 ls) = true) ->
  bounded (value_until j ls) = true ->
  value_until j ls = upper_boundary ->
  (Byte.signed i - 48) <=  last_digit_max_minus ->
  (res (Z_of_string_loop ls 0 1)) = ERROR_RANGE.
Proof.
Admitted.
