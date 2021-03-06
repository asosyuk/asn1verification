Require Import Core.Core Core.Tactics.
Require Import AbstractSpec.
Require Import VST.floyd.proofauto.
Require Import StructTact.StructTactics.

Notation value_until b j l := (value (Z_of_string_loop' (sublist 0 j l) 0 1 b)).

Definition ASN1_INTMAX_MAX := Int64.max_signed.
Definition upper_boundary := Z.div ASN1_INTMAX_MAX 10.
Definition last_digit_max := Zmod ASN1_INTMAX_MAX 10.
Definition last_digit_max_minus := last_digit_max + 1.

(* Lemmas about bounded *)
Ltac Zbool_to_Prop := try (rewrite Z.leb_le ||
                           rewrite Z.leb_gt ||
                           rewrite Z.eqb_eq ||
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

Lemma app_is_digit : forall ls j,
    0 <= j < Zlength ls ->
    (forall i : Z, 0 <= i < j -> is_digit (Znth i ls) = true) ->
    is_digit (Znth j ls) = true ->
    forall i0 : Z, 0 <= i0 < j + 1 -> is_digit (Znth i0 ls) = true.
Proof.
  intros.
  destruct (zle j i0).
  - replace i0 with j by nia.
    eassumption.
  - eapply H0. nia.
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

Lemma bounded'_bool_to_Prop :
  forall v, bounded' false v = true ->  
       0<= v <= Int64.max_signed + 1.
Proof.
  unfold bounded'.
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

Lemma lt_false_inv64:
  forall i j,
    Int64.lt i j = false -> (Int64.signed i >= Int64.signed j)%Z.
Proof.
  intros.
  unfold Int64.lt in H. if_tac in H; inv H. auto.
Qed.
               
Lemma lt_ub_to_next_bounded'_bool : forall v d,
    0 <= d <= 9 -> 
    0 <= v < upper_boundary -> 
    bounded' false (v*10 + d) = true /\
    bounded' false (v*10) = true /\
    bounded' false v = true.
Proof.
  unfold upper_boundary.
  unfold bounded'.
  intros.
  repeat rewrite andb_true_iff in *.
  repeat Zbool_to_Prop.
  cbn in *.
  nia.
Qed.

Lemma lt_ub_to_bounded'_Prop : forall v d,
    0 <= d <= 9 -> (* is digit *)
    0 <= v < upper_boundary -> 
    0 <= v <= Int64.max_signed + 1.
Proof.
  unfold upper_boundary.
  unfold bounded'.
  intros.
  cbn in *.
  nia.
Qed.

Lemma lt_ub_to_next_bounded'_Prop : forall v d,
    0 <= d <= 9 -> (* is digit *)
    0 <= v < upper_boundary -> 
    0 <= v * 10 + d <= Int64.max_signed + 1 /\
    0 <= v * 10 <= Int64.max_signed + 1. 
Proof.
  unfold upper_boundary.
  unfold bounded'.
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
    0 <= v <= Int64.max_signed ->
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

Lemma lt_ub_to_Z4 :  forall i, 
    0 <= Byte.signed i <= Byte.max_unsigned ->
    Int64.lt last_digit_max_minus_int 
             (Int64.repr (Int.signed (Int.sub (Int.repr (Byte.signed i)) 
                                              (Int.repr 48)))) = true -> 
    last_digit_max_minus < (Byte.signed i - 48).
Proof.
  intros.
  rewrite last_digit_max_minus_int_repr in H0.
  unfold Int64.lt, Int.sub in H0; destruct zlt in H0; [|discriminate].
  replace (Int64.signed (Int64.repr 8)) with 8 in l by reflexivity; 
    replace (Int.unsigned (Int.repr 48)) with 48 in l by reflexivity.
  pose proof Byte.signed_range i.
  rewrite Int.unsigned_repr in l by (cbn in *; lia). 
  rewrite Int.signed_repr in l by (cbn in *; lia). 
  rewrite Int64.signed_repr in l by (cbn in *; lia).
  assumption.
Qed.

Lemma lt_ub_to_Z5 :  forall v,
    0 <= v <= Int64.max_signed ->
    Int64.eq (Int64.repr v) upper_boundary_int = false ->
    v <> upper_boundary.
Proof.
  intros.
  rewrite upper_boundary_int_repr in H0.
  unfold Int64.eq in H0; destruct zeq in H0; [discriminate|].
  do 2 rewrite Int64.unsigned_repr in n; cbn in *; try lia.
Qed.

Lemma lt_ub_to_Z6 :  forall i,
    0 <= Byte.signed i <= Byte.max_signed ->
    Int64.lt last_digit_max_minus_int
             (Int64.repr (Int.signed (Int.sub (Int.repr (Byte.signed i)) 
                                              (Int.repr 48)))) = false -> 
    (Byte.signed i - 48) <= last_digit_max_minus.
Proof.         
  intros.
  rewrite last_digit_max_minus_int_repr in H0.
  unfold Int64.lt, Int.sub in H0; destruct zlt in H0; [discriminate|].
  pose proof Byte.signed_range i.
  do 2 rewrite Int.unsigned_repr in g by (cbn in *; lia).
  rewrite Int.signed_repr in g by (cbn in *; lia).
  replace (Int64.signed (Int64.repr 8)) with 8 in g by reflexivity.
  rewrite Int64.signed_repr in g by (cbn in *; lia).
  cbn in *; lia.
Qed.

Lemma eq_ub_not_bounded'_minus : forall v d,
    0 <= v ->
    0 <= d <= 9 -> 
    v = upper_boundary ->
    d > last_digit_max_minus ->
    bounded' false (v*10 + d) = false.
Proof.
  intros.
  unfold bounded'; cbn in *.
  rewrite andb_false_iff; do 2 rewrite Z.leb_gt.
  lia.
Qed.

Ltac lt_ub_to_Z H := try (eapply lt_ub_to_Z1 in H ||
                            eapply lt_ub_to_Z2 in H ||
                               eapply lt_ub_to_Z3 in H ||
                                 eapply lt_ub_to_Z4 in H ||
                                  eapply lt_ub_to_Z5 in H ||
                                   eapply lt_ub_to_Z6 in H).

(* Lemma lt_ub_bounded'_Prop : forall v d,
    0 <= d <= 9 ->
    0 <= v ->
    Int64.min_signed <= v <= Int64.max_signed ->
    Int64.lt (Int64.repr v) upper_boundary_int = true ->
    Int64.min_signed <= v * 10 + d <= Int64.max_signed /\ 
    Int64.min_signed <= v * 10 <= Int64.max_signed.
Proof.
  intros v d D V V' Lt.
  eapply lt_ub_to_next_bounded'_Prop.
  eassumption.
  eapply lt_inv64 in Lt.
  rewrite Int64.signed_repr in *.
  replace (Int64.signed upper_boundary_int) with upper_boundary
   in Lt by normalize.
  all: nia.
Qed. *)

Lemma neg_bounded' : forall v, 
    0 <= v -> 
    bounded' false v = true -> bounded (-1 * v) = true.
  Proof.
    unfold bounded', bounded.
    cbn.
    intros v H.
     repeat rewrite andb_true_iff in *.
     repeat rewrite Z.leb_le in *;
    try nia.
Qed.

                  
Lemma lt_ub_not_bounded' : forall v d, 
      0 <= v ->
      0 <= d <= 9 -> 
      v > upper_boundary ->
      bounded' false (v*10 + d) = false.
Proof.
  intros.
  unfold bounded'; cbn in *.
  rewrite andb_false_iff; do 2 rewrite Z.leb_gt.
  lia.
Qed.

Lemma eq_ub_bounded'_minus : forall v d,
    0 <= v ->
    0 <= d <= 9 -> 
    v = upper_boundary ->
    d <= last_digit_max_minus ->
    bounded' false (v*10 - d) = true.
Proof.
  intros.
  unfold bounded'; cbn in *.
  rewrite andb_true_iff; do 2 rewrite Z.leb_le.
  nia.
Qed.

Lemma eq_ub_next : forall v d,
    0 <= v ->
    0 <= d  -> 
    v = upper_boundary ->
    v*10 + d > upper_boundary.
Proof.
  intros.
  cbn in *.
  lia.
Qed.
      
Lemma eq_ub_bounded'_plus : forall v d, 
      0 <= v ->
      0 <= d <= 9 -> 
      v = upper_boundary ->
      d <= last_digit_max ->
      bounded' true (v*10 + d) = true.
Proof.
  intros.
  unfold bounded'; cbn in *.
  rewrite andb_true_iff; do 2 rewrite Z.leb_le.
  lia.
Qed.

Lemma eq_ub_not_bounded'_plus : forall v d, 
    0 <= v ->
    0 <= d <= 9 -> 
    v = upper_boundary ->
    d > last_digit_max ->
    bounded' true (v*10 + d) = false.
Proof.
  intros.
  unfold bounded'; cbn in *.
  rewrite andb_false_iff; do 2 rewrite Z.leb_gt.
  lia.
Qed.



Lemma bounded'_false : forall v w b,
    bounded' b v = false ->
    0 <= v <= w ->
    bounded' b w = false.
  Proof.
    destruct b;
  unfold bounded'; cbn in *;
  intros;
  rewrite andb_false_iff in *;
  repeat rewrite Z.leb_gt in *;
  nia.
Qed.


Lemma loop_non_neg : forall ls v i, 0 <= v -> 0 <= value (Z_of_string_loop' ls v i false).
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
          
(* Lemmas about Spec *) 

(* ERROR RANGE *)

Lemma ERROR_RANGE_not_bounded'_loop : forall ls v i b,
  0 <= v ->
  res (Z_of_string_loop' ls v i b) = ERROR_RANGE ->
  bounded' b (value (Z_of_string_loop' ls v i b)) = false.
Proof.
  induction ls; intros v i b.
  - discriminate.
  - simpl.
 repeat break_if;
      simpl; try congruence;
        intros;
 try eapply IHls; intuition.
 eapply is_digit_to_Z in Heqb0.
 nia.
 eapply bounded'_false with (v := v).
 eassumption.
 eapply is_digit_to_Z in Heqb0.
 nia.
Qed.

Lemma ERROR_RANGE_not_bounded_loop_C : forall ls v i b,
  0 <= v ->
  res (Z_of_string_loop_C ls v i b) = ERROR_RANGE ->
  bounded (value (Z_of_string_loop_C ls v i b)) = false.
Proof.
  induction ls; intros v i b.
  - discriminate.
  - simpl.
 repeat break_if;
      simpl; try congruence;
        intros;
 try eapply IHls; intuition.
 eapply is_digit_to_Z in Heqb0.
 nia.
 break_match.
 simpl in *. congruence.
 break_if. simpl.
 (* add lemma *)
 admit.
 simpl in *; congruence.
 admit.
Admitted.

Lemma Zlength_aux_inc : forall ls i,
    1 + Zlength_aux i byte ls = Zlength_aux (i + 1) byte ls.
Proof.
  induction ls.
  intros; cbn; lia.
  cbn.
  intros.
  eapply IHls with (i := (Z.succ i)).
Qed.

Lemma sublist_ERROR_RANGE : forall ls v j i, 
    0 < j ->
    res (Z_of_string_loop' (sublist 0 j ls) v i false) = ERROR_RANGE ->
    res (Z_of_string_loop' ls v i false) = ERROR_RANGE.
Proof.
  induction ls; intros v j i.
  -  
    unfold sublist; rewrite skipn_nil; rewrite firstn_nil;
      cbn; discriminate.
  - 
    intros J.
    assert (0 <= j - 1) by lia.
    replace (sublist 0 j (a :: ls)) with (a :: sublist 0 (j - 1) ls); cbn.
    repeat break_if;
      cbn; try congruence.
    apply Z_le_lt_eq_dec in H; destruct H.
    eapply IHls with (j := j - 1); assumption.
    rewrite <-e; cbn; discriminate.
    unfold sublist; cbn.
    replace (j - 1 - 0) with (j - 1) by lia; replace (j - 0) with (j) by lia.
    remember (j - 1) as n; assert (Z.succ n = j) by lia; rewrite <-H0.
    rewrite Z2Nat.inj_succ by assumption.
    rewrite firstn_cons; reflexivity.
Qed.

Lemma sublist_ERROR_RANGE_C : forall ls v j i, 
    0 < j ->
    res (Z_of_string_loop_C (sublist 0 j ls) v i false) = ERROR_RANGE ->
    res (Z_of_string_loop_C ls v i false) = ERROR_RANGE.
Proof.
  intros.
  erewrite <- abstract_spec_C_spec_equiv_false_res in *.
  eapply sublist_ERROR_RANGE;
    try eassumption.
Qed.

Lemma bounded'_to_bounded : forall ls v i, bounded (value (Z_of_string_loop_C ls v i false)) = true 
             ->  bounded' false (value (Z_of_string_loop' ls v i false)) = true.
  Proof.
    intros.
    erewrite abstract_spec_C_spec_equiv_false_value.
    unfold bounded', bounded in *.
Admitted.
    

Lemma ERROR_RANGE_index_C : forall ls v i j,
    0 <= j ->
    j + 1 <= Zlength ls ->
    res (Z_of_string_loop_C ls v i false) = ERROR_RANGE -> 
    bounded (value (Z_of_string_loop_C (sublist 0 j ls) v i false)) = true ->
    bounded (value (Z_of_string_loop_C (sublist 0 (j + 1) ls) v i false)) = false -> 
    index (Z_of_string_loop_C ls v i false) = j + i.
Proof.
Admitted.
       

(* OK *)

Lemma all_digits_OK_or_ERROR_RANGE_loop : forall ls v i b,
    (forall i, 0 <= i < Zlength ls -> is_digit (Znth i ls)  = true) ->
    res (Z_of_string_loop' ls v i b) = OK \/
    res (Z_of_string_loop' ls v i b) = ERROR_RANGE.
Proof.
  - induction ls; intros v0 i0 b DIG.
    -- autorewrite with sublist in *.
      auto.
    -- 
    cbn.
    replace (is_digit a) with true.
    break_if.
    eapply IHls.
    (*from V *)
    (* from DIG *)
    admit.
    auto.
    (* from DIG *)
    admit.
Admitted.

Lemma all_digits_OK_or_ERROR_RANGE_loop_C : forall ls v i b,
    (forall i, 0 <= i < Zlength ls -> is_digit (Znth i ls)  = true) ->
    res (Z_of_string_loop_C ls v i b) = OK \/
    res (Z_of_string_loop_C ls v i b) = ERROR_RANGE.
Proof.
Admitted. (* use the map *)

(* OK *)
Lemma OK_index_loop : forall ls b v i,
  res (Z_of_string_loop' ls v i b) = OK -> 
  index (Z_of_string_loop' ls v i b) = i + Zlength ls.
Proof.
   induction ls; intros b v i.
  - intuition.
  - simpl.
    repeat break_match;
      autorewrite with sublist;
      simpl; try congruence.
    replace (i + Z.succ (Zlength ls)) with
        ((i+1) + Zlength ls) by nia.
    specialize (IHls b (v * 10 + Z_of_char a) (i + 1)).
    intuition.
Qed.

Lemma OK_index_loop_C : forall ls b v i,
  res (Z_of_string_loop_C ls v i b) = OK -> 
  index (Z_of_string_loop_C ls v i b) = i + Zlength ls.
Proof.
Admitted.
(* use map *)

Lemma OK_index : forall ls,
    res (Z_of_string' ls) = OK -> 
    index (Z_of_string' ls) = Zlength ls.
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


Lemma OK_index_C : forall ls,
    res (Z_of_string_C ls) = OK -> 
    index (Z_of_string_C ls) = Zlength ls.
Proof.
Admitted.

Lemma bounded'_to_OK_loop : forall ls v i b,
   0 <= v ->
  bounded' b (value (Z_of_string_loop' ls v i b)) = true ->
  (forall i, 0 <= i < Zlength ls -> is_digit (Znth i ls)  = true) ->
  res (Z_of_string_loop' ls v i b) = OK.
Proof.
  intros.
  edestruct all_digits_OK_or_ERROR_RANGE_loop with (ls := ls)
                                                   (v := v)
  as [Ok | ER];
    intuition;
    try eassumption.
  eapply ERROR_RANGE_not_bounded'_loop in ER.
  congruence.
  nia.
Qed.

Lemma bounded_to_OK_loop_C : forall ls v i b,
   0 <= v ->
  bounded (value (Z_of_string_loop_C ls v i b)) = true ->
  (forall i, 0 <= i < Zlength ls -> is_digit (Znth i ls)  = true) ->
  res (Z_of_string_loop_C ls v i b) = OK.
Proof.
  intros.
  edestruct all_digits_OK_or_ERROR_RANGE_loop_C with (ls := ls)
                                                   (v := v)
  as [Ok | ER];
    intuition;
    try eassumption.
  eapply ERROR_RANGE_not_bounded_loop_C in ER.
  congruence.
  nia.
Qed.

Lemma OK_bounded_loop : forall ls b v i,
    bounded v = true ->
    res (Z_of_string_loop_C ls v i b) = OK ->
    bounded (value (Z_of_string_loop_C ls v i b)) = true.
Proof.
  induction ls; intros b v i.
  - simpl; congruence.
  - intro.
    simpl.
    repeat break_if;
      simpl; try congruence.
     eapply IHls.
    all: intuition.
     try (rewrite Z.ltb_lt in *).
     admit.
     break_match.
     simpl.
     admit.
     break_if.
     simpl in *; congruence.
     simpl in *; congruence.
Admitted.
 
Lemma app_char_to_OK_loop : forall ls b i,
    0 < Zlength ls ->
    is_sign i = true ->
    res (Z_of_string_loop' ls 0 1 b) = OK ->
    res (Z_of_string' (i :: ls)) = OK.
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
    intuition; try congruence; try eassumption.
  admit. (* refactor *)
Admitted.

Lemma is_digit_bounded' : forall b c,
    is_digit c = true ->
    bounded' b (Z_of_char c) = true.
Proof.
  destruct b.
  intros.
  unfold is_digit, bounded', zero_char, nine_char, Z_of_char in *; cbn in *.
  rewrite andb_true_iff in *.
  repeat rewrite ->Z.leb_le in *.
  lia.
  intros.
  unfold is_digit, bounded', zero_char, nine_char, Z_of_char in *; cbn in *.
  rewrite andb_true_iff in *.
  repeat rewrite ->Z.leb_le in *.
  lia.
Qed.

(* EXTRA DATA *)
             
Lemma value_next_loop : forall ls v i b r,
    (res (Z_of_string_loop' ls v i r)) = OK ->
    is_digit b = true ->
    value (Z_of_string_loop' (ls ++ [b]) v i r) = 
    (value (Z_of_string_loop' ls v i r)) * 10 + (Z_of_char b).
Proof.
  induction ls; intros.
  * simpl in *.
    repeat bool_rewrite.
    break_if; easy.
  * simpl in *.
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

Lemma EXTRA_DATA_next_loop : forall ls v i b r,
    (res (Z_of_string_loop' ls v i r)) = OK ->
    is_digit b = false ->
    res (Z_of_string_loop' (ls ++ [b]) v i r) = EXTRA_DATA.
Proof.
  induction ls; intros.
  * simpl in *.
    repeat bool_rewrite.
    easy.
  * simpl in *.
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

Lemma EXTRA_DATA_index_loop : forall ls v i b r,
    (res (Z_of_string_loop' ls v i r)) = OK ->
    is_digit b = false ->
    index (Z_of_string_loop' (ls ++ [b]) v i r) = Zlength ls + i.
Proof.
  induction ls; intros.
  * simpl in *.
    repeat bool_rewrite.
    easy.
  * simpl in *.
    break_if.
    break_if.
    erewrite IHls.
    autorewrite with sublist.
    nia.
    eassumption.
    all: simpl in *;
    repeat break_if;
      try congruence; simpl in *;
    try congruence.
Qed.

Lemma next_value_lt_ub : forall ls j i b,
     (forall i : Z, 0 <= i < j  ->
               is_digit (Znth i ls) = true) ->
     0 < j + 1 <= Zlength ls ->
     bounded' b (value_until b j ls) = true -> 
     Znth j ls = i ->
     is_digit i = true ->
     (value_until b (j + 1) ls) = (value_until b j ls * 10 + (Z_of_char i)).
Proof.
  intros.
  rewrite sublist_last_1.
  subst.
  eapply value_next_loop.
  eapply bounded'_to_OK_loop.
  nia.
  eassumption.
  admit.
  eassumption.
  all: nia.
Admitted.
(*
Lemma ub_last_digit_error_range : forall j i ls,
  0 <= j < Zlength ls ->
  Znth j ls = i ->
  is_digit i = true ->
  (forall i0 : Z, 0 <= i0 < j -> is_digit (Znth i0 ls) = true) ->
  bounded' false (value_until false j ls) = true ->
  (value_until false j ls > upper_boundary \/
  (value_until false j ls = upper_boundary /\
  last_digit_max_minus < (Byte.signed i - 48))) ->
  (res (Z_of_string_loop' ls 0 1 false)) = ERROR_RANGE.
Proof.
  intros.
  inversion H4.
  - 
  inversion H3.
  eapply bounded'_bool_to_Prop in H3.
  assert (bounded' false (value_until false (j + 1) ls) = false) as Bound.
  { erewrite next_value_lt_ub.
    eapply lt_ub_not_bounded'.
    eapply loop_non_neg; nia.
    eapply is_digit_to_Z; eassumption.
    all: unfold value_until, Z_of_char in *;
      try eassumption; try nia. }

  assert (res (Z_of_string_loop' ls 0 1 false) = ERROR_RANGE) as Result_loop.
  { edestruct all_digits_OK_or_ERROR_RANGE_loop
      with (ls := sublist 0 (j + 1) ls) (v := 0) (i := 1) (b := false) as [Ok | Er].
    autorewrite with sublist.
    admit.
    inversion Ok.
    eapply OK_bounded'_loop in Ok.
    congruence.
    admit.
    eapply sublist_ERROR_RANGE in Er.
    rewrite Er.
    reflexivity.
    nia.
  }
  eassumption.
  - 
    inversion H3.
  eapply bounded'_bool_to_Prop in H3.
  assert (bounded' false (value_until false (j + 1) ls) = false) as Bound.
  { erewrite next_value_lt_ub.
    eapply eq_ub_not_bounded'_minus.
    eapply loop_non_neg; nia.
    eapply is_digit_to_Z; eassumption.
    all: unfold value_until, Z_of_char in *;
      try eassumption; try nia. }

  assert (res (Z_of_string_loop' ls 0 1 false) = ERROR_RANGE) as Result_loop.

  { edestruct all_digits_OK_or_ERROR_RANGE_loop
      with (ls := sublist 0 (j + 1) ls) (v := 0) (i := 1) (b := false)  as [Ok | Er].
    autorewrite with sublist.
    admit.
    inversion Ok.
    eapply OK_bounded'_loop in Ok.
    congruence.
    admit.
    eapply sublist_ERROR_RANGE in Er.
    rewrite Er.
    reflexivity.    
    nia.
  }
  eassumption.
Admitted.

(* EXTRA DATA *)

Lemma EXTRA_DATA_or_ERROR_RANGE_result :
  forall ls v k j i b, 
    0 <= j < Zlength ls ->
    Znth j ls = i -> 
    is_digit i = false -> 
    res (Z_of_string_loop' ls v k b) = EXTRA_DATA
    \/ res (Z_of_string_loop' ls v k b) = ERROR_RANGE.
  induction ls; intros v k j i b N Dig Bound.
  - autorewrite with sublist in *.
    nia.
  - simpl.
    repeat break_if.
    assert (0 <= Zlength ls).
    eapply Zlength_nonneg.
    assert (0 < j) as ZZ.
    destruct (zle 0 (j -1)).
    nia.
    assert (j = 0) as Z by nia.
    rewrite Z in Dig.
    erewrite Znth_0_cons in Dig.
    subst.
    congruence.
    eapply IHls with (j := j - 1) (i := i).  
    autorewrite with sublist in *.
    auto with zarith.
    rewrite <- Dig.
    erewrite Znth_pos_cons; auto.
    eassumption.
    all: intuition. 
Qed.

Lemma EXTRA_DATA_value_loop : forall ls v i b r,
    (res (Z_of_string_loop' ls v i r)) = OK ->
    is_digit b = false ->
    value (Z_of_string_loop' (app ls [b]) v i r) =  
    value (Z_of_string_loop' ls v i r).
Proof.
  induction ls; intros.
  * simpl in *.
    repeat bool_rewrite.
    easy.
  * simpl in *.
    break_if.
    break_if.
    erewrite IHls.
    autorewrite with sublist.
    nia.
    eassumption.
    all: simpl in *;
      repeat break_if;
      try congruence; simpl in *;
        try congruence.
Qed.

Lemma sublist_EXTRA_DATA : forall ls v j i m vl b, 
    res (Z_of_string_loop' (sublist 0 j ls) v i b) = EXTRA_DATA ->
    value (Z_of_string_loop' (sublist 0 j ls) v i b) = vl ->
    index (Z_of_string_loop' (sublist 0 j ls) v i b) = m ->

    res (Z_of_string_loop' ls v i b) = EXTRA_DATA /\
    index (Z_of_string_loop' ls v i b) = m /\
    value (Z_of_string_loop' ls v i b) = vl.
Admitted.
*)
