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

Lemma lt_ub_to_Z : forall v,
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

Lemma all_digits_OK_or_ERROR_RANGE : forall ls,
    0 < Zlength ls -> 
    (forall i, 0 <= i < Zlength ls -> is_digit (Znth i ls)  = true) ->
    res (Z_of_string ls) = OK \/
    res (Z_of_string ls) = ERROR_RANGE.
Proof.
  intros.
  destruct ls.
   - autorewrite with sublist in *.
     nia.
   - simpl.
     replace (is_sign i) with false.
     replace (is_digit i) with true.
     replace (bounded (0 + Z_of_char i)) with true.
     replace (Byte.signed i =? plus_char) with false.
     replace (Byte.signed i =? minus_char) with false.
     break_match.
     auto.
     eapply all_digits_OK_or_ERROR_RANGE_loop.
     (* true, from H0 *)
     admit.
Admitted.

Lemma exists_non_digit_EXTRA_DATA : forall ls,
    0 < Zlength ls -> 
    (exists i, 0 <= i < Zlength ls /\ is_digit (Znth i ls) = false) ->
    res (Z_of_string ls) = EXTRA_DATA.
Proof.
Admitted.

Lemma lt_ub_to_bounded : forall v,
    0 <= v < upper_boundary -> bounded v = true.
Admitted.


Lemma gt_ub_to_not_bounded : forall v,
    0 <= v -> upper_boundary < v -> bounded v = false.
Admitted.

Lemma eq_ub_bounded_plus : forall v d,
    0 <= v ->
    0 <= d <= 9 -> 
    v = upper_boundary ->
    d <= last_digit_max ->
    bounded (v*10 + d) = true.
Admitted.

Lemma eq_ub_not_bounded_plus : forall v d,
    0 <= v ->
    0 <= d <= 9 -> 
    v = upper_boundary ->
    d > last_digit_max ->
    bounded (v*10 + d) = false.
Admitted.

Lemma sign_not_digit : forall  i, is_sign i = true -> is_digit i = false.
Admitted.

Lemma digit_not_sign : forall i, is_digit i = true -> is_sign i = false.
Admitted.

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

(* Maybe don't need these:

Lemma ERROR_RANGE_not_bounded : forall ls,
  res (Z_of_string ls) = ERROR_RANGE ->
  bounded (value (Z_of_string ls)) = false.
Proof.
  destruct ls.
  - discriminate.
  - cbn.
     repeat break_if;
       simpl; try congruence;
         repeat break_if;
       simpl; try congruence;
         try eapply ERROR_RANGE_not_bounded_loop.
Admitted.

Lemma bounded_to_OK : forall ls,
  0 < Zlength ls ->
  bounded (value (Z_of_string ls)) = true ->
  (forall i, 0 <= i < Zlength ls -> is_digit (Znth i ls)  = true) ->
  res (Z_of_string ls) = OK.
Proof.
  intros.
  edestruct all_digits_OK_or_ERROR_RANGE with (ls := ls)
  as [OK | ER];
    intuition.
  eapply ERROR_RANGE_not_bounded in ER.
Admitted. *)

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


(* Lemmas about index *)

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

Lemma value_next_loop : forall ls v i b,
    is_digit b = true ->
    (res (Z_of_string_loop ls v i)) = OK ->
    bounded ((value (Z_of_string_loop ls v i)) * 10 + (Z_of_char b))
            = true ->
    is_digit b = true ->
    value (Z_of_string_loop (ls ++ [b]) v i) = 
    (value (Z_of_string_loop ls v i)) * 10 + (Z_of_char b).
  Proof.
    induction ls; intros.
    * simpl in *.
      repeat bool_rewrite.
      easy.
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
      (forall i : Z, 0 <= i < Zlength ls ->
                is_digit (Znth i ls) = true) ->
      0 < j + 1 <= Zlength ls ->
      (value_until j ls) < upper_boundary ->
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
   eapply lt_ub_to_next_bounded_bool.
   instantiate (1 := 0); nia.
   split.
   eapply loop_non_neg; nia.
   eassumption.
   autorewrite with sublist in *.
   admit.
   apply lt_ub_to_next_bounded_bool.
   eapply is_digit_to_Z; eassumption.
    split.
   eapply loop_non_neg; nia.
   eassumption.
   eassumption.
   nia.
   nia.
Admitted.
    
   
Lemma typed_true_to_digit : forall i, 
    typed_true tint (if 48 <=? Byte.signed i 
                     then Val.of_bool (Byte.signed i <=? 57) 
                     else Vfalse) -> 
    is_digit i = true.
Proof.
  intros.
  unfold is_digit; unfold typed_true, strict_bool_val, Val.of_bool in H; 
    unfold zero_char, nine_char, Byte.lt.
  rewrite andb_true_iff.
  cbn in H.
  assert (Int.eq Int.one Int.zero = false) 
    by (unfold Int.eq; break_match; [discriminate|reflexivity]).
  break_match; repeat break_match; cbn; auto; try discriminate.
  all: try rewrite Z.leb_le in *.
  all: apply Vint_inj in Heqv.
  all: rewrite <-Heqv in H.
  all: try rewrite H0 in *.
  all: cbn in H.
  all: discriminate.
Qed.

Lemma lt_ub_bounded : forall j ls, 
    0 <= j -> j + 1 <= Zlength ls ->
    value_until j ls < upper_boundary -> 
    Byte.signed (Znth j ls) - zero_char <= last_digit_max ->
    bounded (value_until (j + 1) ls) = true.
Abort.

Lemma value_always_bounded : forall j ls,
  j <= Zlength ls ->
  bounded (value_until j ls) = true.
Admitted.
  
Lemma next_value : forall j ls b,
    0 <= j -> j + 1 <= Zlength ls ->
    Znth j ls = b -> is_digit b = true ->
    value_until (j + 1) ls =
    value_until j ls * 10 + Z_of_char b.
Proof.
  induction ls using rev_ind; intros.
  admit.
  apply Z_le_lt_eq_dec in H0; inversion H0; clear H0.
  *
    rewrite Zlength_app in H3; cbn in H3.
    assert (j + 1 <= Zlength ls) by Lia.lia.
    assert (j < Zlength ls) by Lia.lia.
    rewrite app_Znth1 in H1 by assumption.
    specialize (IHls b H H0 H1 H2).
    unfold value_until in *; do 2 rewrite sublist_firstn in *.
    do 2 rewrite Zfirstn_app1 by Lia.lia.
    rewrite IHls; reflexivity.
  *
    rewrite Zlength_app in H3. 
    pose proof H3; cbn in H3.
    assert (j = Zlength ls) by Lia.lia.
    rewrite app_Znth2 in H1 by Lia.lia.
    rewrite <-H4 in H1; cbn in H1.
    rewrite Z.sub_diag in H1.
    rewrite Znth_0_cons in H1.
    rewrite H1 in *.
    unfold value_until; do 2 rewrite sublist_firstn.
    rewrite H0.
    rewrite <-Zlength_app.
    rewrite ZtoNat_Zlength.
    rewrite firstn_all.
    rewrite Zfirstn_app1 by Lia.lia.
    rewrite H4.
    rewrite ZtoNat_Zlength.
    rewrite firstn_all.
    clear - H2.
Admitted.


Lemma ub_last_digit_error_range : forall j i i0 ls,
  0 <= j < Zlength ls ->
  Znth j ls = i0 ->
  (value_until j ls > upper_boundary \/
  (value_until j ls = upper_boundary /\
  last_digit_max < (Byte.signed i0 - 48))) ->
  (res (Z_of_string (i :: ls))) = ERROR_RANGE.
 Admitted.

Lemma ub_last_digit_error_range_index : forall j i i0 ls,
  0 <= j < Zlength ls ->
  Znth j ls = i0 ->
  (value_until j ls > upper_boundary \/
  (value_until j ls = upper_boundary /\
  last_digit_max < (Byte.signed i0 - 48))) ->
  (index (Z_of_string (i :: ls))) = j + 1.
 Admitted.


Lemma extra_data_index : forall j i ls, 
    0 <= j < Zlength ls -> 
    Znth j ls = i -> 
    is_digit i = false -> 
    (index (Z_of_string ls)) = j.
Proof.
  intros.
  induction ls using rev_ind.
  cbn in H; Lia.lia.
  assert (0 <= j <= Zlength ls) by (rewrite Zlength_app in H; cbn in H; Lia.lia).
  inversion H2.
  apply Z_le_lt_eq_dec in H4.
  inversion H4; clear H4.
  rewrite app_Znth1 in H0 by assumption.
  assert (0 <= j < Zlength ls) by Lia.lia. 
  specialize (IHls H4 H0).
  rewrite <-IHls.
  inversion H; clear H.
Admitted.

                   
                    
                   
                    

