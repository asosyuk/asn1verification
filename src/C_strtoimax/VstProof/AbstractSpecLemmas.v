Require Import Core.Core Core.Tactics.
Require Import AbstractSpec.
Require Import VST.floyd.proofauto.
Require Import StructTact.StructTactics.

Notation value_until j l b := (value (Z_of_string_loop (sublist 0 j l) 0 1 b)).

(* Lemmas about bounded *)
Ltac Zbool_to_Prop := try (rewrite Z.leb_le ||
                           rewrite Z.leb_gt ||
                           rewrite Z.eqb_eq ||
                           rewrite Z.eqb_neq ).

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
    (forall i : Z, 0 <= i < j -> is_digit (Znth i ls) = true) ->
    is_digit (Znth j ls) = true ->
    forall i0 : Z, 0 <= i0 < j + 1 -> is_digit (Znth i0 ls) = true.
Proof.
  intros.
  destruct (zle j i0).
  - replace i0 with j by nia.
    eassumption.
  - eapply H. nia.
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
  forall v, bounded v = true <->  
       Int64.min_signed <= v <= Int64.max_signed.
Proof.
  unfold bounded.
  intro.
  rewrite andb_true_iff in *.
  repeat Zbool_to_Prop.
  tauto.
Qed.

Lemma bounded_false_bool_to_Prop :
  forall v, bounded v = false <->  
       (Int64.min_signed > v) \/  (v > Int64.max_signed).
Proof.
  unfold bounded.
  intro.
  rewrite andb_false_iff in *.
  repeat Zbool_to_Prop.
  nia.
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
    0 <= d <= 9 -> 
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

Ltac lt_ub_to_Z H := try (eapply lt_ub_to_Z1 in H ||
                          eapply lt_ub_to_Z2 in H ||
                          eapply lt_ub_to_Z3 in H ||
                          eapply lt_ub_to_Z4 in H ||
                          eapply lt_ub_to_Z5 in H ||
                          eapply lt_ub_to_Z6 in H).

Ltac int64_to_Z :=
  match goal with 
  | [H : context[Int64.lt _ _ = _] |- _ ] => lt_ub_to_Z H
  | [H : context[Int64.eq _ _ = _] |- _ ] => lt_ub_to_Z H
  end.

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

Lemma eq_ub_not_bounded_minus : forall v d,
    v <= 0 ->
    0 <= d <= 9 -> 
    v = - upper_boundary ->
    d > last_digit_max_minus ->
    bounded (v*10 - d) = false.
Proof.
  intros.
  unfold bounded; cbn in *.
  rewrite andb_false_iff; do 2 rewrite Z.leb_gt.
  lia.
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

Lemma eq_ub_bounded_minus : forall v d,
      v <= 0 ->
      0 <= d <= 9 -> 
      v = -upper_boundary ->
      d <= last_digit_max_minus ->
      bounded (v*10 - d) = true.
Proof.
  intros.
  unfold bounded; cbn in *.
  rewrite andb_true_iff; do 2 rewrite Z.leb_le.
  nia.
Qed.
  
Lemma loop_neg : forall ls v i,
    v <= 0 ->
    value (Z_of_string_loop ls v i false) <= 0.
Proof.
  induction ls.
  - intuition. 
  - intros.
    simpl;
      repeat break_if;
      simpl; try congruence;
        try eapply is_digit_to_Z in Heqb;
        try eapply IHls.
    all: try nia.
Qed.

Lemma eq_ub_next_gt_ub_plus : forall v d,
    0 <= v ->
    0 <= d  -> 
    v = upper_boundary ->
    v*10 + d > upper_boundary.
Proof.
  intros.
  cbn in *.
  lia.
Qed.
      
Lemma eq_ub_next_gt_ub_minus : forall v d,
    v <= 0 ->
    0 <= d  -> 
    v = - upper_boundary ->
    v*10 - d < -upper_boundary.
Proof.
  intros.
  cbn in *.
  lia.
Qed.

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

Lemma loop_non_neg : forall ls v i, 0 <= v -> 0 <= value (Z_of_string_loop ls v i true).
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
          
Lemma value_false_eq_neg_value_true : forall ls v i, 
    0 <= v ->
    bounded (value (Z_of_string_loop ls v i true)) = true -> 
    value (Z_of_string_loop ls (-v) i false) = 
    - value (Z_of_string_loop ls v i true). 

Proof.
  induction ls.
  - intuition.
  - simpl. intros v i L B.
    repeat break_if;
      simpl; try congruence;
        replace (- v * 10 - Z_of_char a) with 
            (-((v * 10 + Z_of_char a))) by nia;
        try eapply IHls; 
        try eapply is_digit_to_Z in Heqb;
        try nia;
        try eassumption.
    simpl in *.
    congruence.
    eapply neg_bounded in Heqb1.
    replace (-1 * (v * 10 + Z_of_char a))%Z with
        ((-v * 10 - Z_of_char a)) in Heqb1 by nia.
    congruence.
    nia.
Qed.

Lemma value_false_eq_neg_value_true0 : forall ls i,
    bounded (value (Z_of_string_loop ls 0 i true)) = true ->
    value (Z_of_string_loop ls 0 i false) = 
    - value (Z_of_string_loop ls 0 i true). 

Proof.
  intros. 
  replace 0 with (-0) by nia.
  eapply value_false_eq_neg_value_true;
    try nia; try eassumption.
Qed.

Lemma bounded_true_to_false : forall ls i,
    bounded (value (Z_of_string_loop ls 0 i true))  = true ->
    bounded (value (Z_of_string_loop ls 0 i false)) = true.
Proof.
  intros.
  erewrite value_false_eq_neg_value_true0;
    try eassumption.
  eapply neg_bounded.
  eapply loop_non_neg; nia.
  eassumption.
Qed.

Lemma lt_ub_not_bounded_plus : forall v d, 
      0 <= d <= 9 -> 
      v > upper_boundary ->
      bounded (v*10 + d) = false. 
Proof.
  intros.
  unfold bounded; cbn in *.
  rewrite andb_false_iff; do 2 rewrite Z.leb_gt.
  lia.
Qed.

Lemma lt_ub_not_bounded_minus : forall v d, 
    0 <= d <= 9 -> 
    v < - upper_boundary ->
    bounded (v*10 - d) = false.
Proof.
  intros.
  unfold bounded; cbn in *.
  rewrite andb_false_iff; do 2 rewrite Z.leb_gt.
  lia.
Qed.

(* Lemmas about Spec *) 

(* ERROR RANGE *)

Lemma ERROR_RANGE_not_bounded_loop : forall ls v i b,
    res (Z_of_string_loop ls v i b) = ERROR_RANGE ->
    bounded (value (Z_of_string_loop ls v i b)) = false.
Proof.
  induction ls; intros v i b.
  - discriminate.
  - simpl.
    repeat break_if.
    simpl; try congruence;
      try eapply IHls; simpl;  intuition.
    simpl. intuition.
    simpl. congruence.
Qed.


Lemma sublist_ERROR_RANGE : forall ls v j i b, 
    0 < j <= Zlength ls ->
    res (Z_of_string_loop (sublist 0 j ls) v i b) = ERROR_RANGE ->
    res (Z_of_string_loop ls v i b) = ERROR_RANGE.
Proof.
  induction ls; intros v j i b.
  -  
    unfold sublist; rewrite skipn_nil; rewrite firstn_nil;
      cbn; discriminate.
  - 
    intros J.
    assert (0 <= j - 1) by lia.
    replace (sublist 0 j (a :: ls)) with (a :: sublist 0 (j - 1) ls); cbn.
    repeat break_match;
      simpl; try congruence.
    apply Z_le_lt_eq_dec in H; destruct H.
    autorewrite with sublist in *.
    eapply IHls with (j := j - 1). nia.
    rewrite <-e; simpl. discriminate.
    simpl in IHls. 
    erewrite semax_lemmas.cons_app.
    replace (a :: ls) with (app [a] ls).
    erewrite sublist0_app2.
    reflexivity.
    autorewrite with sublist in *.
    assert (0 <= Zlength ls) by (eapply Zlength_nonneg).   
    nia.
    erewrite <- semax_lemmas.cons_app.
    auto.
Qed.

Lemma ERROR_RANGE_index : forall ls v i j b,
    0 <= j ->
    j + 1 <= Zlength ls ->
    res (Z_of_string_loop ls v i b) = ERROR_RANGE -> 
    bounded (value (Z_of_string_loop (sublist 0 j ls) v i b)) = true ->
    bounded (value (Z_of_string_loop (sublist 0 (j + 1) ls) v i b)) = false -> 
    index (Z_of_string_loop ls v i b) = j + i.
Proof.
  induction ls; intros v i j b.
  -
    cbn; discriminate.
  -
    intros J Z; apply Z_le_lt_eq_dec in J; destruct J.
    replace (sublist 0 j (a :: ls)) with (a :: sublist 0 (j - 1) ls).
    replace (sublist 0 (j + 1) (a :: ls)) with (a :: sublist 0 j ls).
    rewrite Zlength_cons in Z; assert (0 <= j - 1) by lia; 
      assert (j - 1 + 1 <= Zlength ls) by lia.
    cbn; repeat break_if; cbn; try congruence.
    intros.
    replace (j) with (j - 1 + 1) in H3 by lia.
    pose proof IHls (app_char b v a) (i + 1) (j - 1) b H H0 H1 H2 H3.
    replace (j - 1 + (i + 1)) with (j + i) in H4 by lia.
    assumption.
    1,2: unfold sublist; cbn.
    replace (j + 1 - 0) with (Z.succ j) by lia; rewrite Z2Nat.inj_succ by lia; 
      replace (j - 0) with (j) by lia; rewrite firstn_cons; reflexivity.
    remember (j - 1) as n; replace (n - 0) with (n) by lia; 
      replace (j - 0) with (j) by lia; assert (j = Z.succ n) by lia; 
        rewrite H; rewrite Z2Nat.inj_succ by lia; rewrite firstn_cons; 
          reflexivity.
    rewrite <-e; cbn; repeat break_if; cbn; try congruence.
    reflexivity.
Qed.

(* OK *)
Lemma all_digits_OK_or_ERROR_RANGE_loop : forall ls v i b,
    (forall i, 0 <= i < Zlength ls -> is_digit (Znth i ls)  = true) ->
    res (Z_of_string_loop ls v i b) = OK \/
    res (Z_of_string_loop  ls v i b) = ERROR_RANGE.
Proof.
  - induction ls; intros v i b  DIG.
    -- autorewrite with sublist in *.
      auto.
    -- 
    cbn.
    assert (is_digit a = true).
    replace a with (Znth 0 (a::ls)).
    eapply DIG.
    autorewrite with sublist.
    assert (0 <= Zlength ls) by (eapply Zlength_nonneg).   
    nia.
    eapply Znth_0_cons.
    repeat break_if.
    eapply IHls.
    (* from DIG *)
    admit.
    auto.
    congruence.
Admitted.

(* OK *)
Lemma OK_index_loop : forall ls v i b,
  res (Z_of_string_loop ls v i b) = OK -> 
  index (Z_of_string_loop ls v i b) = i + Zlength ls.
Proof.
   induction ls; intros v i b.
  - intuition.
  - simpl.
    repeat break_match;
      autorewrite with sublist;
      simpl; try congruence.
    replace (i + Z.succ (Zlength ls)) with
        ((i+1) + Zlength ls) by nia.
    eapply IHls.
Qed.

Lemma OK_index : forall ls,
    res (Z_of_string ls) = OK -> 
    index (Z_of_string ls) = Zlength ls.
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
      try nia;  try easy.
Qed.

Lemma bounded_to_OK_loop : forall ls v i b,
  bounded (value (Z_of_string_loop ls v i b)) = true ->
  (forall i, 0 <= i < Zlength ls -> is_digit (Znth i ls)  = true) ->
  res (Z_of_string_loop ls v i b) = OK.
Proof.
  intros.
  edestruct all_digits_OK_or_ERROR_RANGE_loop with (ls := ls)
                                                   (v := v)
  as [Ok | ER];
    intuition;
    try eassumption.
  eapply ERROR_RANGE_not_bounded_loop in ER.
  congruence.
Qed.

Lemma OK_bounded_loop : forall ls v i b,
    bounded v = true ->
    res (Z_of_string_loop ls v i b) = OK ->
    bounded (value (Z_of_string_loop ls v i b)) = true.
Proof.
  induction ls; intros v i b.
  - simpl; congruence.
  - cbn.
    repeat break_match;
      simpl; try congruence.
    repeat break_if;
      simpl; try congruence.
    intros. eapply IHls.
    all: intuition.
Qed.
 
Definition sign_to_bool i :=
  if Byte.signed i =? minus_char then false else true.

Lemma minus_not_plus : forall i, (Byte.signed i =? minus_char) = true -> 
                             (Byte.signed i =? plus_char) = false.
Proof.
  intro.
  repeat Zbool_to_Prop.
  unfold minus_char, plus_char.
  nia.
Qed.

Lemma plus_not_minus : forall i, (Byte.signed i =? plus_char) = true -> 
                             (Byte.signed i =? minus_char) = false.
Proof.
  intro.
  repeat Zbool_to_Prop.
  unfold minus_char, plus_char.
  nia.
Qed.

Lemma app_char_to_OK_loop : forall ls i,
    0 < Zlength ls ->
    is_sign i = true ->
    res (Z_of_string_loop ls 0 1 (sign_to_bool i)) = OK ->
    res (Z_of_string (i :: ls)) = OK.
Proof.
  intros until i. intros L S Ok.
  unfold is_sign in S; unfold sign_to_bool in *.
  destruct_orb_hyp.
  inversion H; eapply plus_not_minus in H.
  rewrite H in *.
  all:
    simpl;
    repeat break_if; autorewrite with sublist in *;
      try nia;
      try eapply sign_not_digit in S;
      intuition; try congruence;
        try eassumption.
  eapply plus_not_minus in Heqb.
  congruence.
Qed.

Lemma is_digit_bounded : forall c,
    is_digit c = true ->
    bounded (Z_of_char c) = true.
Proof.
  intros.
  unfold is_digit, bounded, zero_char, nine_char, Z_of_char in *; cbn in *.
  rewrite andb_true_iff in *.
  repeat rewrite ->Z.leb_le in *.
  lia.
Qed.

(* EXTRA DATA *)
             
Lemma value_next_loop : forall ls v i b r,
    (res (Z_of_string_loop ls v i r)) = OK ->
    is_digit b = true ->
    value (Z_of_string_loop (ls ++ [b]) v i r) = 
    app_char r (value (Z_of_string_loop ls v i r)) b.
Proof.
  induction ls; intros.
  * simpl in *.
    repeat bool_rewrite.
    break_if; try easy.
  * simpl in *.
    break_if.
    break_if.
    erewrite  IHls.
    reflexivity.
    eassumption.
    all: simpl in *;
    repeat break_if;
      try congruence; simpl in *;
    try congruence.
Qed.

Lemma next_value_lt_ub : forall ls j i r,
    (forall i : Z, 0 <= i < j  -> is_digit (Znth i ls) = true) ->
    0 < j + 1 <= Zlength ls ->
    bounded (value_until j ls r) = true -> 
    Znth j ls = i ->
    is_digit i = true ->
    (value_until (j + 1) ls r) = app_char r (value_until j ls r) i.
Proof.
  intros.
  rewrite sublist_last_1.
  subst.
  eapply value_next_loop.
  eapply bounded_to_OK_loop.
  eassumption.
  autorewrite with sublist.
  Search sublist 0.
  intros.
  erewrite Znth_sublist.
  normalize.
  all: try nia; try eassumption.
Qed.

Lemma bounded0 : (bounded 0 = true).
  { unfold bounded.
    rewrite andb_true_iff in *.
    repeat Zbool_to_Prop.
    cbn.
    nia. }
Qed.

Lemma ub_last_digit_error_range : forall j i ls b,
    0 <= j < Zlength ls ->
    Znth j ls = i ->
    is_digit i = true ->
    (forall i0 : Z, 0 <= i0 < j -> is_digit (Znth i0 ls) = true) ->
    bounded (value_until j ls b) = true ->
    (Z.abs (value_until j ls b)) > upper_boundary \/
    (Z.abs (value_until j ls b)) = upper_boundary /\
    last_digit b < (Byte.signed i - 48) ->
    (res (Z_of_string_loop ls 0 1 b)) = ERROR_RANGE.
Proof.
  intros.
  inversion H4.
  - 
    inversion H3.
    eapply bounded_bool_to_Prop in H3.
    assert (bounded (value_until (j + 1) ls b) = false) as Bound.
    { erewrite next_value_lt_ub with (i := i).
      destruct b.
      eapply lt_ub_not_bounded_plus.
      eapply is_digit_to_Z; eassumption.    
      all: unfold Z_of_char in *;
        try eassumption; try nia. 
      assert (0 <= value_until j ls true) by (eapply loop_non_neg; nia). 
      nia.
      eapply lt_ub_not_bounded_minus.
      eapply is_digit_to_Z; eassumption.    
      all: unfold Z_of_char in *;
        try eassumption; try nia.

      assert (value_until j ls false <= 0 ) by (eapply loop_neg; nia). 
      nia.
    }

    assert (res (Z_of_string_loop ls 0 1 b) = ERROR_RANGE) as Result_loop.

    { edestruct all_digits_OK_or_ERROR_RANGE_loop
        with (ls := sublist 0 (j + 1) ls) (v := 0) (i := 1) (b := b)  as [Ok | Er].
      autorewrite with sublist.
      eapply app_is_digit.
      intros.
      erewrite Znth_sublist.
      normalize.
      all: try nia; try eassumption.
      erewrite Znth_sublist.
      normalize.
      subst.
      all: try nia; try eassumption.
      inversion Ok.
      eapply OK_bounded_loop  with (b := b) in  Ok.
      congruence.
      eapply bounded0.
      eapply sublist_ERROR_RANGE in Er.
      rewrite Er.
      reflexivity.
      nia.
    }
    eassumption.
  - 
    inversion H3. clear H4.
    eapply bounded_bool_to_Prop in H3.
    assert (bounded (value_until (j + 1) ls b) = false) as Bound.
    { erewrite next_value_lt_ub with (i := i).
      assert (0 <= value_until j ls true) by (eapply loop_non_neg; nia).      
      destruct b.
      eapply eq_ub_not_bounded_plus.
      eassumption.
      eapply is_digit_to_Z; eassumption.    
      all: unfold Z_of_char in *;
        try eassumption; try nia. 
      break_and.
      unfold last_digit in *.
      nia.      
      assert (value_until j ls false <= 0 ) by (eapply loop_neg; nia). 
      eapply eq_ub_not_bounded_minus.
      eassumption.
      
      eapply is_digit_to_Z; eassumption.    
      all: unfold Z_of_char in *;
        try eassumption; try nia.
      break_and.
      unfold last_digit in *.
      nia.
    }

    assert (res (Z_of_string_loop ls 0 1 b) = ERROR_RANGE) as Result_loop.

    { edestruct all_digits_OK_or_ERROR_RANGE_loop
        with (ls := sublist 0 (j + 1) ls) (v := 0) (i := 1) (b := b)  as [Ok | Er].
      autorewrite with sublist.
      eapply app_is_digit.
      intros.
      erewrite Znth_sublist.
      normalize.
      all: try nia; try eassumption.
      erewrite Znth_sublist.
      normalize.
      subst.
      all: try nia; try eassumption.
      inversion Ok.
      eapply OK_bounded_loop  with (b := b) in  Ok.
      congruence.
      eapply bounded0.
      eapply sublist_ERROR_RANGE in Er.
      rewrite Er.
      reflexivity.
      nia.
    }
    eassumption.
Qed.

(* EXTRA DATA *)

Lemma EXTRA_DATA_or_ERROR_RANGE_result :
  forall ls v k j i, 
    0 <= j < Zlength ls ->
    Znth j ls = i -> 
    is_digit i = false -> 
    res (Z_of_string_loop ls v k false) = EXTRA_DATA
    \/ res (Z_of_string_loop ls v k false) = ERROR_RANGE.
  induction ls; intros v k j i N Dig Bound.
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


Lemma EXTRA_DATA_loop : forall ls v i b r,
    res (Z_of_string_loop ls v i r) = OK ->
    is_digit b = false ->
    Z_of_string_loop (app ls [b]) v i r =  
    {| res := EXTRA_DATA;
       value := value (Z_of_string_loop ls v i r);
       index :=  Zlength ls + i |}.    
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
    replace (Z.succ (Zlength ls) + i) with
        (Zlength ls + (i + 1)) by nia.
    reflexivity.
    all: try eassumption.
    all: simpl in *;
      repeat break_if;
      try congruence; simpl in *;
        try congruence.
Qed.

Lemma sublist_EXTRA_DATA : forall ls v j i m vl b, 
    0 < j <= Zlength ls ->
    Z_of_string_loop (sublist 0 j ls) v i b = 
    {| res := EXTRA_DATA;
       index := m;
       value := vl |} -> Z_of_string_loop ls v i b =
                        {| res := EXTRA_DATA;
                           index := m;
                           value := vl
                        |}.
Proof.
  Proof.
  induction ls; intros v j i m vl b.
  -  
    unfold sublist; rewrite skipn_nil; rewrite firstn_nil;
      cbn; discriminate.
  - 
    intros J.
    assert (0 <= j - 1) by lia.
    replace (sublist 0 j (a :: ls)) with (a :: sublist 0 (j - 1) ls); cbn.
    repeat break_match;
      simpl; try congruence.
    apply Z_le_lt_eq_dec in H; destruct H.
    autorewrite with sublist in *.
    eapply IHls with (j := j - 1). nia.
    rewrite <-e; simpl. discriminate.
    simpl in IHls. 
    erewrite semax_lemmas.cons_app.
    replace (a :: ls) with (app [a] ls).
    erewrite sublist0_app2.
    reflexivity.
    autorewrite with sublist in *.
    assert (0 <= Zlength ls) by (eapply Zlength_nonneg).   
    nia.
    erewrite <- semax_lemmas.cons_app.
    auto.
Qed.

Lemma EXTRA_DATA_sign_res : forall i i0 j ls, 
    is_sign i = true ->
    0 <= j  < Zlength ls ->
    Znth j ls = i0 ->
    (forall i : Z, 0 <= i < j -> is_digit (Znth i ls) = true) -> 
    bounded (value_until j ls (sign_to_bool i)) = true ->
    is_digit i0 = false ->
    Z_of_string (i :: ls) = {| res := EXTRA_DATA;
                              index := j + 1;
                              value := value_until j ls (sign_to_bool i)
                           |}. 
Proof.
  intros.
  assert ((sublist 0 (j + 1) ls) = 
          app (sublist 0 j ls) [i0]) as SL.
  { erewrite  sublist_split with (mid := j).
    f_equal.
    erewrite sublist_one.
    f_equal.
    eassumption.
    all: try nia. }

 assert (Z_of_string_loop (sublist 0 (j + 1) ls) 0 1 (sign_to_bool i) = 
         {| res := EXTRA_DATA;
            index := j + 1;
            value := value_until j ls (sign_to_bool i)
         |}).

  { rewrite SL.
    erewrite EXTRA_DATA_loop.
    autorewrite with sublist.
    reflexivity.
    eapply bounded_to_OK_loop.
    eassumption.
    intros.
    autorewrite with sublist in H5.
    replace (Znth i1 (sublist 0 j ls)) with (Znth i1 ls).
    eapply H2; try nia; try eassumption.
    erewrite Znth_sublist.
    normalize.
    all: try nia; try eassumption. 
  }

  simpl.
  repeat bool_rewrite.
  unfold is_sign in *; unfold sign_to_bool in *.
  destruct_orb_hyp.
  - rewrite H in *.
    eapply plus_not_minus in H.
    rewrite H in *.
    break_match.
     autorewrite with sublist in *.
     nia.
      eapply sublist_EXTRA_DATA in H5.
     eassumption.
  autorewrite with sublist in *;
    try nia.
  - rewrite H in *.
    eapply minus_not_plus in H.
    rewrite H in *.
    break_match.
     autorewrite with sublist in *.
     nia.
      eapply sublist_EXTRA_DATA in H5.
     eassumption.
  autorewrite with sublist in *;
    try nia.
Qed.
