Require Import Core.Core Core.Tactics.
Require Import AbstractSpec.
Require Import VST.floyd.proofauto.
Require Import StructTact.StructTactics.

Definition value_until j l := 
             (value (Z_of_string (sublist 0 j l))). 

Definition ASN1_INTMAX_MAX := Int64.max_unsigned.
Definition upper_boundary := Z.div ASN1_INTMAX_MAX 10.
Definition last_digit_max := Zmod ASN1_INTMAX_MAX 10.
Definition last_digit_max_minus := last_digit_max + 1.

Lemma all_digits_OK_or_ERROR_RANGE_loop : forall ls v i,
    (forall i, 0 <= i < Zlength ls -> is_digit (Znth i ls)  = true) ->
    res (Z_of_string_loop ls v i) = ASN_STRTOX_OK \/
    res (Z_of_string_loop ls v i) = ASN_STRTOX_ERROR_RANGE.
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
    res (Z_of_string ls) = ASN_STRTOX_OK \/
    res (Z_of_string ls) = ASN_STRTOX_ERROR_RANGE.
Proof.
  intros.
  destruct ls.
   - autorewrite with sublist in *.
     nia.
   - simpl.
     replace (is_sign i) with false.
     replace (is_digit i) with true.
     replace (bounded (0 + Z_of_char i)) with true.
     replace (Byte.eq i plus_char) with false.
     replace (Byte.eq i minus_char) with false.
     break_match.
     auto.
     eapply all_digits_OK_or_ERROR_RANGE_loop.
     (* true, from H0 *)
     admit.
Admitted.

Lemma value_next_loop : forall ls v i b,
    is_digit b = true ->
    (res (Z_of_string_loop ls v i)) = ASN_STRTOX_OK ->
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
  all: rewrite Byte.signed_repr in l by (cbn; Lia.lia).
  all: try rewrite Byte.signed_repr in l0 by (cbn; Lia.lia).
  all: try Lia.lia.
  all: apply Vint_inj in Heqv.
  all: rewrite <-Heqv in H.
  all: try rewrite H0 in *.
  all: cbn in H.
  all: discriminate.
Qed.


Lemma lt_ub_bounded : forall j ls, 
    0 <= j -> j + 1 <= Zlength ls ->
    value_until j ls < upper_boundary -> 
    Byte.signed (Znth j ls) - Byte.signed zero_char <= last_digit_max ->
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
  (res (Z_of_string (i :: ls))) = ASN_STRTOX_ERROR_RANGE.
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
    is_digit i = true -> 
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

(** Need a tactic to take out arithmetic hypotheses from this:

H5 : typed_true tint
         (force_val
            (sem_cmp_pp Clt
               (Vptr end'_b (Ptrofs.add (Ptrofs.add str_ofs Ptrofs.one) (Ptrofs.repr j)))
               (Vptr end'_b end'_ofs))) 

typed_false tint
          (force_val
             (sem_cmp_pp Clt
                (Vptr end'_b
                   (Ptrofs.add (Ptrofs.add (Ptrofs.add str_ofs Ptrofs.one) (Ptrofs.repr j))
                      (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1)))))
                (Vptr end'_b end'_ofs)))


**)
