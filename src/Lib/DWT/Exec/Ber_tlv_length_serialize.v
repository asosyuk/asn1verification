Require Import VST.floyd.proofauto.
Require Import Core.Core Core.Notations.

Open Scope IntScope.

Fixpoint required_size_loop n z l :=
  match n with
  | O => l
  | S n => if z >> (Int.repr l) * (Int.repr 8) == 0
          then l 
          else required_size_loop n z (l + 1)%Z
  end.

Definition required_size z := required_size_loop 3%nat z 1%Z. 

Lemma required_size_spec:
         forall l : int, forall i : Z,
           i = 1%Z \/ i = 2 \/ i = 3 \/ i = 4 ->
           (forall j : Z, 0 <= j < i -> 
               (l >> (Int.repr j) * (Int.repr 8)) == 0 = false) ->
                 l >> (Int.repr i) * (Int.repr 8) = 0 -> 
           required_size l = i.
Proof.
  intros l i N B SH.
  repeat break_or_hyp.
  * unfold required_size.
      cbn in *.
      rewrite SH.
      replace (0 == 0) with true by reflexivity;
      auto.
  * unfold required_size.
      cbn.
    do 1 erewrite B.
    autorewrite with norm in *.
    cbn in *.
    rewrite SH;
      replace (0 == 0) with true by reflexivity;
      auto.
    normalize.
    nia.
  * unfold required_size;
      cbn.
    erewrite B.
    erewrite B.
     autorewrite with norm in *;
    cbn in *;
    rewrite SH;
      replace (0 == 0) with true by reflexivity;
      auto.
    all: normalize;
    nia.
  * unfold required_size;
      cbn.
    erewrite B.
    erewrite B.
    erewrite B.
    all: nia.
 (*    autorewrite with norm in *;
    cbn in *;
    rewrite SH;
      replace (0 == 0) with true by reflexivity;
      auto.
    all: normalize;
    nia. *)
Qed.

Fixpoint serialize_length_loop i n l :=
  match n with
  | O => []
  | S n => 
    Int.zero_ext 8 (l >> i) :: serialize_length_loop (i - Int.repr 8) n l 
  end. 

Definition serialize_length l := 
  let s := required_size l in
  let n := Z.to_nat s in
  (Int.repr 128 or (Int.repr s)) :: serialize_length_loop (Int.repr ((s - 1) * 8)) n l.

Fixpoint serialize_length_loop_app s n l :=
  match n with
  | O => []
  | S n => 
     serialize_length_loop_app (s + 1)%Z n l 
                               ++ [Int.zero_ext 8 (l >> Int.repr (s * 8))]
  end. 

Definition serialize_length_app l := 
  let s := required_size l in
  let n := Z.to_nat s in
  (Int.zero_ext 8 (Int.repr 128 or (Int.repr s))) :: serialize_length_loop_app 0%Z n l.

Lemma loop_len_req_size : forall n l i, 
    len (serialize_length_loop_app i n l) = Z.of_nat n.
Proof.
  induction n; intros.
  - reflexivity.
  - simpl.
    erewrite Zlength_app.
    erewrite IHn.
    cbn.
    nia.
Qed.

           
Open Scope Z.

Lemma req_size_32 : forall l, 1 <= required_size l <= 4.
Proof.
  intros.
  unfold required_size.
  cbn.
  repeat break_if; autorewrite with norm; nia.
Qed.

Definition length_serialize len size : list int * Z :=
   if (127 >=? Int.signed len)%Z then
    if eq_dec size 0%int 
    then ([], 1%Z)
    else ([Int.zero_ext 8 len], 1%Z) 
  else let r := required_size len in 
       if (r <? Int.unsigned size)%Z 
       then (serialize_length_app len, (r + 1)%Z) 
       else ([], r + 1).

Lemma tag_serialize_req_size : forall l s, 
    let (ls, z) := length_serialize l s in
    len ls <= z.
Proof.
intros.
unfold length_serialize.
pose proof (req_size_32 l).
repeat break_if; auto; try list_solve.
autorewrite with sublist list.
unfold serialize_length_app.
autorewrite with sublist.
setoid_rewrite loop_len_req_size.
erewrite Z2Nat.id; try nia.
Qed.

Lemma length_serialize_req_size_gt0 : forall l s, 
     0 < snd (length_serialize l s).
Proof.
intros l s.
unfold length_serialize.
pose proof (req_size_32 l).
repeat break_if; auto; unfold snd in *; try nia.
Qed.

Lemma shr_lt_zero_32: 
  forall x, Int.shr x (Int.repr (Int.zwordsize)) 
       = if Int.lt x Int.zero then Int.mone else Int.zero.
Proof.
  intros. apply Int.same_bits_eq; intros.
  rewrite Int.bits_shr; auto.
  rewrite Int.unsigned_repr.
  transitivity (Int.testbit x (Int.zwordsize - 1)).
  f_equal. destruct (zlt (i + (Int.zwordsize)) Int.zwordsize); try omega.
  rewrite Int.sign_bit_of_unsigned.
  unfold Int.lt. rewrite Int.signed_zero. unfold Int.signed.
  destruct (zlt (Int.unsigned x) Int.half_modulus).
  rewrite zlt_false. rewrite Int.bits_zero; auto.
  generalize (Int.unsigned_range x); omega.
  rewrite zlt_true. rewrite Int.bits_mone; auto.
  generalize (Int.unsigned_range x); omega.
  generalize Int.wordsize_max_unsigned; omega. 
Qed.
