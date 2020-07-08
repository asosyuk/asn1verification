Require Import VST.floyd.proofauto.
Require Import Core.Core Core.Notations.

Open Scope IntScope.

Fixpoint required_size_loop n z l :=
  match n with
  | O => l
  | S n => if z >>u (Int.repr l) * (Int.repr 7) == 0
          then l 
          else required_size_loop n z (l + 1)%Z
  end.

Definition required_size z := required_size_loop 4%nat z 1%Z. 

Lemma required_size_spec:
         forall l : int, forall i : Z,
           i = 1%Z \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 ->
           (forall j : Z, 0 <= j < i -> 
               (l >>u (Int.repr j) * (Int.repr 7)) == 0 = false) ->
                 l >>u (Int.repr i) * (Int.repr 7) = 0 -> 
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
     rewrite SH;
      replace (0 == 0) with true by reflexivity;
      auto.
    all: nia.
  * unfold required_size;
      cbn.
    erewrite B.
    erewrite B.
    erewrite B.
     erewrite B.
    all: nia.
Qed.


Fixpoint serialize_tag_loop s n t :=
  match n with
  | O => []
  | S n => 
     let b := Int.zero_ext 8
              (Int.repr 128 or 
                        ((t >>u Int.repr (s * 7)) & Int.repr 127)) in
     serialize_tag_loop (s + 1)%Z n t ++ [b]
  end. 

Definition serialize_tag t := 
  let s := required_size t in
  let n := Z.to_nat (s - 1) in
  serialize_tag_loop 0%Z n t ++ [Int.zero_ext 8 (t & Int.repr 127)].

Lemma loop_len_req_size : forall n l i, 
    len (serialize_tag_loop i n l) = Z.of_nat n.
Proof.
  induction n; intros.
  - reflexivity.
  - simpl.
    erewrite Zlength_app.
    erewrite IHn.
    cbn.
    nia.
Qed.
           
Lemma req_size_32 : forall l, 1 <= required_size l <= 5.
Proof.
  intros.
  unfold required_size.
  cbn.
  repeat break_if; autorewrite with norm; nia.
Qed.

Open Scope Z.

Definition ber_tlv_tag_serialize (tag size : int): list int * Z :=
  let tclass := (tag & Int.repr 3)%int in 
  let tval := tag >>u (Int.repr 2) in
  if 30 >=? Int.unsigned tval then
    if eq_dec size 0%int 
    then ([], -1)
    else ([Int.zero_ext 8 ((tclass << Int.repr 6) or tval)]%int, 1)
  else 
    let r := required_size tval in
    if eq_dec size 0%int 
       then ([], -1)
       else let t := (Int.zero_ext 8 ((tclass << Int.repr 6) or Int.repr 31))%int in
            if Int.unsigned size - 1 <? r
            then ([t], -1)
            else
            (t :: (serialize_tag tval), r + 1).

Lemma tag_serialize_req_size : forall l s, 
    let (ls, z) := ber_tlv_tag_serialize l s in
    z <> -1 -> len ls = z.
Proof.
intros.
unfold ber_tlv_tag_serialize.
repeat break_if; auto; try nia.
intros.
pose proof (req_size_32 (l >>u Int.repr 2)).
unfold serialize_tag.
autorewrite with sublist list;
erewrite loop_len_req_size;
erewrite Z2Nat.id; try nia.
Qed.

Lemma shr_lt_zero_35: 
             forall x, Int.shru x (Int.repr 35)
                  = if Int.ltu x Int.zero then Int.mone else Int.zero.
Proof.
  intros. apply Int.same_bits_eq; intros.
  rewrite Int.bits_shru; auto.
  rewrite Int.unsigned_repr.
  transitivity (Int.testbit x (Int.zwordsize - 1)).
  f_equal. 
Admitted.
