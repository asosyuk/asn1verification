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

Require Import ExtLib.Structures.Monad Types.

Inductive DWT_Error := .

 Delimit Scope monad_scope with monad.

  Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 58, left associativity) : monad_scope.
  Notation "f =<< c" := (@bind _ _ _ _ c f) (at level 61, right associativity) : monad_scope.
  Notation "f >=> g" := (@mcompose _ _ _ _ _ f g) (at level 55, right associativity) : monad_scope. 

  Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity) : monad_scope.

  Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
    (at level 61, right associativity) : monad_scope.

  Notation "' pat <- c1 ;; c2" :=
    (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
    (at level 61, pat pattern, c1 at next level, right associativity) : monad_scope.

(*
Definition tag_serialize (tag size : int): errW1 asn_enc_rval :=
  let tclass := (tag & Int.repr 3)%int in 
  let tval := tag >>u (Int.repr 2) in
  if 30 >=? Int.unsigned tval then
    if eq_dec size 0%int 
    then raise (CustomError DWT_Error)
    else (tell1 [Int.zero_ext 8 ((tclass << Int.repr 6) or tval)]%int 
               ;; ret (encode 1))
  else 
    let r := required_size tval in
    if eq_dec size 0%int 
       then raise (CustomError DWT_Error)
       else
         let t := (Int.zero_ext 8 ((tclass << Int.repr 6) or Int.repr 31))%int in
         tell1 [t] ;; 
               if Int.unsigned size - 1 <? r
               then raise (CustomError DWT_Error)
               else
                 tell1 (serialize_tag tval) ;; ret (encode (r + 1)). *)

Definition tag_serialize (tag size : int): errW1 asn_enc_rval :=
  let tclass := (tag & Int.repr 3)%int in 
  let tval := tag >>u (Int.repr 2) in
  if 30 >=? Int.unsigned tval then
    if eq_dec size 0%int 
    then ret (encode 1)
    else tell1 [Int.zero_ext 8 ((tclass << Int.repr 6) or tval)]%int 
               ;; ret (encode 1)
  else 
    let r := required_size tval in
    if eq_dec size 0%int 
    then (if Int.unsigned size - 1 <? r
          then ret (encode (r + 1))
          else
            tell1 (serialize_tag tval) ;; ret (encode (r + 1)))
       else
         let t := (Int.zero_ext 8 ((tclass << Int.repr 6) or Int.repr 31))%int in
         tell1 [t] ;; 
               if Int.unsigned size - 1 <? r
               then  ret (encode (r + 1))
               else
                 tell1 (serialize_tag tval) ;; ret (encode (r + 1)).

(*
Lemma tag_serialize_req_size : forall l s, 
    let (ls, z) := tag_serialize l s in
    z <> -1 -> len ls = z.
Proof.
intros.
unfold tag_serialize.
repeat break_if; auto; try nia.
intros.
pose proof (req_size_32 (l >>u Int.repr 2)).
unfold serialize_tag.
autorewrite with sublist list;
erewrite loop_len_req_size;
erewrite Z2Nat.id; try nia.
Qed.

Lemma tag_serialize_req_size_gt0 : forall l s, 
    let (ls, z) := tag_serialize l s in
    z <> -1 -> 0 < z.
Proof.
intros.
unfold tag_serialize.
repeat break_if; auto; try nia.
intros.
pose proof (req_size_32 (l >>u Int.repr 2)).
nia.
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
*)
