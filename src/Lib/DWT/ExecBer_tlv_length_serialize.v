Require Import VST.floyd.proofauto.
Require Import Core.Core Core.Notations.

Open Scope IntScope.

Fixpoint required_size_loop n z l :=
  match n with
  | O => l
  | S n => if z >> (l * Int.repr 8) == 0
          then l 
          else required_size_loop n z (l + Int.repr 1)
  end.

Definition required_size z := required_size_loop 4%nat z (Int.repr 1). 

(* Lemma requried_size_inc : forall n l i j, required_size_loop n l j (i + 1)%int =
                                     required_size_loop n l j i + 1.
Proof.
  induction n; intros; simpl; auto.
  rewrite IHn.
  break_if; auto.
Qed. *)

Lemma required_size_spec:
         forall l i : int,
           i = Int.repr 1 \/ i = Int.repr 2 \/ i = Int.repr 3 \/ i = Int.repr 4 ->
           (forall j : int, 0 <= Int.unsigned j < Int.unsigned i -> 
               (l >> j * Int.repr 8) == 0 = false) ->
                 l >> (i * Int.repr 8) = 0 -> 
           required_size l = i.
Proof.
  intros l i N B SH.
  repeat break_or_hyp.
  * unfold required_size;
      cbn;
      rewrite SH;
      replace (0 == 0) with true by reflexivity;
      auto.
  * unfold required_size;
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
     autorewrite with norm in *;
    cbn in *;
    rewrite SH;
      replace (0 == 0) with true by reflexivity;
      auto.
    all: normalize;
    nia.
Qed.

(* Fixpoint required_size_loop n l :=
  match n with
  | O => 1
  | S m => 
    let s := Int.repr (Z.of_nat n) in
    if (l >> s * Int.repr 8)%int == 0
    then required_size_loop m l
    else s
  end.

Definition required_size l := required_size_loop 4%nat l. *)

Fixpoint serialize_length_loop i n l :=
  match n with
  | O => []
  | S n => (l >> i) :: serialize_length_loop (i - Int.repr 8) n l 
  end. 

Definition serialize_length l := 
  let s := required_size l in
  let n := Z.to_nat (Int.unsigned s) in
  (Int.repr 128 or s) :: serialize_length_loop ((s - 1) * Int.repr 8) n l.
 
Definition ber_tlv_length_serialize len size : list int * int :=
   if (127 >=? Int.signed len)%Z then
    if eq_dec size 0 
    then ([], 1)
    else ([len], 1) 
  else let r := required_size len in 
       if (r <u size) 
       then (serialize_length len, r + 1) 
       else ([], r + 1).

