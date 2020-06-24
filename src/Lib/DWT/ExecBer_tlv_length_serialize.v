Require Import VST.floyd.proofauto.
Require Import Core.Core Core.Notations.

Open Scope IntScope.

Fixpoint required_size_loop n z i l :=
  match n with
  | O => l
  | S n => if z >> i == 0
          then l 
          else required_size_loop n z (i + Int.repr 8) (l + 1)
  end.

Definition required_size z := required_size_loop 4%nat z (Int.repr 8) 1. 


Eval cbv in (required_size_loop 4%nat (Int.repr Int.max_unsigned) 
                                (Int.repr (3 * 8))
                                (Int.repr 0) + Int.repr 3).
Eval cbv in (required_size_loop 4%nat (Int.repr Int.max_unsigned) (Int.repr 8)
                                (Int.repr 1)).

(* Lemma requried_size_succ : forall n l i j,
    required_size_loop n l ((j + 1) * (Int.repr 8)) i + j =
    required_size_loop n l (Int.repr 8) i.
Proof.
  induction n.
  intros.
  simpl. auto.
  admit.
  intros.
  simpl.
  rewrite IHn.
  replace (j * Int.repr 8 + Int.repr 8) with ((j + 1) * Int.repr 8).
Admitted. *)

Lemma requried_size_inc : forall n l i j, required_size_loop n l j (i + 1)%int =
                                     required_size_loop n l j i + 1.
Proof.
  induction n; intros; simpl; auto.
  rewrite IHn.
  break_if; auto.
Qed.

Lemma requried_size_succ : forall n l,
    let j := Int.repr (Z.of_nat n) in
    required_size_loop n l (j * (Int.repr 8)) j =
    required_size_loop n l (Int.repr 8) 0.
Proof.
  induction n.
  intros.
  simpl. auto.
  intros.
  simpl.
  replace (j * Int.repr 8 + Int.repr 8) with ((j + 1) * Int.repr 8).
Admitted.

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

