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

