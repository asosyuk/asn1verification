Require Import VST.floyd.proofauto.
Require Import Core.Core Core.Notations.

Open Scope IntScope.

Program Fixpoint required_size_loop v i l {measure (Z.to_nat (Int.unsigned (Int.repr 32 - i)))}:=
  if (i <u Int.repr 32) 
  then if (v >> i) == 0
       then l
       else required_size_loop v (i + Int.repr 8) (l + 1)
  else l.
Obligation 1.
Admitted.

Definition required_size v := required_size_loop v (Int.repr 8) 1.

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

