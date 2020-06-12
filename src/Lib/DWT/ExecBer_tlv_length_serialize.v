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

(* Definition serialize_length l := 
  let n := Z.to_nat (Int.unsigned (required_size l)) 
  serialize_length_loop n *)
  
Fixpoint serialize_tag_loop  n i tval :=
  match n with
  | O => []
  | S n => (Int.repr 128 or (tval >> i & Int.repr 127)) 
            :: serialize_tag_loop n (i - Int.repr 7) tval
  end. 

Definition serialize_tag' tval :=
  let s := byte_length' tval in 
  let n := Z.to_nat (Int.unsigned (s - 1)) in
  serialize_tag_loop n (s * Int.repr  7 - Int.repr 7) tval
                     ++[(tval >> Int.repr 2) & Int.repr 127]. 

Definition ber_tlv_length_serialize len size : list int * int :=
   if (127 >=? Int.signed len)%Z then
    if eq_dec size 0 
    then ([], 1)
    else ([len], 1) 
  else if (size <=u required_size len) 
       then ([], required_size len + 1)
       else ([],1).

