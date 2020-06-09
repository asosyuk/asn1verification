Require Import VST.floyd.proofauto.
Require Import Core.Core Core.Notations.

Definition byte_length z :=
  let fix byte_length n z i l :=
      match n with
      | O => l
      | S n => if z >> i =? 0
               then l 
               else byte_length n z (i + 7) (l + 1)
      end in
  byte_length 4%nat z 7 1.

Definition serialize_tag tval :=
let fix serialize_tag n i tval :=
  match n with
  | O => [tval & 127]
  | S n => (128 or (tval >> i & 127)) :: serialize_tag n (i - 7) tval
  end in 
 let req_size := byte_length tval in 
 serialize_tag (Z.to_nat (req_size - 1)) ((req_size * 7) - 7)%Z tval.
    
Definition ber_tlv_tag_serialize (tag size : Z): list byte * Z :=
  let tclass := tag & 3 in 
  let tval := tag >> 2 in
  if tval <=? 30 then (* Encoded in 1 octet *)
    if eq_dec size 0 
    then ([], 1)
    else ([Byte.repr ((tclass << 6) or tval)], 1) 
  else (* Encoded in > 1 octet *) 
    let required_size := byte_length tval in
    if eq_dec size 0 
       then ([], required_size + 1)
       else let buf0 := (tclass << 6) or 31 in
            if size - 1 <? required_size 
            then ([Byte.repr buf0], required_size + 1)
            else
            (map Byte.repr (buf0 :: (serialize_tag tag)), required_size + 1).

Open Scope IntScope.

Fixpoint byte_length'_loop n z i l :=
  match n with
  | O => l
  | S n => if z >> i == 0
          then l 
          else byte_length'_loop n z (i + Int.repr 7) (l + 1)
  end.

Definition byte_length' z := byte_length'_loop 4%nat z (Int.repr 7) 1.

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

Definition ber_tlv_tag_serialize' (tag size : int): list int * int :=
  let tclass := tag & Int.repr 3 in 
  let tval := tag >> Int.repr 2 in
  if tval <=u Int.repr 30 then
    if eq_dec size 0 
    then ([], 1)
    else ([(tclass << Int.repr 6) or tval], 1) 
  else 
    let required_size := byte_length' tval in
    if eq_dec size 0 
       then ([], required_size + 1)
       else let buf0 := (tclass << Int.repr 6) or Int.repr 31 in
            if (size - 1 <u required_size)
            then ([buf0], required_size + 1)
            else
            (buf0 :: (serialize_tag' tag), required_size + 1).
