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
    if negb (size =? 0) 
    then ([Byte.repr ((tclass << 6) or tval)], 1)
    else ([], 1)
  else (* Encoded in > 1 octet *) 
    let required_size := byte_length tval in
    if negb (size =? 0) 
       then let buf0 := (tclass << 6) or 31 in
            if size - 1 <? required_size 
            then ([Byte.repr buf0], required_size + 1)
            else
            (map Byte.repr (buf0 :: (serialize_tag tag)), required_size + 1)
       else ([], required_size + 1).


