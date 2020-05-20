Require Import Core.Core.

Definition byte_length z :=
  let fix byte_length n i z l:= 
      match n with
      | O => l
      | S n =>
        if z / 2^i =? 0 
        then l 
        else byte_length n (i + 7) z (l + 1)
      end
  in byte_length 4%nat 7 z 1.

Definition byte_length_shift z :=
  let fix byte_length n z i l :=
      match n with
      | O => l
      | S n =>  
        if Z.shiftr z i =? 0
        then l else 
          byte_length n z (i + 7) (l + 1)
      end in
  byte_length 4%nat z 7 1.

Definition serialize_tag tval :=
let fix serialize_tag n i tval :=
  match n with
  | O => [Z.land tval 127]
  | S n => (Z.lor 128 (Z.land (Z.shiftr tval i) 127)) :: serialize_tag n (i - 7) tval
  end in 
 let req_size := byte_length_shift tval in 
 serialize_tag (Z.to_nat (req_size - 1)) ((req_size * 7) - 7)%Z tval.
    
Definition ber_tlv_tag_serialize (tag size : Z) : list byte * Z :=
  let tclass := Z.land tag 3 in 
  let tval := Z.shiftr tag 2 in
  if tval <=? 30 then (* Encoded in 1 octet *)
    if negb (size =? 0) 
    then ([Byte.repr (Z.lor (Z.shiftl tclass 6) tval)], 1)
    else ([], 1)
  else (* Encoded in > 1 octet *) 
    let required_size := byte_length tval in
    if negb (size =? 0) 
       then let buf0 := (Z.lor (Z.shiftl tclass 6) 31) in
            if size - 1 <? required_size 
            then ([], required_size + 1)
            else
            (map Byte.repr (buf0 :: (serialize_tag tag)), required_size + 1)
       else ([], required_size + 1).


