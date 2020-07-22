Require Import Core.Core Core.Notations Core.Notations Types.
Require Import ExtLib.Structures.Monad.
Require Import Der_write_TL_m.

Inductive DWT_Error := .

Fixpoint required_size (ls : list Z)  (l : Z) : errW1 asn_enc_rval :=
  match ls with
  | [] => ret (encode l)
  | t :: tl => 
    i <- der_write_TL_m (Int.repr t) (Int.repr l) 0 Int.zero ;;
      match i with encode i => required_size tl (l + i) end
  end.

Fixpoint WT (ts : list Z) (ls : list int) (i : Z) (size : Z) (last_tag_form : Z)
  : errW1 asn_enc_rval:=
  match ts, ls with
  | [], [] => ret (encode 0)
  | t :: tl, l :: ls => 
    let c := if (negb (last_tag_form =? 0) || (i <? (len ts - 1)))%bool
             then Int.one 
             else Int.zero in 
     z1 <- der_write_TL_m (Int.repr t) l size c ;;
     z2 <- WT tl ls (i - 1) size last_tag_form ;;
     match z1, z2 with encode z1, encode z2 =>
     ret (encode (z1 + z2)) end
  | _, _ => raise (CustomError DWT_Error)
  end.

Definition der_write_tags (td : TYPE_descriptor) 
           (struct_len : Z) (tag_mode : Z)
           (last_tag_form : Z) (tag : Z) (size : Z) : errW1 asn_enc_rval :=
  let ts := tags td in
  let l := len ts in

  if 4 <? l + 1 
  then raise (CustomError DWT_Error)
  else if (if tag_mode =? 0
           then l + 1 
           else l) =? 0 
       then ret (encode 0)
       else '(_, ls) <- listen (required_size ts struct_len) ;;
             z <- WT ts ls l size last_tag_form ;;
             match z with encode z => ret (encode (z - struct_len)) end.
