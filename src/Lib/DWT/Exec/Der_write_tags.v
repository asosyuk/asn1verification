Require Import Core.Core Core.Notations Core.Notations Types.
Require Import ExtLib.Structures.Monad.
Require Import Der_write_TL_m.

Inductive DWT_Error := .

Fixpoint der_write_tags_loop1 (tags : list Z) (length : Z) : errW1 asn_enc_rval :=
  match tags with
  | [] => ret (encode length)
  | tag :: tl => 
    i <- der_write_TL_m (Int.repr tag) (Int.repr length) 0 0%int ;;
    der_write_tags_loop1 tl (length + encoded i)
  end.

Fixpoint der_write_tags_loop2 (ts : list Z) (ls : list int)
         (i : Z) (size : Z) (last_tag_form : Z)
  : errW1 asn_enc_rval:=
  match ts, ls with
  | [], [] => ret (encode 0)
  | t :: tl, l :: ls => 
    let c := if (negb (last_tag_form =? 0) || (i <? (len ts - 1)))%bool
             then Int.one 
             else Int.zero in 
     z1 <- der_write_TL_m (Int.repr t) l size c ;;
     z2 <- der_write_tags_loop2 tl ls (i - 1) size last_tag_form ;;
     ret (encode (encoded z1 + encoded z2))
  | _, _ => raise (CustomError DWT_Error)
  end.

Definition der_write_tags (td : TYPE_descriptor) 
           (struct_len : Z) (tag_mode : Z)
           (last_tag_form : Z) (tag : Z)
           (size : Z) : errW1 asn_enc_rval :=

  let ts := tags td in
  let l := len ts in

  if 4 <? l + 1 
  then raise (CustomError DWT_Error)
  else if (if tag_mode =? 0
           then l + 1 
           else l) =? 0 
       then ret (encode 0)
       else '(_, ls) <- listen (der_write_tags_loop1 ts struct_len) ;;
             z <- der_write_tags_loop2 ts ls l size last_tag_form ;;
             ret (encode (encoded z - struct_len)).
