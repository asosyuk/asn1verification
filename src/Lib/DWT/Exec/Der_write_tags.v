Require Import  VST.floyd.proofauto
 Core.Core Core.Notations Core.Notations Types.
Require Import ExtLib.Structures.Monad.
Require Import Exec.Der_write_TL_m.

Inductive DWT_Error := .

Require Import VST.floyd.sublist.

Fixpoint der_write_tags_loop1 ts sl (ls : list Z) :=
  match ts with
    | [] => ret (ls, encode sl)
    | h :: tl => '(l, encode y) <- der_write_tags_loop1 tl sl ls ;;
                '(encode x) <- der_write_TL_m (Int.repr h) (Int.repr y) 0 0%int;;
                ret (y :: l, encode (x + y))
  end.


Fixpoint der_write_tags_loop2 (ts : list Z) (ls : list int)
         (i : Z) (size : Z) (last_tag_form : Z)  :=
  match ts, ls with
  | t :: tl, l :: ls => 
    let c := if (negb (last_tag_form =? 0) || (i <? (len ts - 1)))%bool
             then Int.one 
             else Int.zero in 
     '(encode z1) <- der_write_TL_m (Int.repr t) l size c ;;
     '(encode z2) <- der_write_tags_loop2 tl ls (i - 1) size last_tag_form ;;     
     ret (encode (z1 + z2))
  | _, _ => ret (encode 0)
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
       else
         '(ls, z) <- der_write_tags_loop1 ts struct_len [] ;;
          _ <- der_write_tags_loop2 ts (map Int.repr ls) l size last_tag_form ;;
          ret (encode (encoded z - struct_len)).



