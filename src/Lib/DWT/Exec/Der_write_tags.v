Require Import Core.Core Core.Notations Core.Notations Types.
Require Import ExtLib.Structures.Monad.
Require Import Der_write_TL_m.

Inductive DWT_Error := .

Require Import VST.floyd.sublist.

Fixpoint der_write_tags_loop1 (n : nat) (lens : list Z) (ts : list Z) (l : Z) 
  : errW1 (asn_enc_rval * list Z) :=
  match n with
  | O => ret (encode l, lens)
  | S n => 
    '(encode i) <-
     der_write_TL_m (Int.repr (Znth (Z.of_nat (S n)) ts)) (Int.repr l) 0 0%int ;;
     der_write_tags_loop1 n (l - i :: lens) ts (l + i)
  end.

Lemma der_write_tags_loop1_fail : forall n ls l s e ls',
    (0 < n)%nat ->
    der_write_TL_m (Int.repr (Znth (Z.of_nat n) ls)) (Int.repr l) 0 0%int s = inl e ->
    der_write_tags_loop1 n ls' ls l s = inl e.
Proof.
  induction n;
  intros until ls';
  intros N;
  intros B.
  - nia.
  - simpl.
    simpl in B.
    erewrite B.
    auto.
Qed. 

Fixpoint der_write_tags_loop2 (ts : list Z) (ls : list int)
         (i : Z) (size : Z) (last_tag_form : Z)
  : errW1 asn_enc_rval :=
  match ts, ls with
  | [], [] => ret (encode 0)
  | t :: tl, l :: ls => 
    let c := if (negb (last_tag_form =? 0) || (i <? (len ts - 1)))%bool
             then Int.one 
             else Int.zero in 
     '(encode z1) <- der_write_TL_m (Int.repr t) l size c ;;
     '(encode z2) <- der_write_tags_loop2 tl ls (i - 1) size last_tag_form ;;
     ret (encode (z1 + z2))
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
       else
         '(_, ls) <- listen (der_write_tags_loop1 (length ts) [] ts struct_len) ;;
          z <- der_write_tags_loop2 ts ls l size last_tag_form ;;
          ret (encode (encoded z - struct_len)).
