Require Import Core.Core Core.Notations Core.Notations Types.
Require Import ExtLib.Structures.Monad.
Require Import Der_write_TL.

(* Writes header octets *)
(*Definition der_write_tags (td : TYPE_descriptor) : errW1 asn_enc_rval :=
  match decoder_type td with
  | BOOLEAN_t => tell1 (map Byte.repr [1; 1]) >>= fun _ => ret (encode 2)
  | _ => raise (CustomError NotBoolean)
  end. *)

Definition index (a : Z) (ls : list Z) :=
  let fix index (a : Z) (ls : list Z) (i : Z) :=
      match ls with
      | [] => -1
      | h :: tl => if h =? a then i else index a tl (i + 1)
      end in
  index a ls 0.

Import MonadNotation.

Inductive DWT_Error := .

Fixpoint required_size (ls : list Z) (ls' : list Z) (l : Z) : errW1 asn_enc_rval :=
  match ls with
  | [] => tell1 (map Byte.repr ls') >>= fun _ => ret (encode l)
  | t :: tl => 
    let (_, i) := der_write_TL (Int.repr t) (Int.repr l) 0 Int.zero in
    if i =? -1 
    then raise (CustomError DWT_Error)
    else required_size tl (l::ls') (l + i)
  end.

Fixpoint WT (ts : list Z) (ls : list Z) (i : Z) (size : Z) (last_tag_form : Z) :=
  match ts, ls with
  | [], [] => ([], 0)
  | t :: tl, l :: ls => 
    let c := if (negb (last_tag_form =? 0) || (i <? (len ts - 1)))%bool
             then Int.one 
             else Int.zero in 
    let (k1, z1) := der_write_TL (Int.repr t) (Int.repr l) size c in
    let (k2, z2) := WT tl ls (i - 1) size last_tag_form in
    (k1 ++ k2, z1 + z2)
  | _, _ => ([], -1)
  end.

Definition der_write_tags (td : TYPE_descriptor) 
           (struct_len : Z) (tag_mode : Z) (last_tag_form : Z) (tag : Z) (size : Z) :=
  let ts := tags td in
  let l := len ts in
  if 4 <? l + 1 
  then ([], -1)
  else let tag_count := 
           if tag_mode =? 0
           then l + 1 
           else l in
       if tag_count =? 0 
       then ([], 0)
       else let (ls, s) := required_size ts [] struct_len in
            let (rs, z) := WT ts ls l size last_tag_form in
            (rs, z - struct_len).
                    


(* Writes header octets *)
Definition der_write_tags (td : TYPE_descriptor) : errW1 asn_enc_rval :=
  match decoder_type td with
  | BOOLEAN_t => tell1 (map Byte.repr [1; 1]) >>= fun _ => ret (encode 2)
  | _ => raise (CustomError NotBoolean)
  end.

Theorem eval_dwt_boolean : forall td,
  decoder_type td = BOOLEAN_t ->
  evalErrW (der_write_tags td) [] = Some (encode 2).
Proof.
  intros.
  unfold evalErrW, der_write_tags; rewrite H; cbn.
  reflexivity.
Qed.

Theorem exec_dwt_boolean : forall td,
  decoder_type td = BOOLEAN_t ->
  execErrW (der_write_tags td) [] = Some [Byte.one; Byte.one].
Proof.
  intros.
  unfold execErrW, der_write_tags; rewrite H; cbn.
  reflexivity.
Qed.    
  
