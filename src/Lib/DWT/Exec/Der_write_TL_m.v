Require Import ExtLib.Structures.Monad Types.
Require Import Core.Core Core.Notations Core.Tactics.
Require Import Exec.Ber_tlv_tag_serialize
        Exec.Ber_tlv_length_serialize.
Require Import VST.floyd.sublist.

Open Scope Z.


(* Definition der_write_TL tag len size constructed := 
  let (tl, t) := tag_serialize tag (Int.repr size) in
  let (ll, l) := length_serialize len (Int.repr (size - t)) in
  let ls := if eq_dec constructed 0%int 
            then tl ++ ll 
            else (upd_Znth 0 tl (Znth 0 tl or (Int.repr 32))%int) ++ ll in
  if ((t =? -1) || (32 <? t))%bool 
  then ([], -1)
  else if l =? -1 
       then ([], -1) 
       else let s := l + t in
            if 32 <? s 
            then ([], -1)
            else (ls, s). *)

Definition der_write_TL_m tag len size constructed : errW1 asn_enc_rval := 
 pass
   (let (tl, t) := tag_serialize tag (Int.repr size) in
    let (ll, l) := length_serialize len (Int.repr (if size =? 0 then 0 else size - t)) in
    if (32 <? t) || (32 <? t + l) 
    then raise (CustomError DWT_Error)
    else if negb (constructed == 0%int) 
       then ret (encode (t + l), id) 
         else ret (encode (t + l), fun ls =>
                             (upd_Znth 0 ls (Znth 0 ls or (Int.repr 32))%int))).

Lemma tag_serialize_bounds : forall t l, 1 <= snd (tag_serialize t l) <= 6.
  { unfold tag_serialize.
    intros.
    cbn.
    repeat break_if; autorewrite with norm; try nia. } 
Qed.

Lemma length_serialize_bounds : 
  forall t l, 1 <= snd (length_serialize t l) <= 6.
  { unfold length_serialize.
    intros.
    cbn.
    repeat break_if; autorewrite with norm; try nia. } 
Qed.

(*Lemma tag_serialize_bounds :  forall t l z,
    (evalErrW (tag_serialize t l)) [] = Some (encode z) -> 
                               -1 <= z <= 6.
Proof.
 unfold tag_serialize.
 intros.
 repeat break_if; unfold evalErrW in *; cbn in *.
 all: try congruence; repeat break_if; inversion H; 
   try nia.
Qed.


Lemma length_serialize_bounds : forall t l z,
    (evalErrW (length_serialize t l)) [] = Some (encode z) -> 
                               -1 <= z <= 6.
Proof.
 unfold length_serialize.
 intros.
 repeat break_if; unfold evalErrW in *; cbn in *.
 all: try congruence; repeat break_if; inversion H; 
   try nia.
Qed. *)

(*

Lemma der_write_TL_serialize_sum : 
  forall t l s c, 
    let (tls, tl) := tag_serialize t (Int.repr s)  in
    let (lls, ll) := length_serialize l (Int.repr (s - tl)) in
    tl <> -1 ->
    ll <> -1 ->
    tl <= 32 ->
    tl + ll <= 32 ->
    c = 0%int ->
    der_write_TL t l s c = (tls ++ lls, tl + ll).
Proof.
  intros.
  repeat break_let.
  unfold der_write_TL.
  intros Z Z0 Z32 Zplus C.
  erewrite Heqp.
  erewrite Heqp0.
  repeat break_if; try destruct_orb_hyp;
  repeat Zbool_to_Prop; try nia.
  intuition.
  congruence.
Qed.

Lemma der_write_TL_serialize_sum_c : 
  forall t l s c, 
    let (tls, tl) := tag_serialize t (Int.repr s)  in
    let (lls, ll) := length_serialize l (Int.repr (s - tl)) in
    tl <> -1 ->
    ll <> -1 ->
    tl <= 32 ->
    tl + ll <= 32 ->
    c <> 0%int ->
    der_write_TL t l s c = ((upd_Znth 0 tls (Znth 0 tls or (Int.repr 32))%int) ++ lls, tl + ll).
Proof.
  intros.
  repeat break_let.
  unfold der_write_TL.
  intros Z Z0 Z32 Zplus C.
  erewrite Heqp.
  erewrite Heqp0.
  repeat break_if; try destruct_orb_hyp;
  repeat Zbool_to_Prop; try rep_omega.
  erewrite e in C.
  congruence.
  intuition.
Qed.

Definition Z_of_val v := 
  match v with
  | Vptr b i => Ptrofs.unsigned i 
  | _ => 0
  end.

*)
Definition Z_of_val v := 
  match v with
  | Vptr b i => Ptrofs.unsigned i 
  | _ => 0
  end.
