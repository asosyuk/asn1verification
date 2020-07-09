Require Import VST.floyd.proofauto.
Require Import Core.Core Core.Notations Core.Tactics.
Require Import ExecBer_tlv_tag_serialize
        ExecBer_tlv_length_serialize.

Open Scope Z.

Definition der_write_TL tag len size := 
  let (tl, t) := tag_serialize tag (Int.repr size) in
  let (ll, l) := length_serialize len (Int.repr (size - t)) in
  let ls := tl ++ ll in
  if ((t =? -1) || (32 <? t))%bool 
  then ([], -1)
  else if l =? -1 
       then (ls, -1) 
       else let s := l + t in
            if 32 <? s 
            then ([], -1)
            else (tl ++ ll, s).

Lemma tag_serialize_bounds : forall t l, -1 <= snd (tag_serialize t l) <= 6.
  { unfold tag_serialize.
    intros.
    cbn.
    repeat break_if; autorewrite with norm; try nia. } 
Qed.

Lemma length_serialize_bounds : 
  forall t l, -1 <= snd (length_serialize t l) <= 6.
  { unfold length_serialize.
    intros.
    cbn.
    repeat break_if; autorewrite with norm; try nia. } 
Qed.

Lemma der_write_TL_serialize_sum : 
  forall t l s, 
    let (tls, tl) := tag_serialize t (Int.repr s)  in
    let (lls, ll) := length_serialize l (Int.repr (s - tl)) in
    tl <> -1 ->
    ll <> -1 ->
    tl <= 32 ->
    tl + ll <= 32 ->
    der_write_TL t l s = (tls ++ lls, tl + ll).
Proof.
  intros.
  repeat break_let.
  unfold der_write_TL.
  intros Z Z0 Z32 Zplus.
  erewrite Heqp.
  erewrite Heqp0.
  repeat break_if; try destruct_orb_hyp;
  repeat Zbool_to_Prop; try nia.
  intuition.
Qed.

Definition Z_of_val v := 
  match v with
  | Vptr b i => Ptrofs.unsigned i 
  | _ => 0
  end.
