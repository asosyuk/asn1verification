Require Import VST.floyd.proofauto.
Require Import Core.Core Core.Notations Core.Notations Types.
Require Import ExtLib.Structures.Monad.
Require Import BFT.Exec BFL.Exec VST.floyd.sublist.

(* assuming ctx is not null *)

Open Scope Z.

Definition ASN__STACK_OVERFLOW_CHECK used_stack max_stack_size := 
  if eq_dec max_stack_size 0 
  then 0
  else if  max_stack_size <? used_stack
       then -1
       else 0.

Open Scope bool.
Open Scope int.
Definition ber_check_tags_primitive ts td ctx size sizeofval sizemax: 
  option (int * int) :=
  if ASN__STACK_OVERFLOW_CHECK 0 ctx =? 0
  then let (tag_len, tlv_tag) := ber_fetch_tags ts size  in
       if (tag_len == Int.repr (-1)) || (tag_len == 0)%int then None 
       else 
         if (tlv_tag == Int.repr (Znth 0 (tags td))) 
         then
           let (len_len, tlv_len) := ber_fetch_len 
                                       (sublist (Int.signed tag_len)
                                                (len ts) ts)
                                                0 0%int
                                       (Int.repr size -
                                                  tag_len)%int 
                                                sizeofval sizemax in
           if (len_len == Int.repr (-1)) || (len_len == 0%int) then None 
           else 
             if ((127 <? Int.signed tag_len) ||
                 (127 <? Int.signed len_len) ||
                  (Int.max_signed - 255 <? Int.signed tlv_len))
             then None 
             else Some (tlv_len, tag_len + len_len)%int
         else None
  else None.

Lemma ber_fetch_len_bounds : 
  forall ptr isc len_r size sizeofval,
   0 <= size <= Int.max_signed ->
   Int.min_signed <= Int.signed len_r <= Int.max_signed ->
   0 <= Int.signed (fst (ber_fetch_len ptr isc len_r (Int.repr size)
                                          sizeofval 
                                          (Int.repr Int.max_signed)))
    <= size.
Proof.
  intros. 
  unfold ber_fetch_len.
  Require Import Core.Tactics.
  repeat break_match; simpl;
    subst;
    try replace (Int.signed 0%int) with 0%Z by auto with ints;
     try replace (Int.signed 1%int) with 1%Z by auto with ints;
      try assert (Int.signed size <> 0%Z) by admit;
     try rep_lia.
  1-3: unfold Int.neg; strip_repr.
  Admitted.

Lemma ber_fetch_len_bounds_snd : 
  forall ptr len_r size sizeofval,
   0 <= Int.signed len_r <= Int.max_signed ->
   (0 <= Int.signed (snd (ber_fetch_len ptr 0 len_r (Int.repr size)
                                          sizeofval 
                                          (Int.repr Int.max_signed))))%Z.
Proof.
  intros. 
  unfold ber_fetch_len.
  Require Import Core.Tactics.
  repeat break_match; simpl;
    subst;
    try replace (Int.signed 0%int) with 0%Z by auto with ints;
     try replace (Int.signed 1%int) with 1%Z by auto with ints;
     try rep_lia.
  admit.
  simpl in Heqb. discriminate.
  destruct_orb_hyp.
  Zbool_to_Prop.
  generalize H1.
  unfold Int.lt.
  break_if. discriminate.
  generalize g.
  replace (Int.signed 0%int) with 0%Z by auto with ints.
  strip_repr.
Admitted.

Lemma ber_fetch_tags_bounds : 
  forall ptr size,
    0 <= size <= Int.max_signed ->
   0 <= Int.signed (fst (Exec.ber_fetch_tags ptr size)) 
   <= size.
Proof.
 Admitted. 

(*Lemma ber_check_tags_primitive_bounds_fst : 
  forall ts td ctx size sizeofval p,  
    ber_check_tags_primitive ts td ctx size sizeofval (Int.repr Int.max_signed)
    = Some p ->
    Int.min_signed <= fst p <= Int.max_signed.
Proof.
  intros.
  unfold ber_check_tags_primitive in H.
  repeat break_match; try congruence.
  inversion H. simpl. 
  replace z1 with (snd (ber_fetch_len (sublist 1 (len ts) (map Int.unsigned ts)) 0 0
            (size - z) sizeofval Int.max_signed)). 
  eapply ber_fetch_len_bounds.
  admit. 
   Require Import VstTactics Core.Tactics.
   strip_repr.
   erewrite Heqp1. auto.
Admitted.

Lemma ber_check_tags_primitive_bounds_snd : 
  forall ts td ctx size sizeofval p,  
    ber_check_tags_primitive ts td ctx size sizeofval Int.max_signed = Some p ->
    Int.min_signed <= snd p <= Int.max_signed.
Proof.
  intros.
  unfold ber_check_tags_primitive in H.
  repeat break_match; try congruence.
  inversion H. simpl. 
Admitted.

Lemma ber_fetch_len_bounds : 
  forall ptr isc len_r size sizeofval,
   Int.min_signed <= hd 0 ptr <= Int.max_signed ->
   Int.min_signed <= len_r <= Int.max_signed ->
   Int.min_signed <= fst (ber_fetch_len ptr isc len_r size sizeofval Int.max_signed) <= Int.max_signed.
Proof.
  intros. 
  unfold ber_fetch_len.
  repeat break_match; simpl; try lia.
  cbn. lia. 
  Require Import VstTactics Core.Tactics.
  all: try strip_repr.
  unfold bfl_loop in Heqp.
  unfold aux_loop in *.
  destruct ptr.
  cbn in Heqp.
  discriminate.
Admitted.

Lemma ber_fetch_tags_bounds : 
  forall ptr size,
   Int.min_signed <= fst (Exec.ber_fetch_tags ptr size) <= Int.max_signed.
Proof.
 Admitted. *)

(*
Parameter ber_fetch_tag : Z -> Z.
Parameter ber_fetch_length : bool-> Z -> Z.
Parameter constructed : list Z -> bool.
Parameter ber_check_tags_loop : Z -> Z -> Z -> option Z.

Open Scope bool.

(* checks the tag, outputs consumed length and expected length *)
Definition ber_check_tags ts td ctx tag_mode size step : 
  option Z :=
  if asn_stack_overflow_check ctx 
  then Some (-1) 
  else 
    let tagno := step + (if tag_mode =? 1 then -1 else 0) in                
    if (tag_mode =? 0) || (0 <? len (tags td))
    then 
      let tag_len := ber_fetch_tag size in
      if (tag_len =? -1) || (tag_len =? 0) 
      then None 
      else let len_len := ber_fetch_length (constructed ts) (size - tag_len) in
           if (len_len =? -1) || (len_len =? 0) 
           then None
           else let size := size - tag_len - len_len in
                ber_check_tags_loop tagno size step
    else ber_check_tags_loop tagno size step.
                 
(*  
Theorem ber_check_tags_bool_res : forall td ls,
    decoder_type td = BOOLEAN_t ->
    ber_check_tags td ls = Some (mk_check_tag 2 1) 
    \/ ber_check_tags td ls = None.
Proof.
  intros.
  unfold ber_check_tags; rewrite H.
  repeat break_match; auto.
Qed.

Theorem ber_check_tags_bool_Some : forall td ls,
    decoder_type td = BOOLEAN_t ->
    ber_check_tags td (Byte.one::Byte.one::ls) = 
    Some (mk_check_tag 2 1).
Proof.
  intros.
  unfold ber_check_tags.
  rewrite H.
  reflexivity.
Qed.

Theorem ber_check_tags_bool_Some_intro : forall td ls,
    decoder_type td = BOOLEAN_t ->
    ber_check_tags td ls = Some (mk_check_tag 2 1) ->
    exists tl, ls = 1%byte::1%byte::tl.
Proof.
  intros td ls DT.
  unfold ber_check_tags.
  repeat break_match; try discriminate.
  intros.
  unfold andb in Heqb; repeat break_match_hyp; try discriminate.
  pose proof Byte.eq_spec i 1%byte as T; rewrite Heqb0 in T.
  pose proof Byte.eq_spec i0 1%byte as T1; rewrite Heqb in T1.
  rewrite T, T1.
  exists l0; reflexivity.
Qed.
*) *)
