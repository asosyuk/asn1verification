Require Import VST.floyd.proofauto.
Require Import Core.Core Core.Notations Core.Notations Types.
Require Import ExtLib.Structures.Monad.
Require Import BFT.Exec BFL.Exec VST.floyd.sublist.

(* assuming ctx is not null *)

Definition ASN__STACK_OVERFLOW_CHECK used_stack max_stack_size := 
  if eq_dec max_stack_size 0 
  then 0
  else if  max_stack_size <? used_stack
       then -1
       else 0.

Open Scope bool.

Definition ber_check_tags_primitive ts td ctx size sizeofval sizemax: 
  option (Z * Z) :=
  if ASN__STACK_OVERFLOW_CHECK 0 ctx =? 0
  then let (tag_len, tlv_tag) := ber_fetch_tags ts size 0 sizeofval in
       if (tag_len =? -1) || (tag_len =? 0) then None 
       else 
         if (tlv_tag =? nth O (tags td) 0) 
         then
           let (len_len, tlv_len) := ber_fetch_len (sublist 1 (len ts) ts)
                                                   0 0 (size - tag_len) sizeofval sizemax in
           if (len_len =? -1) || (len_len =? 0) then None 
           else 
             let limit_len := tlv_len + tag_len + len_len in
             if limit_len <? 0 then None
             else Some (tlv_len, tag_len + len_len)
         else None
  else None.

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
