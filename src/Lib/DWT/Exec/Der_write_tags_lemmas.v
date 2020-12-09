Require Import  VST.floyd.proofauto
 Core.Core Core.Notations Core.Notations Types.
Require Import ExtLib.Structures.Monad.
Require Import Exec.Der_write_TL_m.
Require Import Exec.Der_write_tags.

Inductive DWT_Error := .

Require Import VST.floyd.sublist.

Lemma loop1_app : forall l1 l2 z e i ls, 
    der_write_tags_loop1 l2 z ls i = inl e ->
    der_write_tags_loop1 (l1 ++ l2) z ls i = inl e.
Proof.
  induction l1.
  - auto.
  - intros.
    simpl.
    erewrite IHl1; auto.
Qed.

Lemma write_TL_to_loop1 :  forall e h tl l ls sl ln i,
      der_write_tags_loop1 tl sl i [] = inr (ls, (ln, encode l)) ->
      der_write_TL_m (Int.repr h) (Int.repr l) 0 0%int ls = inl e ->
      der_write_tags_loop1 (h :: tl) sl i [] = inl e.
Proof.
  intros.
  simpl.
  erewrite H.
  erewrite H0.
  auto.
Qed.

Lemma write_TL_to_loop1_sublist :  
  forall j e ts l ls sl ln i,
    0 <= j < len ts ->
    der_write_tags_loop1
      (sublist (len ts - j) (len ts) ts) sl i [] = inr (ls, (ln, encode l)) ->
    der_write_TL_m
      (Int.repr (Znth (len ts - j - 1) ts)) (Int.repr l) 0 0%int ls = inl e ->
    der_write_tags_loop1 ts sl i [] = inl e.
Proof.
  intros until i.
  intros J L TL.
  replace ts with
      ((sublist 0 (len ts - j - 1) ts 
                ++  (sublist (len ts - j - 1) (len ts) ts))).
  eapply loop1_app.
  replace (sublist (len ts - j - 1) (len ts) ts) with
      ((Znth (len ts - j - 1) ts) :: (sublist (len ts - j) (len ts) ts)). 
  eapply write_TL_to_loop1; try eassumption.
  erewrite Znth_cons_sublist.
  all: autorewrite with sublist;
  auto.
  nia.
Qed.


Lemma write_TL_to_loop1_inr : forall i h tl ls1 l1 ls2 l2 sl lens1,
      der_write_tags_loop1 tl sl i [] = inr (ls1, (lens1, encode l1)) ->
      der_write_TL_m (Int.repr h) (Int.repr l1) 0 0%int ls1 = inr (ls2, encode l2) ->
      der_write_tags_loop1 (h :: tl) sl i [] 
      = inr (ls1 ++ ls2, (l1 :: lens1, (encode (l2 + l1)))).
Proof. 
  intros.
  simpl.
  erewrite H.
  erewrite H0.
  auto.
Qed.

Lemma write_TL_to_loop1_sublist_inr :  
              forall lens1 i j ts ls1 l1 ls2 l2 sl,
    0 <= j < len ts ->
    der_write_tags_loop1
      (sublist (len ts - j) (len ts) ts) sl i [] = inr (ls1, (lens1, encode l1)) ->
    der_write_TL_m
      (Int.repr (Znth (len ts - j - 1) ts))
      (Int.repr l1) 0 0%int ls1 = inr (ls2, encode l2) ->
    der_write_tags_loop1 (sublist (len ts - (j + 1)) 
                                  (len ts) ts) sl i []
    = inr (ls1 ++ ls2, (l1 :: lens1, (encode (l2 + l1)))).
Proof.
  intros until sl.
  intros J L T.
  replace (sublist (len ts - (j + 1)) (len ts) ts) with
      ((Znth (len ts - j - 1) ts) :: (sublist (len ts - j) (len ts) ts)). 
  eapply write_TL_to_loop1_inr; try eassumption.
  erewrite Znth_cons_sublist.
  all: autorewrite with sublist;
  auto.
  replace (len ts - j - 1)  with (len ts - (j + 1)) by nia.
  auto.
  nia.
Qed.

Lemma write_TL_to_loop2_inl_left :  forall e s ht hl tll tlt  i ltf ii,
      der_write_TL_m (Int.repr ht) hl s 
                     (if negb (ltf =? 0) || (i <? len (ht :: tlt) - 1)
                      then 1%int 
                      else 0%int) 
                     ii = inl e ->
      der_write_tags_loop2 (ht :: tlt) (hl :: tll) i s ltf ii = inl e.
Proof.
  intros.
  simpl.
  break_if;
  erewrite H;
  auto.
Qed.

Lemma write_TL_to_loop2_inl_right :  forall e s ht hl tll tlt  i ltf ls v ii,
      der_write_TL_m (Int.repr ht) hl s 
                     (if negb (ltf =? 0) || (i <? len (ht :: tlt) - 1)
                      then 1%int 
                      else 0%int) 
                     ii = inr (ls, v) ->
      der_write_tags_loop2 tlt tll (i - 1) s ltf (ii ++ ls) = inl e ->
      der_write_tags_loop2 (ht :: tlt) (hl :: tll) i s ltf ii = inl e.
Proof.
  intros.
  simpl.
  erewrite H.
  break_match.
  erewrite H0.
  auto.
Qed.


Require Import Core.Tactics.


Lemma TS_inr_not_one : forall t s ls e ,
  Ber_tlv_tag_serialize.tag_serialize t (Int.repr s)
  = (ls, e) ->
  0 <= e <= 6.
Proof.
  intros.
  unfold Ber_tlv_tag_serialize.tag_serialize in H.
  repeat break_if; cbn in H; try congruence.
  inversion H as [A].
  nia.
  inversion H as [A].
  nia.
  all: repeat break_if;
    inversion H as [A];
    nia.
Qed.

Lemma TS_inr_not_int_one : forall t s ls e,
  Ber_tlv_tag_serialize.tag_serialize t (Int.repr s)
  = (ls, e) ->
  Int.repr (e) <> Int.repr (-1).
Proof.
  intros.
  unfold Ber_tlv_tag_serialize.tag_serialize in H.
  repeat break_if; cbn in H; try congruence.
  inversion H as [A].
  discriminate.
  repeat break_if;
    inversion H as [A];
    discriminate.
   all: repeat break_if;
    inversion H as [A];
    try discriminate.
Qed.

Lemma LS_inr_not_int_one : forall t s ls e,
  Ber_tlv_length_serialize.length_serialize t (Int.repr s)
  = (ls, e) ->
  Int.repr (e) <> Int.repr (-1).
Proof.
  intros.
  unfold Ber_tlv_length_serialize.length_serialize  in H.
  repeat break_if; cbn in H; try congruence; 
  repeat break_if; try inversion H as [A];
  discriminate.
Qed.

Lemma LS_inr_not_one : forall t s ls e,
  Ber_tlv_length_serialize.length_serialize t (Int.repr s)
  = (ls, e) ->
  0 <= e <= 5.
Proof.
  intros.
  unfold Ber_tlv_length_serialize.length_serialize  in H.
  repeat break_if; cbn in H; try congruence; 
  repeat break_if; try inversion H as [A];
  try lia.
Qed.

Lemma DWT_inr_not_one : forall t l s c ls e i,
  der_write_TL_m t l s c i = inr (ls, e) ->
   Int.repr (encoded e) <> Int.repr (-1).
Proof.
  intros.
  unfold der_write_TL_m in H.
  cbn in H.
(*  repeat break_match;
    try congruence;
  subst;
  inversion H;
  subst; clear H;
  inversion Heqs1;
  subst; clear Heqs1;
  inversion Heqs0;
  subst; clear Heqs0;
  inversion Heqs2;
  subst; clear Heqs2;
  simpl in *;
  inversion Heqs4 as [TS];
  eapply TS_inr_not_one in TS;
   inversion Heqs3 as [LS];
  eapply LS_inr_not_one in LS;
  assert (0 <= encoded + encoded0 <= 11) as E by nia;
  assert (-1 <> encoded + encoded0) as EE by nia;
  destruct (eq_dec (Int.repr (encoded + encoded0)) (Int.repr (-1))) as [e | g];
  try inversion e;
  try erewrite Int.Z_mod_modulus_eq in H0;
  try erewrite Zmod_small in H0;
  try nia;
  try rep_omega;
  try eassumption. *)
Admitted.
  
Lemma eval_DWT_opt_to_Z : forall t l s c i,
  (Int.repr
    match
      evalErrW (der_write_TL_m t l s c) i
    with
    | Some {| encoded := v0 |} => v0
    | None => -1
    end == Int.repr (- (1)))%int = true -> 
   (exists e, (der_write_TL_m t l s c) i = inl e).
Proof.
  intros.
  unfold evalErrW in H.
  repeat break_match; try congruence.
  inversion Heqo as [A].
  rewrite A in *. clear A.
  symmetry in H.
  eapply binop_lemmas2.int_eq_true in H.
  eapply DWT_inr_not_one in Heqs0.
  simpl in Heqs0.
  contradiction.
  exists e. auto.
Qed.

Lemma eval_DWT_opt_inr' : forall t l s c i,
    Int.repr (match
            evalErrW (der_write_TL_m t l s c) i
          with
          | Some {| encoded := v0 |} => v0
          | None => -1
          end) <> Int.repr (-1) -> 
    exists v, der_write_TL_m t l s c i = inr v.
Proof.
  intros.
  unfold evalErrW in H.
  repeat break_match; try congruence.
  inversion Heqo as [A].
  rewrite A in *. clear A.
  exists (l0, {| encoded := encoded |}).
  auto.
Qed.

Lemma eval_DWT_opt_inr : forall t l s c i v,
    v =(match
            evalErrW (der_write_TL_m t l s c) i
          with
          | Some {| encoded := v0 |} => v0
          | None => -1
          end) ->
    Int.repr v <> Int.repr (-1) -> 
    exists ls, der_write_TL_m t l s c i = inr (ls, encode v).
Proof.
  intros.
  unfold evalErrW in H.
  repeat break_match; try congruence.
  inversion Heqo as [A].
  rewrite A in *. clear A.
  exists l0.
  inversion H.
  auto.
Qed.

Lemma write_tags_loop1_encoded :  forall tl l ls sl ln i ii,
      der_write_tags_loop1 tl sl i ii = inr (ls, (ln, l)) ->
      sl <= encoded l.
Proof.
  induction tl; intros.
  - simpl in H. inversion H. simpl. lia.
  - cbn in H.
    break_match; try congruence.
    repeat break_let.
    break_if; try congruence.
    break_if.
    discriminate.
    inversion H.
    simpl.
    assert (sl <= Types.encoded {| encoded := encoded |}).
    { eapply IHtl.
      eassumption. }
    eapply TS_inr_not_one in Heqp2.
    eapply LS_inr_not_one in Heqp3.
    simpl in *.
    lia. 
Qed.

Lemma eval_DWT_opt_to_Z_inv : forall td struct_len s c b  size i ls v,
    der_write_tags td struct_len s c b size i
    = inr (ls, encode v) ->
     v <> -1.
Proof.
 intros until v.
 unfold der_write_tags.
 cbn.
 repeat break_match; intro K; try congruence; try inversion K; simpl; try lia.
 eapply write_tags_loop1_encoded in Heqs0.
 lia.
 eapply write_tags_loop1_encoded in Heqs0.
 lia.
Qed.

Lemma eval_DWT_opt_to_Z_inv_int : forall td struct_len s c b  size i ls v,
    Int.min_signed <= v <= Int.max_signed ->
    der_write_tags td struct_len s c b size i
    = inr (ls, encode v) ->
     Int.repr v <> Int.repr (-1).
Proof.
  intros.
  eapply eval_DWT_opt_to_Z_inv in H0.
  unfold not.
  intro K.
  eapply repr_inj_signed in K; rep_omega. 
Qed.

Lemma DWT_bounds : forall td struct_len s c b a size i ls v,
    tags td = [a] ->
    der_write_tags td struct_len s c b size i
    = inr (ls, v) ->
    Int.min_signed <= encoded v <= Int.max_signed.
Proof.
  intros until v.
  unfold der_write_tags.
  cbn.
  repeat break_match; intro K; try congruence; try inversion K; simpl; try lia.
  Zbool_to_Prop. list_solve.
  Zbool_to_Prop. erewrite K in *. autorewrite with sublist in *. list_solve.
  intro P. inversion P.
  generalize Heqs0.
  erewrite K.
  cbn.
  repeat break_let.
  eapply TS_inr_not_one in Heqp3.
  eapply LS_inr_not_one in Heqp4.
  break_if; try congruence.
  break_if; try discriminate.
  intro J. inversion J. clear J.
  simpl. lia. 
  intro J. inversion J. clear J. 
  simpl. 
  generalize Heqs0.
  erewrite K.
  cbn.
  repeat break_let.
  eapply TS_inr_not_one in Heqp3.
  eapply LS_inr_not_one in Heqp4.
  break_if; try congruence.
  break_if; try discriminate.
  intro J. inversion J. clear J.
  simpl. lia.
Qed.

Lemma DWT_bounds_concrete : forall td struct_len s c b a size i ls v,
    tags td = [a] ->
    der_write_tags td struct_len s c b size i
    = inr (ls, v) ->
    0 <= encoded v <= 11.
Proof.
  intros until v.
  unfold der_write_tags.
  cbn.
  repeat break_match; intro K; try congruence; try inversion K; simpl; try lia.
  Zbool_to_Prop. list_solve.
  Zbool_to_Prop. erewrite K in *. autorewrite with sublist in *. list_solve.
  intro P. inversion P.
  generalize Heqs0.
  erewrite K.
  cbn.
  repeat break_let.
  eapply TS_inr_not_one in Heqp3.
  eapply LS_inr_not_one in Heqp4.
  break_if; try congruence.
  break_if; try discriminate.
  intro J. inversion J. clear J.
  simpl. lia. 
  intro J. inversion J. clear J. 
  simpl. 
  generalize Heqs0.
  erewrite K.
  cbn.
  repeat break_let.
  eapply TS_inr_not_one in Heqp3.
  eapply LS_inr_not_one in Heqp4.
  break_if; try congruence.
  break_if; try discriminate.
  intro J. inversion J. clear J.
  simpl. lia.
Qed.

