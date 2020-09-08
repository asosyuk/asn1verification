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

Lemma loop2_app_singleton : 
  forall ts ll e s i ltf t l ls v b ii,
    der_write_tags_loop2 ts ll i s ltf ii = inr (ls, v) ->
    der_write_TL_m (Int.repr t) l s 
                   (if negb (ltf =? 0) || (i <? len (ts ++ [b]) - 1)
                    then 1%int 
                    else 0%int) ls = inl e ->
    der_write_tags_loop2 (ts ++ [b]) (ll ++ [Int.repr b]) i s ltf ii = inl e.
Proof.
Admitted.

Lemma write_TL_to_loop2_sublist : 
  forall ts ll j e s i ltf ii,
    der_write_tags_loop2 (sublist 0 j ts) (sublist 0 j ll) i s ltf ii = inl e ->
    der_write_tags_loop2 ts ll (len ts) s ltf ii = inl e.
Admitted.

Require Import Ber_tlv_tag_serialize_m.
Require Import Ber_tlv_length_serialize_m.

Lemma a : forall t s i i' e, 
    tag_serialize t s i = inl e -> tag_serialize t s i' = inl e.
Proof.
  intros.
  all: unfold tag_serialize in *;
    repeat break_if; cbn in *; try congruence.
Qed.

Lemma b : forall t s i i' e, 
    length_serialize t s i = inl e -> length_serialize t s i' = inl e.
Proof.
  intros.
  all: unfold length_serialize in *;
    repeat break_if; cbn in *; try congruence.
Qed.

Lemma b' : forall t s i i' e, 
    length_serialize t s i = inr e -> exists e, length_serialize t s i' = inr e.
Proof.
  intros.
  eexists.
  unfold length_serialize in *;
    repeat break_if; cbn in *. 
  congruence.
  reflexivity.
Admitted.

Lemma AUX : forall i i' t l s c e, 
    der_write_TL_m t l s c i = inl e -> 
    der_write_TL_m t l s c i' = inl e.
Proof.
  intros.
  cbn in H.
  destruct (tag_serialize t (Int.repr s) i) eqn : L.
  inversion H.
  cbn.
  erewrite a with (i' := i').
  auto.
  subst.
  eassumption.
  cbn.
  cbn in H.
Admitted.

(*Lemma AUX : forall i' i t l s c e , 
    der_write_TL_m t l s c i = inl e -> 
    der_write_TL_m t l s c (i ++ i') = inl e.
Proof.
  induction i'; intros until e; intro T.
  - autorewrite with sublist.
    auto.
  - replace (i ++ a :: i') with ((i ++ [a]) ++ i').
    eapply IHi'.
    cbn.
    repeat break_match; auto; try congruence.
    1-3: admit.
Admitted.  *)

Parameter TL : Z -> option Z.

Fixpoint loop ls :=
  match ls with
  | [] => Some 0
  | h :: tl => let x := TL h in
              let y := loop tl in
              match x, y with
                | Some x, Some y => Some (x + y)
                | _, _ => None
              end
  end.

Lemma loop_app :
  forall ts b v, 
    loop ts = Some v ->
    TL b = None ->
    loop (ts ++ [b]) = None.
Proof.
  induction ts; intros until v; intros Loop TLb; simpl in *.
  - erewrite TLb. auto.
  - generalize Loop.
    break_match; auto.
    break_match; try congruence.
    erewrite IHts; auto.
Qed.

Parameter TL' : Z -> errW1 Z.

Fixpoint loop' ls :=
  match ls with
  | [] => ret 0
  | h :: tl => x <- TL' h ;;
              y <- loop' tl ;;
              ret (x + y)
  end.

(*
Lemma loop_app' :
  forall ts ls b i v e, 
    loop' ts i = inr (ls, v) ->
    TL' b [] = inl e ->
    loop' (ts ++ [b]) [] = inl e.
Proof.
  induction ts; intros until e; intros Loop TLb; simpl in *.
  - inversion Loop.
    erewrite TLb.
    auto.
  - generalize Loop.
    break_match; try congruence.
    break_let.
    break_match; try congruence.
    break_let.
    erewrite IHts; auto.
    eassumption.
Qed.  
     eassumption.
Admitted.
    
   
  
Lemma rev_app_cons : forall {A} (a : A) ls, rev (a :: ls) = rev ls ++ [a].
  Proof.
    intros.
    replace [a0] with (rev [a0]) by reflexivity.
    erewrite <- rev_app_distr.
    reflexivity.
Qed.
 *)

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
(*
Lemma loop2_app_singleton' : 
  forall ts e s i ltf t l ls v ii,
    der_write_tags_loop2' ts i s ltf ii = inr (ls, v) ->
    der_write_TL_m (Int.repr t) (Int.repr l) s 
                   (if negb (ltf =? 0) || (i <? len (ts ++ [(t, l)]) - 1)
                    then 1%int 
                    else 0%int) ls = inl e ->
    der_write_tags_loop2' (ts ++ [(t,l)]) i s ltf ii = inl e.
Proof.
  induction ts; intros until ii; intros Loop TL.
  - simpl in *.
    inversion Loop.
    erewrite TL.
    auto.
 - simpl in Loop.
   simpl.
   break_let.
   generalize Loop.
   assert ((if negb (ltf =? 0) || (i <? len ((z, z0) :: ts ++ [(t, l)]) - 1) then 1%int else 0%int) =
           (if negb (ltf =? 0) || (i <? len ((z, z0) :: ts) - 1) then 1%int else 0%int)) as P.
   admit.
   rewrite P.
   break_match.
   congruence.
   intro.
   break_let.
   break_match.
   erewrite IHts.
   auto.
   erewrite <- Loop0.
   break_match.
   auto.
   break_let.
   break_match.
   admit.
   admit.
Admitted.
     
Lemma write_TL_to_loop2_sublist_j' : 
  forall ts j e s i ltf ii,
    der_write_tags_loop2' (sublist j (len ts) ts) i s ltf ii = inl e ->
    exists e, der_write_tags_loop2' ts i s ltf ii = inl e.
Proof.
Admitted.            
    
Lemma write_TL_to_loop2_sublist' : 
  forall ts j e s i ltf ii,
    der_write_tags_loop2' (sublist 0 j ts) i s ltf ii = inl e ->
    der_write_tags_loop2' ts i s ltf ii = inl e.
Proof.
  induction ts; intros until ii; intro D.
  - admit.
  - simpl.
    break_let.
     assert ((if negb (ltf =? 0) || (i <? len ((z, z0) :: ts) - 1) then 1%int else 0%int)
              = 
              (if negb (ltf =? 0) || (i <? len ((z, z0) :: sublist 0 (j - 1) ts) - 1)
               then 1%int
               else 0%int)) as B.
    admit.
    assert (sublist 0 j ((z, z0) :: ts)  = (z, z0) :: sublist 0 (j - 1) ts) as F.
      admit.
      setoid_rewrite F in D.
      simpl in D.
    break_match.
    * 
    rewrite <- B in D.
    break_if;
      erewrite Heqs0 in D;
      inversion D;
      auto.
    * break_let.
      break_match.
      rewrite <- B in D.
      erewrite IHts.
      auto.
       break_if.
      erewrite Heqs0 in D.
      clear B.
      break_match.
      inversion D.
      erewrite H0 in *.
      eassumption.
      break_let.
      break_match.
      congruence.

      erewrite Heqs0 in D.
      clear B.
      break_match.
      inversion D.
      erewrite H0 in *.
      eassumption.
      break_let.
      break_match.
      congruence.
Admitted.
      
    

Lemma write_TL_to_loop2_inl : 
  forall tl1 tl2 e s i ltf ls v ii,
    i < len (tl1 ++ tl2) ->
    der_write_tags_loop2' tl1 i s ltf ii = inr (ls, v) ->
    der_write_tags_loop2' tl2 (i - len tl1) s ltf ls = inl e ->
    der_write_tags_loop2' (tl1 ++ tl2) i s ltf ii = inl e.
Proof.
  induction tl1; intros until ii; intros C TL1 TL2.
  - cbn in *.
    inversion TL1.
    subst.
    replace (i - 0) with i in * by nia.
    auto.
  - simpl.
    break_let.
    break_match.
    + simpl in TL1.
      break_if.
      destruct_orb_hyp.
      erewrite H in *.
      simpl in TL1.
      erewrite Heqs0 in TL1.
      congruence.
      replace (i <? len ((z, z0) :: tl1) - 1)  with true in *.
      simpl in TL1.
      replace (negb (ltf =? 0) || true) with true in *.
      erewrite Heqs0 in TL1.
      congruence.
      admit.
      admit.
      admit.
    + break_let.
      break_match.
      erewrite IHtl1.
      auto.
      autorewrite with sublist in *.
      nia.
      simpl in TL1.
      assert (negb (ltf =? 0) || (i <? len ((z, z0) :: tl1 ++ tl2) - 1) =
              negb (ltf =? 0) || (i <? len ((z, z0) :: tl1) - 1)) as L.
      admit.
      erewrite <- L in TL1.
      erewrite Heqs0 in TL1.
      generalize TL1.
      break_match.
      congruence.
      break_let.
      break_match.
      admit.
      instantiate (1 := ls).
      generalize TL2.
      replace (i - len ((z, z0) :: tl1)) with (i - 1 - len tl1).
      auto.
      autorewrite with sublist.
      nia.
Admitted.
                                                                                       
*)
Require Import Ber_tlv_tag_serialize_m Ber_tlv_length_serialize_m.

Lemma TS_inr_not_one : forall t s ls e i,
  tag_serialize t (Int.repr s) i
  = inr (ls, {| encoded := e |}) ->
  0 <= e <= 6.
Proof.
  intros.
  unfold tag_serialize in H.
  repeat break_if; cbn in H; try congruence.
  inversion H as [A].
  nia.
  inversion H as [A].
  nia.
  all: repeat break_if;
    inversion H as [A];
    nia.
Qed.

Lemma TS_inr_not_int_one : forall t s ls e i,
  tag_serialize t (Int.repr s) i
  = inr (ls, e) ->
  Int.repr (encoded e) <> Int.repr (-1).
Proof.
  intros.
  unfold tag_serialize in H.
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

Lemma LS_inr_not_int_one : forall t s ls e i,
  length_serialize t (Int.repr s) i
  = inr (ls, e) ->
  Int.repr (encoded e) <> Int.repr (-1).
Proof.
  intros.
  unfold length_serialize in H.
  repeat break_if; cbn in H; try congruence.
  inversion H as [A].
  discriminate.
  repeat break_if;
    inversion H as [A];
    discriminate.
Qed.

Lemma LS_inr_not_one : forall t s ls e i,
  length_serialize t (Int.repr s) i
  = inr (ls, {| encoded :=  e |}) ->
  0 <= e <= 5.
Proof.
  intros.
  unfold length_serialize in H.
  repeat break_if; cbn in H; try congruence.
  inversion H as [A].
  nia.
  repeat break_if;
    inversion H as [A];
    nia.
Qed.

Lemma DWT_inr_not_one : forall t l s c ls e i,
  der_write_TL_m t l s c i = inr (ls, e) ->
   Int.repr (encoded e) <> Int.repr (-1).
Proof.
  intros.
  unfold der_write_TL_m in H.
  cbn in H.
  repeat break_match;
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
  try eassumption. 
Qed.
  

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


