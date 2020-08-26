Require Import  VST.floyd.proofauto
 Core.Core Core.Notations Core.Notations Types.
Require Import ExtLib.Structures.Monad.
Require Import Der_write_TL_m.

Inductive DWT_Error := .

Require Import VST.floyd.sublist.

Fixpoint der_write_tags_loop1 (ts : list Z) (sl : Z) (ls : list Z) :=
  match ts with
    | [] => ret (ls, encode sl)
    | h :: tl => '(l, encode y) <- der_write_tags_loop1 tl sl ls ;;
                '(encode x) <- der_write_TL_m (Int.repr h) (Int.repr y) 0 0%int;;
                ret (y :: l, encode (x + y))
  end.

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
         '(_, ls) <- listen (der_write_tags_loop1 (*(length ts) [] *) ts struct_len []) ;;
          z <- der_write_tags_loop2 ts ls l size last_tag_form ;;
          ret (encode (encoded z - struct_len)).

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


