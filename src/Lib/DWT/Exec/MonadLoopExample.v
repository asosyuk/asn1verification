Require Import ZArith Psatz List.
Import ListNotations.
Require Import ExtLib.Structures.Monad ErrorWithWriter ExtLib.Data.List.
Import MonadNotation.
Require Import StructTact.StructTactics.


(* errW1 monad *)

Inductive Err :=
  HeaderEncodeError | CBEncodeError | CustomError {T : Type} : T -> Err.

Definition errW1 := @errW Err (list Z).

Existing Class Monoid.
Existing Instance Monoid_list_app.


Open Scope Z.

Parameter f : Z -> option Z.

Fixpoint loop ls :=
  match ls with
  | [] => Some 0
  | h :: tl => let x := f h in
              let y := loop tl in
              match x, y with
                | Some x, Some y => Some (x + y)
                | _, _ => None
              end
  end.

Lemma loop_app :
  forall ts b v, 
    loop ts = Some v ->
    f b = None ->
    loop (ts ++ [b]) = None.
Proof.
  induction ts; intros until v; intros Loop TLb; simpl in *.
  - erewrite TLb. auto.
  - generalize Loop.
    break_match; auto.
    break_match; try congruence.
    erewrite IHts; auto.
Qed.

Parameter fW : Z -> errW1 Z.

Fixpoint loopW ls :=
  match ls with
  | [] => ret 0
  | h :: tl => x <- fW h ;;
              y <- loopW tl ;;
              ret (x + y)
  end.

Lemma AUX :
  forall (T : Type) (E : errW1 T) (e : Err) (,
   forall t l e, fW b t = inl e -> fW b t ++ l = inl e.
Proof.

Admitted.


Lemma loopW_app :
  forall ts ls b js v e, 
    loopW ts js = inr (ls, v) ->
    fW b ls = inl e ->
    loopW (ts ++ [b]) js = inl e.
Proof.
  intros.
  assert (exists t, ts = [t]) by admit.
  destruct H1 as [t H1]; subst ts.
  cbn in *.
  break_match; try discriminate.
  break_let; subst.
  invc H.
  repeat break_match; invc Heqs0.
  admit.

Lemma loopW_app :
  forall ts ls b v e, 
    loopW ts [1] = inr (ls, v) ->
    fW b ls = inl e ->
    loopW (ts ++ [b]) [1] = inl e.
Proof.
  induction ts; intros until e; intros Loop TLb; simpl in *.
  - inversion Loop. subst. erewrite TLb. auto.
  - generalize Loop.
    break_match; try congruence.
    break_let.
    break_match; try congruence.
    break_let.
    intro.
    erewrite IHts; auto.
    eassumption.
    eapply AUX.
    exists ls.
    eassumption.

Lemma loopW_app :
  forall ts ls b i v e, 
    loopW ts i = inr (ls, v) ->
    fW b ls = inl e ->
    loopW (ts ++ [b]) i = inl e.
Proof.
   induction ts; intros until e; intros Loop TLb; simpl in *.
  - inversion Loop. erewrite TLb. auto.
  - generalize Loop.
    break_match; try congruence.
    break_let.
    break_match; try congruence.
    break_let.
    intro.
    erewrite IHts; auto.
    eassumption.
    eapply AUX.
    exists ls.
    eassumption.
Qed.
