(*Require Import VST.floyd.proofauto.*)
Require Import Core Int Notations.

Ltac ints_to_Z :=
  repeat rewrite Int.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac ptrofs_to_Z :=
  repeat rewrite Ptrofs.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac ptrofs_compute_add_mul :=
      simpl; unfold Ptrofs.add; unfold Ptrofs.mul; unfold Ptrofs.of_intu; unfold Ptrofs.of_int;
      repeat rewrite Ptrofs.unsigned_repr_eq;  repeat rewrite Int.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac ints_compute_add_mul :=
      simpl; unfold Int.add; unfold Int.mul;
      repeat rewrite Int.unsigned_repr_eq;  repeat rewrite Int.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac ints64_compute_add_mul :=
      simpl; unfold Int64.add; unfold Int.mul;
      repeat rewrite Int64.unsigned_repr_eq;  repeat rewrite Int64.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac crush_match := repeat break_match;
                    try congruence.


Ltac switch_destruct i :=
  let EQ := fresh "EQ" in
  match goal with
  | [ H : Int.eq i ?X = true |- _ ] => pose proof (Int.eq_spec i X) as EQ; rewrite H in EQ; try (rewrite EQ); clear H
  | [ H : Int64.eq i ?X = true |- _ ] => pose proof (Int64.eq_spec i X) as EQ; rewrite H in EQ; try (rewrite EQ); clear H
  | [ H : Int.eq i ?X = false |- _ ] => pose proof (Int.eq_spec i X) as EQ; rewrite H in EQ; clear H
  | [ H : Int64.eq i ?X = false |- _ ] => pose proof (Int64.eq_spec i X) as EQ; rewrite H in EQ; clear H
  | [ H : i <> Int.repr ?X |- _ ] => pose proof (int_to_unsigned_neq i (Int.repr X) H) as EQ; clear H
  end.

Ltac bool_rewrite :=
  match goal with
  | [ H : ?X = true |- context[?X] ] => rewrite H
  | [ H : ?X = false |- context[?X] ] => rewrite H
  end.

Ltac destruct_orb_hyp :=
 match goal with
 | [H : orb _ _ = true |- _] => apply orb_prop in H; destruct H
 | [H : orb _ _ = false |- _] => apply orb_false_elim in H; destruct H
 end.
 
Ltac destruct_andb_hyp :=
 match goal with
 | [H : andb _ _ = true |- _] => apply andb_prop in H; destruct H
 | [H : andb _ _ = false |- _] => apply andb_false_elim in H; destruct H
 end.

Ltac Zbool_to_Prop :=
  try (rewrite Z.leb_le in * 
        || rewrite Z.leb_gt in * 
        || rewrite Z.eqb_eq in * 
        || rewrite Z.eqb_neq in * 
        || rewrite Z.ltb_ge in * 
        || rewrite Z.ltb_lt in *).

(*Tactic Notation "forward_if" constr(postL) constr(postP) constr(postS) :=
  let l :=
  lazymatch type of postL with
  | localdef =>
      match goal with
      | |- semax _ (PROPx (?P) (LOCALx ?Q ?R)) _ _ =>
          let Q' := remove_LOCAL2 constr:(cons postL nil) Q in
          constr:(cons postL Q')
      end
  | list localdef =>
      match goal with
      | |- semax _ (PROPx (?P) (LOCALx ?Q ?R)) _ _ =>
          let Q' := remove_LOCAL2 postL Q in
          let Q'' := eval cbv iota zeta beta delta [app] in (postL ++ Q') in Q''
      end
  | _ => fail "First arg must be localdef or list localdef" 
  end in 
  let p :=
  lazymatch type of postP with
  | Prop =>
      match goal with
      | |- semax _ (PROPx (?P) ?Q) _ _ =>
          constr:(cons postP P)
      end
  | list Prop =>
      match goal with
      | |- semax _ (PROPx (?P) ?Q) _ _ =>
          let P' := eval cbv iota zeta beta delta [app] in (postP ++ P) in P'
      end
  | _ => fail "Second arg must be Prop or list Prop"
  end in
  lazymatch type of postS with
  | mpred =>
      match goal with
      | |- semax _ (PROPx (?P) (LOCALx ?Q) SEPx (?R)) _ _ =>
          (*let R' := modify_sep [postS] R in*)
          forward_if_tac ((PROPx p) (LOCALx l) (SEPx R))
      end
  | list mpred =>
      match goal with
      | |- semax _ (PROPx (?P) (LOCALx ?Q) SEPx (?R)) _ _ =>
          (*let R' := modify_sep postS R in*)
          forward_if_tac ((PROPx p) (LOCALx l) (SEPx R))
      end
  | _ => fail "Third arg must be mpred or list mpred" 
  end.*)
