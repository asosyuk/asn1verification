Require Import Core IntLemmas Notations.
Require Import StructTact.StructTactics.

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

Ltac choose_seq s1 :=
  match goal with
  | [ |- exec_stmt _ _ _ _ (Ssequence s1 _)
                  _ _ _ _ ] => eapply exec_Sseq_2 
  | [ |- exec_stmt _ _ _ _ (Ssequence _ _ )
                  _ _ _ _ ] => eapply exec_Sseq_1
  end.

Ltac exec_Axiom :=
  match goal with
  | [ |- context [exec_stmt _ _ _ _ Sskip _ _ _ Out_normal]] => econstructor
  | [ |- context [exec_stmt _ _ _ _ Scontinue _ _ _ Out_continue]] => econstructor
  | [ |- context [exec_stmt _ _ _ _ Sbreak _ _ _ Out_break]] => econstructor
  end.

Ltac exec_loop_continue := 
  repeat match goal with
         | [ |- exec_stmt _ _ _ (Sloop _) _ _ _ _ ] => idtac
         | _ => econstructor ; exec_loop_continue
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

Ltac gso_simpl := rewrite PTree.gso by discriminate.
Ltac gss_simpl := rewrite PTree.gss.

Ltac env_assumption := try (eassumption || gso_simpl || gss_simpl).

Ltac exec_until_seq := 
  repeat  match goal with
          | [ |- exec_stmt _ _ _ _ (Ssequence _ _) _ _ _ _ ] => idtac
          | _ => econstructor ; exec_until_seq
          end.

Ltac forward := repeat (econstructor || env_assumption).

Ltac break_ife_true := match goal with
                       | [ |- exec_stmt _ _ _ _ (if ?X then _ else _ ) _ _ _ _ ] => replace X with true
                       end.

Ltac break_ife_false := match goal with
                        | [ |- exec_stmt _ _ _ _ (if ?X then _ else _ ) _ _ _ _ ] => replace X with false
                        end.


Theorem set_env_eq_ptree_set : forall (A : Type) (te : PTree.t A) a b, 
    (in te set [ a <~ b ]) = (PTree.set a b te).
Proof.
 intros. 
 unfold s.
 simpl.
 reflexivity.
Qed.

Ltac gso := rewrite set_env_eq_ptree_set; rewrite PTree.gso.
Ltac gss := rewrite set_env_eq_ptree_set; rewrite PTree.gss.

Ltac seq1 := eapply exec_Sseq_1.
Ltac seq2 := eapply exec_Sseq_2.
Ltac sset := eapply exec_Sset.
Ltac loop := eapply exec_Sloop_loop.
