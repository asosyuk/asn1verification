From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.

Ltac switch_destruct i :=
  match goal with
  | [ H : Int.eq i ?X = true |- _ ] =>  pose proof (Int.eq_spec i X) as EQ; rewrite H in EQ; try (rewrite EQ)
  | [ H : Int64.eq i ?X = true |- _ ] =>  pose proof (Int64.eq_spec i X) as EQ; rewrite H in EQ; try (rewrite EQ)
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

 Ltac gso_simpl := rewrite PTree.gso by discriminate.
 Ltac gss_simpl := rewrite PTree.gss.

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

 Ltac env_assumption := try (eassumption || gso_simpl || gss_simpl).

 Ltac exec_until_seq := 
     repeat  match goal with
            | [ |- exec_stmt _ _ _ _ (Ssequence _ _)  _ _ _ _ ] => idtac
            | _ => econstructor ; exec_until_seq

             end.

