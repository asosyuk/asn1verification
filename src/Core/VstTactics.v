Require Import VST.floyd.proofauto.

Ltac forward_empty_loop :=
      match goal with
      | [ _ : _ |- semax _ ?Pre (Ssequence (Sloop Sskip Sbreak) _) _ ] =>
          forward_loop Pre break: Pre; try forward ; try entailer! 
      end. 

Ltac rewrite_if_b := 
  try rewrite if_true in * by (reflexivity || assumption || congruence); 
  try rewrite if_false in * by (reflexivity || assumption || congruence).
