Require Import VST.floyd.proofauto.

Ltac forward_empty_loop :=
      match goal with
      | [ _ : _ |- semax _ ?Pre (Ssequence (Sloop Sskip Sbreak) _) _ ] =>
          forward_loop Pre break: Pre; try forward ; try entailer! 
      end. 

Ltac strip_repr :=
       autorewrite with norm;
       unfold Int.add; unfold Int.mul; unfold Int.neg;
       unfold Int.sub;
       try erewrite Int.unsigned_one in *;
         try erewrite Int.unsigned_zero in *;
         repeat rewrite Int.unsigned_repr;  
         repeat rewrite Int.signed_repr;     
         try rep_omega; auto. 

Ltac rewrite_if_b := 
  try rewrite if_true in * by (reflexivity || assumption); 
  try rewrite if_false in * by (reflexivity || assumption).
