Require Import VST.floyd.proofauto.

Ltac process_cases sign := 
match goal with
| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N (LScons (Some ?X) ?C ?SL)
      with Some _ => _ | None => _ end) _ =>
       let y := constr:(adjust_for_sign sign X) in let y := eval compute in y in 
      rewrite (select_switch_case_signed y); 
           [ | reflexivity | clear; compute; split; congruence];
     let E := fresh "E" in let NE := fresh "NE" in 
     destruct (zeq (Int.unsigned (Int.repr y)) N) as [E|NE];
      [ unfold seq_of_labeled_statement at 1 ;
        apply unsigned_eq_eq in E;
        match sign with
        | Signed => apply repr_inj_signed in E; [ | rep_omega | rep_omega]
        | Unsigned => apply repr_inj_unsigned in E; [ | rep_omega | rep_omega]
        end;
        try match type of E with ?a = _ => is_var a; subst a end;
        repeat apply -> semax_skip_seq
     | process_cases sign
    ]
| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N (LScons None ?C ?SL)
      with Some _ => _ | None => _ end) _ =>
      change (select_switch_case N (LScons None C SL))
       with (select_switch_case N SL);
      process_cases sign
| |- semax _ _ (seq_of_labeled_statement 
     match select_switch_case ?N LSnil
      with Some _ => _ | None => _ end) _ =>
      change (select_switch_case N LSnil)
           with (@None labeled_statements);
      cbv iota;
      unfold seq_of_labeled_statement at 1;
      repeat apply -> semax_skip_seq
end.

Ltac forward_switch' := 
 match goal with
| |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Sswitch ?e _) _ => 
  let sign := constr:(signof e) in let sign := eval hnf in sign in
   let HRE := fresh "H" in let v := fresh "v" in
    evar (v: val);
    do_compute_expr Delta P Q R e v HRE;
    simpl in v;
    let n := fresh "n" in evar (n: int); 
    let H := fresh in assert (H: v=Vint n) by (unfold v,n; reflexivity);
    let A := fresh in 
    match goal with |- ?AA => set (A:=AA) end;
    revert n H; normalize; intros n H; subst A;
    let n' := fresh "n" in pose (n' := Int.unsigned n); 
    let H' := fresh in assert (H': n = Int.repr n');
    [try (symmetry; apply Int.repr_unsigned) 
       | rewrite H,H' in HRE; clear H H';
         subst n' n v; 
         rewrite (Int.repr_unsigned (Int.repr _)) in HRE;
          eapply semax_switch_PQR ; 
           [reflexivity | check_typecheck | exact HRE 
           | clear HRE; unfold select_switch at 1; unfold select_switch_default at 1;
             try match goal with H := @abbreviate statement _ |- _ => clear H end;
             process_cases sign ] 
]

end.

Ltac forward_switch post :=
  check_Delta; check_POSTCONDITION;
  repeat (apply -> seq_assoc; abbreviate_semax);
  repeat apply -> semax_seq_skip;
first [ignore (post: environ->mpred)
      | fail 1 "Invariant (first argument to forward_if) must have type (environ->mpred)"];
     match goal with
     | |- semax _ _ (Ssequence (Sswitch _ _) _) _ => 
       apply semax_seq with post;
       [forward_switch' 
      | abbreviate_semax; 
        simpl_ret_assert (*autorewrite with ret_assert*)]
     | |- semax _ _ (Sswitch _ _) _ =>
       forward_switch'   
end.

Ltac forward_empty_while_break B :=
  match goal with
  | [ _ : _ |- semax _ ?Pre (Ssequence (Sloop _ Sbreak) _) _ ] =>
    forward_loop Pre break: B; try forward ; try entailer! 
  end. 

Ltac replace_sep ls Q p := 
  let rec replace_sep ls Q p :=
      match ls with 
      | [] => constr:([Q])
      | ?h :: ?tl => match h with 
                   | data_at _ _ _ p => constr: (Q :: tl)
                   | _ =>
                     let r := replace_sep tl Q p in
                     constr: (h :: r)
                   end
      end in
  replace_sep ls Q p. 

Ltac forward_if_add_sep Q p
  := match goal with
     | [ _ : _ |- semax _ (@PROPx environ ?ps 
                                 (LOCALx ?lcs 
                                         (@SEPx environ ?ls))) 
                       (Ssequence (Sifthenelse _ _ _) _) _ ] => 
       let ls' := replace_sep ls Q p in
       forward_if (@PROPx environ ps
                          (LOCALx lcs
                                  (@SEPx environ (ls'))))
     | [ _ : _ |- semax _ (@PROPx environ ?ps 
                                 (LOCALx ?lcs 
                                         (@SEPx environ ?ls))) 
                       (Ssequence (Ssequence (Sifthenelse _ _ _) _) _) _ ]  =>
       let ls' := replace_sep ls Q p in
       forward_if (@PROPx environ ps
                          (LOCALx lcs
                                  (@SEPx environ (ls'))))
     end.


Ltac forward_empty_while :=
  match goal with
  | [ _ : _ |- semax _ ?Pre (Sloop _ Sbreak) _ ] =>
    forward_loop Pre; try forward ; try entailer!
  | [ _ : _ |- semax _ ?Pre (Ssequence (Sloop _ Sbreak) _) ?Post ] =>
   forward_loop Pre; try forward ; try entailer!  
  end. 

Ltac add_sep Q p
  := match goal with
     | [ _ : _ |- semax _ (@PROPx environ ?ps 
                                 (LOCALx ?lcs 
                                         (@SEPx environ ?ls))) 
                       ?C ?Post ] =>
       let ls' := replace_sep ls Q p in
       replace (@PROPx environ ps 
                       (LOCALx lcs 
                               (@SEPx environ ls)))
         with
           (@PROPx environ ps
                   (LOCALx lcs
                           (@SEPx environ (ls'))))
     end.
