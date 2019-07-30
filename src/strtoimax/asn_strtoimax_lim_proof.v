From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import IntNotations asn_strtoimax_lim IntLemmas Tactics asn_strtoimax_lim_spec.
Local Open Scope Int64Scope.

(* Lemmas for each `asn_strtox_result_e` case *)
(* Case ASN_STRTOX_ERROR_INVAL: str >= *end *)

Lemma asn_strtoimax_lim_correct : forall le str fin intp m' res val ip,  
    le!_str = Some (vptr str)  ->
    le!_end = Some (vptr fin) ->
    le!_intp = Some (vptr intp)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    asn_strtoimax_lim str fin intp
    = Some {| return_type := res ;
              value := val ;
              intp := ip ;
              memory := Some m' ; 
           |} -> 
    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim.(fn_body) t le' m'
                       (Out_return (Some ((Vint (asn_strtox_result_e_to_int res)), tint))).
Admitted.

Lemma asn_strtoimax_lim_loop_correct : forall dist b ofs le str fin intp inp_value m' sign,
    
    le!_str = Some (vptr str)  ->
    le!_end = Some (vptr fin) ->
    le!_intp = Some (vptr intp)  ->
    le!_value = Some (Vlong inp_value) ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    load_addr Mptr m fin = Some (Vptr b ofs) ->

    (distance str (b,ofs)) = dist ->

    asn_strtoimax_lim_loop str fin intp inp_value sign (max_sign sign) dist m
          = Some (ASN_STRTOX_ERROR_RANGE, None, Some m') ->

    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m' (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_RANGE), tint))).

Proof.

Lemma asn_strtoimax_lim_ASN_STRTOX_ERROR_INVAL_correct : forall le str fin intp,
    
    asn_strtoimax_lim str fin intp = Some (ASN_STRTOX_ERROR_INVAL, None, None) ->
    
     exists t le', le!_str = Some (vptr str)  ->
              le!_end = Some (vptr fin) ->
              
             exec_stmt ge e le m f_asn_strtoimax_lim.(fn_body) t le' m (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_INVAL), tint))).
Proof.
  intros.
  unfold asn_strtoimax_lim in H.
   assert (forall dist str fin value s last_digit, asn_strtoimax_lim_loop str fin intp value s last_digit dist m <> Some (ASN_STRTOX_ERROR_INVAL, None, None)) as Loop.
    { induction dist.
      intros.
      simpl.
       break_match.
       congruence.
       congruence.
      intros.
      simpl.
      repeat break_match.
      repeat break_if.
      all: try congruence. } 
  repeat break_match.
  all: try congruence.
  unfold addr_ge in Heqo0.
  destruct b0.
  unfold vptr in *.
  repeat break_let.
   replace (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_INVAL) with  (Int.repr (-2)) by (cbv; auto).
  repeat eexists.
  intros Str Fin.
  exec_until_seq.
  econstructor.
  exec_until_seq.
  econstructor.
  exec_until_seq.
  eapply  exec_Sseq_2.
  repeat econstructor.
  repeat rewrite PTree.gso.
  apply Fin.
  1-3: cbv; congruence.
  unfold load_addr in *.
  apply Heqo.
  repeat rewrite PTree.gso.
  apply Str.
  1-4: try (cbv;congruence).
  apply PTree.gss.
  assert (option_map Val.of_bool
    (if Archi.ptr64
     then Val.cmplu_bool (Mem.valid_pointer m) Cge (Vptr b0 i0) (Vptr b i)
     else Val.cmpu_bool (Mem.valid_pointer m) Cge (Vptr b0 i0) (Vptr b i)) = (option_map Val.of_bool (Some true))).
  f_equal.
  unfold ptr_ge in Heqo0.
  assumption.
    eapply H0.
    econstructor.
    repeat econstructor.
    all: congruence.
Qed.

(* Useful lemmas about the spec *)

Lemma strtoimax_loop_inv : forall n str fin intp outp m' value,
    asn_strtoimax_lim_loop str fin intp value Signed last_digit_max_minus (S n) m =
    Some (ASN_STRTOX_OK, outp, m') ->
    exists i, asn_strtoimax_lim_loop (str ++) fin intp (value * Int64.repr 10 + int_to_int64 (i - zero_char)%int) Signed last_digit_max_minus n m =
    Some (ASN_STRTOX_OK, outp, m').
Proof.
  intros.
  simpl in H.
  break_if.
  all: repeat break_match; try congruence; exists i; assumption.
Qed.

Proposition ptr_ge_true : forall  b1 b2 i1 i2, ptr_ge b1 b2 i1 i2 = Some true -> sem_cmp Cge (Vptr b1 i1) (tptr tschar) (Vptr b2 i2) (tptr tschar) m = Some Vtrue.
Proof.
  intros.
  assert ((option_map Val.of_bool (if Archi.ptr64
          then
           Val.cmplu_bool (Mem.valid_pointer m) Cge 
             (Vptr b1 i1) (Vptr b2 i1)
          else
           Val.cmpu_bool (Mem.valid_pointer m) Cge 
                         (Vptr b1 i1) (Vptr b2 i2))) = (option_map Val.of_bool (Some true))).
    f_equal.
    assumption.
    replace (option_map Val.of_bool (Some true)) with (Some Vtrue) in H0 by (simpl; auto).
    eapply H0.
Qed.

Proposition ptr_ge_false : forall  b1 b2 i1 i2, ptr_ge b1 b2 i1 i2 = Some false -> sem_cmp Cge (Vptr b1 i1) (tptr tschar) (Vptr b2 i2) (tptr tschar) m = Some Vfalse.
Proof.
  intros.
  assert ((option_map Val.of_bool (if Archi.ptr64
          then
           Val.cmplu_bool (Mem.valid_pointer m) Cge 
             (Vptr b1 i1) (Vptr b2 i1)
          else
           Val.cmpu_bool (Mem.valid_pointer m) Cge 
                         (Vptr b1 i1) (Vptr b2 i2))) = (option_map Val.of_bool (Some false))).
    f_equal.
    assumption.
    replace (option_map Val.of_bool (Some false)) with (Some Vfalse) in H0 by (simpl; auto).
    eapply H0.
Qed.
  
(* case ASN_STRTOX_EXPECT_MORE: reading + or - and reaching *end *)
Lemma asn_strtoimax_lim_ASN_STRTOX_EXPECT_MORE_correct : forall le str fin intp m',
    
    asn_strtoimax_lim str fin intp = Some (ASN_STRTOX_EXPECT_MORE, None, Some m') ->
    exists t le', le!_str = Some (vptr str)  ->
             le!_end = Some (vptr fin) ->
             le! _last_digit_max = Some (Vlong last_digit_max) -> 
      
             exec_stmt ge e le m f_asn_strtoimax_lim.(fn_body) t le' m' (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_EXPECT_MORE), tint))).
Proof.
  replace (asn_strtox_result_e_to_int ASN_STRTOX_EXPECT_MORE) with (Int.repr (-1)) by (cbv; auto).
  assert (forall dist str fin intp v s last_digit  m',
             asn_strtoimax_lim_loop str fin intp v s last_digit dist m <>  Some (ASN_STRTOX_EXPECT_MORE, None, Some m')) as Loop.
    { induction dist.
      intros.
      simpl.
      break_match.
      congruence.
      congruence.
      intros.
      simpl.
      repeat break_match.
      repeat break_if.
      all: try congruence; eapply IHdist. }
   intros until m'; intros Spec.
   unfold vptr.
   unfold asn_strtoimax_lim in Spec.  
   repeat break_let.
   repeat break_match.
   all: try congruence.
   inversion Spec; clear Spec.
   (* case reading minus *)
   repeat eexists.
   exec_until_seq.
   econstructor.
   repeat econstructor.
   econstructor.
   repeat econstructor.
   econstructor.
   repeat econstructor.
  repeat rewrite PTree.gso.
  eapply H1.
  1-3: cbv; congruence.
  (* dereferencing double pointer *)
  
  apply Heqo.
  repeat rewrite PTree.gso.
  apply H.
  1-4: cbv; congruence.
  apply PTree.gss.
  simpl.
  simpl in Heqo0.
  unfold  addr_ge in *.
  break_let.
  eapply (ptr_ge_false _ _ _ _  Heqo0).
  repeat econstructor.
  repeat econstructor.
  apply exec_Sseq_2.
  repeat econstructor.
  repeat rewrite PTree.gso.
  apply H.
  1-4: cbv; congruence.
  apply Heqo1.
  
  replace  (Out_return (Some (Vint (Int.repr (-1)), tint))) with (outcome_switch  (Out_return (Some (Vint (Int.repr (-1)), tint)))).
  repeat econstructor.
  repeat rewrite PTree.gso.
  eapply H.
  1-5: cbv; congruence.
  simpl in Heqo1.
  simpl.
  apply Heqo1.
  repeat econstructor.
  replace i2 with minus_char.
  econstructor.
  econstructor.
    exec_until_seq.
  (rewrite PTree.gso).
  (rewrite PTree.gso).
  apply PTree.gss.
  1-2: cbv; try congruence.
  1-2: 
    repeat econstructor.
  apply exec_Sseq_2.
  econstructor.
  repeat econstructor.
  repeat (rewrite PTree.gso).
  apply H.
  1-7: cbv; congruence.
  unfold tlong.
  unfold tint.
  simpl.
  econstructor.
  repeat econstructor.
  repeat  (rewrite PTree.gso).
  apply H1.
  1-8: cbv; congruence.
  simpl in Heqo.
  simpl.
  apply Heqo.
  (rewrite PTree.gso).
  apply PTree.gss.
  cbv; congruence.
  apply PTree.gss.
  simpl.
  replace (Ptrofs.repr 1 * Ptrofs.of_ints (Int.repr 1))%ptrofs with (Ptrofs.repr 1) by (auto with ptrofs).
  unfold  addr_ge in *.
  break_let.
  subst.
  pose (ptr_ge_true _ _ _ _ Heqo2).
  simpl in Heqp.
  inversion Heqp; subst.
  eassumption.
  repeat econstructor.
  repeat econstructor.
   repeat  (rewrite PTree.gso).
  apply H1.
  1-9: cbv; congruence.
  (rewrite PTree.gso).
  apply PTree.gss.
  cbv; congruence.
  repeat econstructor.
  simpl.
  replace (Ptrofs.repr 1 * Ptrofs.of_ints (Int.repr 1))%ptrofs with (Ptrofs.repr 1) by (auto with ptrofs).
  apply H0.
  congruence.
  symmetry.
  pose (Int.eq_spec i2 minus_char).
  rewrite Heqb0 in y.
  auto.
  simpl.
  auto.
  congruence.

  pose proof (Loop  (distance (b, i) (b1, i1) - 1)%nat ((b, i) ++) (b0, i0) intp 0 Signed last_digit_max_minus). congruence.
  (* case reading plus *)
   repeat eexists.
   exec_until_seq.
   econstructor.
   repeat econstructor.
   econstructor.
   repeat econstructor.
   econstructor.
   repeat econstructor.
  repeat rewrite PTree.gso.
  eapply H0.
  1-3: cbv; congruence.
  (* dereferencing double pointer *)
  
  apply Heqo.
  repeat rewrite PTree.gso.
  apply H.
  1-4: cbv; congruence.
  apply PTree.gss.
  simpl.
  simpl in Heqo0.
  unfold  addr_ge in *.
  break_let.
  eapply (ptr_ge_false _ _ _ _  Heqo0).
  repeat econstructor.
  repeat econstructor.
  apply exec_Sseq_2.
  repeat econstructor.
  repeat rewrite PTree.gso.
  apply H.
  1-4: cbv; congruence.
  apply Heqo1.
  
  replace  (Out_return (Some (Vint (Int.repr (-1)), tint))) with (outcome_switch  (Out_return (Some (Vint (Int.repr (-1)), tint)))).
  repeat econstructor.
  repeat rewrite PTree.gso.
  eapply H.
  1-5: cbv; congruence.
  simpl in Heqo1.
  simpl.
  apply Heqo1.
  repeat econstructor.
  replace i2 with plus_char.
  constructor.
  eapply exec_Sseq_1.
  repeat econstructor.
   repeat (rewrite PTree.gso).
  apply H.

  1-5: cbv; try congruence.
  repeat econstructor.
  econstructor.
  repeat econstructor.
  repeat (rewrite PTree.gso).
  apply H0.
  1-6: cbv; congruence.
  simpl in Heqo.
  simpl.
  apply Heqo.
  repeat econstructor.
  
  (rewrite PTree.gso).
  apply PTree.gss.
  cbv; congruence.
  apply PTree.gss.
  simpl.
  replace (Ptrofs.repr 1 * Ptrofs.of_ints (Int.repr 1))%ptrofs with (Ptrofs.repr 1) by (auto with ptrofs).
  unfold  addr_ge in *.
  break_let.
  subst.
  pose (ptr_ge_true _ _ _ _ Heqo2).
  simpl in Heqp.
  inversion Heqp; subst.
  eassumption.
  repeat econstructor.
  repeat econstructor.
   repeat  (rewrite PTree.gso).
  apply H0.
  1-7: cbv; congruence.
  (rewrite PTree.gso).
  apply PTree.gss.
  cbv; congruence.
  repeat econstructor.
  simpl.
  replace (Ptrofs.repr 1 * Ptrofs.of_ints (Int.repr 1))%ptrofs with (Ptrofs.repr 1) by (auto with ptrofs).
  inversion Spec.
  auto.
  congruence.
  symmetry.
  pose (Int.eq_spec i2 plus_char).
  rewrite Heqb1 in y.
  auto.
  simpl.
  auto.
  congruence.

  pose (Loop (distance (b, i) (b1, i1) - 1)%nat  ((b, i) ++) (b0, i0) intp 0 Unsigned last_digit_max).  congruence.
  pose (Loop  (distance (b, i) (b1, i1)) (b, i) (b0, i0) intp 0 Unsigned last_digit_max m' ).  congruence.
  Qed.

(* Loop correctness cases *)
(* ASN_STRTOX_OK: conversion successfull *)

(* Dealing with the switch statement *)
Definition switch s1 s2 :=  (Sswitch (Ederef (Etempvar _str (tptr tschar)) tschar)
                      (LScons (Some 48)
                        Sskip
                        (LScons (Some 49)
                          Sskip
                          (LScons (Some 50)
                            Sskip
                            (LScons (Some 51)
                              Sskip
                              (LScons (Some 52)
                                Sskip
                                (LScons (Some 53)
                                  Sskip
                                  (LScons (Some 54)
                                    Sskip
                                    (LScons (Some 55)
                                      Sskip
                                      (LScons (Some 56)
                                        Sskip
                                        (LScons (Some 57)
                                         s1       
                                         
                                          (LScons None
                                            s2
                                            LSnil)))))))))))).

(* If reading i a digit then we enter the correct branch and continue *)
Lemma switch_correct_continue : forall i s1 s2 le b ofs,
    Mem.loadv Mint8signed m (Vptr b ofs) = Some (Vint i) ->
    le ! _str = Some (Vptr b ofs) ->
    is_digit i = true ->
    forall le', (exists t, exec_stmt ge e le m s1 t le' m Out_continue) ->
    (exists t, exec_stmt ge e le m (switch s1 s2) t le' m Out_continue).
Proof.
  intros.
  cbn in H1.
  break_exists.
  repeat destruct_orb_hyp.
  11: congruence.
  all: assert (outcome_switch Out_continue = Out_continue) as Out by (simpl; auto); rewrite <- Out; repeat eexists; try reflexivity; repeat econstructor; try eassumption; try econstructor; (switch_destruct i).
  1-9: eapply exec_Sseq_1; repeat (choose_seq s1); try (exec_Axiom || eassumption || discriminate).
   eapply exec_Sseq_2. try (eassumption || econstructor || discriminate).
   discriminate.
Qed.

Lemma switch_correct_return : forall i s1 s2 le b ofs out,
    Mem.loadv Mint8signed m (Vptr b ofs) = Some (Vint i) ->
    le ! _str = Some (Vptr b ofs) ->
    is_digit i = true ->
    forall le', (exists t, exec_stmt ge e le m s1 t le' m (Out_return out)) ->
    (exists t, exec_stmt ge e le m (switch s1 s2) t le' m (Out_return out)).
Proof.
  intros.
  cbn in H1.
  break_exists.
  repeat destruct_orb_hyp.
  11: congruence.
  all: assert (outcome_switch (Out_return out) = (Out_return out)) as Out by (simpl; auto); rewrite <- Out; repeat eexists; try reflexivity; repeat econstructor; try eassumption; try econstructor; (switch_destruct i).
  1-9: eapply exec_Sseq_1; repeat (choose_seq s1); try (exec_Axiom || eassumption || discriminate).
   eapply exec_Sseq_2. try (eassumption || econstructor || discriminate).
   discriminate.
Qed.

Lemma asn_strtoimax_lim_loop_ASN_STRTOX_OK_correct : forall dist b ofs le str fin intp inp_value out_value out_str m',
     le!_str = Some (vptr str)  ->
     le!_end = Some (vptr fin) ->
     le!_value = Some (Vlong inp_value) ->
     le ! _upper_boundary = Some (Vlong upper_boundary) ->
     le ! _last_digit_max = Some (Vlong last_digit_max) ->
     le ! _sign = Some (Vint (Int.repr 1)) ->
     load_addr Mptr m fin = Some (Vptr b ofs) ->
     (distance str (b,ofs)) = dist ->
    asn_strtoimax_lim_loop str (b,ofs) intp inp_value Unsigned last_digit_max dist m = Some (ASN_STRTOX_OK, Some (out_value,Unsigned, out_str), Some m') ->
    
     exists t le',  exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m Out_normal
                             /\ le'!_value = Some (Vlong out_value).
 Proof.
   induction dist; intros until m'; intros Str End Value UB LastD Sign Load Dist Spec; unfold vptr in *; repeat break_let; subst; simpl in Spec.
   - (* Base case *)
     
     break_match.
     inversion Spec.
     rewrite <- H0.
     repeat eexists.
     eapply exec_Sloop_stop1.
     eapply exec_Sseq_2.
     forward.
      assert (sem_cmp Clt (Vptr b1 i0) (tptr tschar) (Vptr b ofs) (tptr tschar)  asn_strtoimax_lim_spec.m  = Some Vfalse) by admit. (* follows from Dist, may need assumptions about validity of pointers and their comparison *)
     eassumption.
     simpl.
     all: repeat (econstructor || env_assumption || discriminate).      
   - (* I.S. *)
     repeat break_match.
     all: try congruence.
     (* Case (inp_value < upper_boundary) *)
     (* Using Induction Hypothesis *)
     + remember ((_str <~ Vptr b1 (i0 + 1)%ptrofs)
              ((_value <~ Vlong (inp_value * int_to_int64 (Int.repr 10) + int_to_int64 (i1 - zero_char)%int))
              ((_d <~ Vint (i1 - zero_char)%int)
              ((_t'2 <~ Vint i1) ((_t'1 <~ Vint i1) ((_t'3 <~ Vptr b ofs) le)))))) as le''.
     pose proof (IHdist b ofs le'' (b1, (i0 + 1)%ptrofs) (b0, i) intp 
           (inp_value * Int64.repr 10 + int_to_int64 (i1 - zero_char)%int)  out_value out_str 
           m') as IH.
     clear IHdist.
     destruct IH as [t IH]; subst; try (repeat env_assumption || reflexivity).
     admit. (* follows from Dist *)    
     destruct IH as [le' IH]; destruct IH as [IH LE'].
     (* Executing one loop *)
      (* dealing with switch statement: FIX *)
     pose proof (switch_correct_continue i1 switch_body switch_default  (PTree.set _t'1 (Vint i1) (PTree.set _t'3 (Vptr b ofs) le)) b1 i0) as SW.
     replace asn_strtoimax_lim_spec.m  with m in * by admit.
      unfold switch in SW.
      assert (Mem.loadv Mint8signed m (Vptr b1 i0) = Some (Vint i1)) as M by admit.
      assert (((_t'1 <~ Vint i1) ((_t'3 <~ Vptr b ofs) le)) ! _str = Some (Vptr b1 i0)) as L by admit.
     pose proof (SW M L Heqb2  ((_value <~
      Vlong
        (inp_value * cast_int_long Signed (Int.repr 10) +
         cast_int_long Signed (i1 - zero_char)%int))
       ((_d <~ Vint (i1 - zero_char)%int)
          ((_t'2 <~ Vint i1) ((_t'1 <~ Vint i1) ((_t'3 <~ Vptr b ofs) le)))))).
     assert ((exists t : trace,
         exec_stmt ge e ((_t'1 <~ Vint i1) ((_t'3 <~ Vptr b ofs) le)) m switch_body t
           ((_value <~
             Vlong
               (inp_value * cast_int_long Signed (Int.repr 10) +
                cast_int_long Signed (i1 - zero_char)%int))
              ((_d <~ Vint (i1 - zero_char)%int)
                 ((_t'2 <~ Vint i1) ((_t'1 <~ Vint i1) ((_t'3 <~ Vptr b ofs) le)))))
           m Out_continue)) as F.
           {  repeat eexists.
              forward. simpl.
              bool_rewrite. forward.
              replace (negb (1 == 0)%int) with true by (auto with ints).
              forward.
           }
     pose proof (H F).
     destruct H0.
     repeat eexists.
     eapply exec_Sloop_loop.
     instantiate (1 := Out_continue).
     econstructor. (* Wrong local env instantiated  by repeat econstructor ??? *)
     econstructor.
     econstructor.
     forward.
     forward.
     assert (sem_cmp Clt (Vptr b1 i0) (tptr tschar) (Vptr b ofs) (tptr tschar) m = Some Vtrue) by admit. (* follows from Dist *)
     eassumption.
     repeat econstructor.
     replace (negb (1 == 0)%int) with true by (auto with ints).
     econstructor.
     econstructor.
     repeat econstructor; try env_assumption; try eassumption.
     simpl.
     assert (Mem.load Mint8signed m b1 (Ptrofs.unsigned i0) = Some (Vint i1)) by admit. (* follows from Heqo - See Many32 semantics *)
     eassumption.
     econstructor.
     repeat econstructor.
     repeat env_assumption.
     repeat econstructor.
     fold f_asn_strtoimax_lim_loop.
     replace  (i0 + Ptrofs.repr (sizeof ge tschar) * ptrofs_of_int Signed (Int.repr 1))%ptrofs with (i0 + 1)%ptrofs.
     replace (inp_value * cast_int_long Signed (Int.repr 10) +
            cast_int_long Signed (i1 - zero_char)%int) with  (inp_value * int_to_int64 (Int.repr 10) +
                                                              int_to_int64 (i1 - zero_char)%int).
     
     eapply IH.
     simpl.
     unfold int_to_int64.
     admit. (* signed and unsigned ? *)
     auto with ptrofs.
     eassumption.
    
     (* Case  (inp_value == upper_boundary) && (int_to_int64 (i1 - zero_char)%int <= last_digit_max) : same as before *)
     + remember ((_str <~ Vptr b1 (i0 + 1)%ptrofs)
              ((_value <~ Vlong (inp_value * int_to_int64 (Int.repr 10) + int_to_int64 (i1 - zero_char)%int))
              ((_d <~ Vint (i1 - zero_char)%int)
              ((_t'2 <~ Vint i1) ((_t'1 <~ Vint i1) ((_t'3 <~ Vptr b ofs) le)))))) as le''.
     pose proof (IHdist b ofs le'' (b1, (i0 + 1)%ptrofs) (b0, i) intp 
           (inp_value * Int64.repr 10 + int_to_int64 (i1 - zero_char)%int)  out_value out_str 
           m') as IH.
     clear IHdist.
     destruct IH as [t IH]; subst; try (repeat env_assumption || reflexivity).
     admit. (* follows from Dist *)    
     destruct IH as [le' IH]; destruct IH as [IH LE'].
     (* Executing one loop *)
     pose proof (switch_correct_continue i1 switch_body switch_default  (PTree.set _t'1 (Vint i1) (PTree.set _t'3 (Vptr b ofs) le)) b1 i0) as SW.
     replace asn_strtoimax_lim_spec.m  with m in * by admit.
      unfold switch in SW.
      assert (Mem.loadv Mint8signed m (Vptr b1 i0) = Some (Vint i1)) as M by admit.
      assert (((_t'1 <~ Vint i1) ((_t'3 <~ Vptr b ofs) le)) ! _str = Some (Vptr b1 i0)) as L by admit.
     pose proof (SW M L Heqb2  ((_value <~
      Vlong
        (inp_value * cast_int_long Signed (Int.repr 10) +
         cast_int_long Signed (i1 - zero_char)%int))
       ((_d <~ Vint (i1 - zero_char)%int)
          ((_t'2 <~ Vint i1) ((_t'1 <~ Vint i1) ((_t'3 <~ Vptr b ofs) le)))))).
     assert ((exists t : trace,
         exec_stmt ge e ((_t'1 <~ Vint i1) ((_t'3 <~ Vptr b ofs) le)) m switch_body t
           ((_value <~
             Vlong
               (inp_value * cast_int_long Signed (Int.repr 10) +
                cast_int_long Signed (i1 - zero_char)%int))
              ((_d <~ Vint (i1 - zero_char)%int)
                 ((_t'2 <~ Vint i1) ((_t'1 <~ Vint i1) ((_t'3 <~ Vptr b ofs) le)))))
           m Out_continue)) as F.
     {  
       repeat eexists.
       destruct_andb_hyp.
       forward. simpl.
       bool_rewrite. forward.
       replace (negb (1 == 0)%int) with true by (auto with ints).
       forward. simpl.

       bool_rewrite. forward.
       replace (negb (1 == 0)%int) with true by (auto with ints).
       forward. simpl. unfold int_to_int64 in *. rewrite Int.signed_eq_unsigned.
       bool_rewrite; econstructor.
       admit. (* int signed and unsigned *)
       break_ife_true.
       forward.
       auto with ints.
    }
     pose proof (H F).
     destruct H0.
     repeat eexists.
     eapply exec_Sloop_loop.
     instantiate (1 := Out_continue).
     econstructor. (* Wrong local env instantiated  by repeat econstructor ??? *)
     econstructor.
     econstructor.
     repeat econstructor; try env_assumption.
     repeat econstructor; try env_assumption.
     try eassumption.
     econstructor.
     assert (sem_cmp Clt (Vptr b1 i0) (tptr tschar) (Vptr b ofs) (tptr tschar) m = Some Vtrue) by admit. (* follows from Dist *)
     eassumption.
     repeat econstructor.
     replace (negb (1 == 0)%int) with true by (auto with ints).
     econstructor.
     econstructor.
     repeat econstructor; try env_assumption; try eassumption.
     eassumption.
     econstructor.
          repeat econstructor.
    repeat env_assumption.
    simpl.
    econstructor.
     fold f_asn_strtoimax_lim_loop.
     replace  (i0 + Ptrofs.repr (sizeof ge tschar) * ptrofs_of_int Signed (Int.repr 1))%ptrofs with (i0 + 1)%ptrofs.
     replace (inp_value * cast_int_long Signed (Int.repr 10) +
            cast_int_long Signed (i1 - zero_char)%int) with  (inp_value * int_to_int64 (Int.repr 10) +
                                                              int_to_int64 (i1 - zero_char)%int).
     
     eapply IH.
     simpl.
     unfold int_to_int64.
     admit. (* signed and unsigned ? *)
     auto with ptrofs.
     eassumption.
     Admitted.

 (* Case ASN_STRTOX_EXTRA_DATA: go through the loop until a non-digit encountered *)

(* If reading i a digit then we enter the correct branch and continue *)
Lemma switch_default_correct : forall i 
                       s1 s2 le b ofs out,
    Mem.loadv Mint8signed m (Vptr b ofs) = Some (Vint i) ->
    le ! _str = Some (Vptr b ofs) ->
    is_digit i = false ->
    forall le' m', (exists t, exec_stmt ge e le m s2 t le' m' (Out_return out)) ->
                (exists t, exec_stmt ge e le m (switch s1 s2) t le' m' (Out_return out)).
Proof.
  intros until out; intros Mem Str Dig le' m' S2.
  destruct S2 as [t S2].
  repeat eexists.
  replace (Out_return out) with (outcome_switch (Out_return out)) by (reflexivity).
  econstructor.
  repeat econstructor; try eassumption.
  econstructor.
  cbn in Dig.
  repeat destruct_orb_hyp.
  repeat (switch_destruct i).
  try (rewrite Int.unsigned_repr in *).
  unfold select_switch.
  unfold select_switch_default.
  unfold select_switch_case.
  repeat break_if.
  all: try congruence.
  eapply exec_Sseq_2.
  eassumption.
  discriminate.
  all: cbn;  try lia.
       Qed.

   Lemma asn_strtoimax_lim_loop_ASN_STRTOX_EXTRA_DATA_correct : forall dist b ofs le str fin intp inp_value out_value out_str m',          
    le!_str = Some (vptr str)  ->
    le!_end = Some (vptr fin) ->
    le!_intp = Some (vptr intp)  ->
    le!_value = Some (Vlong inp_value) ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    load_addr Mptr m fin = Some (Vptr b ofs) ->

    (distance str (b,ofs)) = dist ->

    asn_strtoimax_lim_loop str fin intp inp_value Unsigned last_digit_max dist m = Some (ASN_STRTOX_EXTRA_DATA, Some (out_value, Unsigned, out_str), Some m') ->

    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m' (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_EXTRA_DATA), tint)))
             /\ le'!_value = Some (Vlong out_value).         
Proof.
  replace (asn_strtox_result_e_to_int ASN_STRTOX_EXTRA_DATA) with Int.one by (reflexivity).
  induction dist; intros until m'; intros Str End Intp Value UB Sign Load Dist Spec;
    unfold vptr in *; repeat break_let;  simpl in Spec.
  - break_match. all: congruence.
  - repeat break_match.
    all: try congruence.
    (* 3 cases *)
    + remember ((_str <~ Vptr b2 (i1 + 1)%ptrofs)
              ((_value <~ Vlong (inp_value * int_to_int64 (Int.repr 10) + int_to_int64 (i2 - zero_char)%int))
              ((_d <~ Vint (i2 - zero_char)%int)
              ((_t'2 <~ Vint i2) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))) as le''.
     pose proof (IHdist b ofs le'' (b2, (i1 + 1)%ptrofs) (b1, i0) intp 
           (inp_value * Int64.repr 10 + int_to_int64 (i2 - zero_char)%int)  out_value out_str 
           m') as IH.
     clear IHdist.
     destruct IH as [t IH]; subst; try (repeat env_assumption || reflexivity).
     admit. (* follows from Dist *)    
     destruct IH as [le' IH]; destruct IH as [IH LE'].
      pose proof (switch_correct_continue i2 switch_body switch_default  (PTree.set _t'1 (Vint i2) (PTree.set _t'3 (Vptr b ofs) le)) b2 i1) as SW.
     replace asn_strtoimax_lim_spec.m  with m in * by admit.
      unfold switch in SW.
      assert (Mem.loadv Mint8signed m (Vptr b2 i1) = Some (Vint i2)) as M by admit.
      assert (((_t'1 <~ Vint i2) ((_t'3 <~ Vptr b ofs) le)) ! _str = Some (Vptr b2 i1)) as L by admit.
      pose proof (SW M L Heqb3  ((_value <~
      Vlong
        (inp_value * cast_int_long Signed (Int.repr 10) +
         cast_int_long Signed (i2 - zero_char)%int))
       ((_d <~ Vint (i2 - zero_char)%int)
          ((_t'2 <~ Vint i2) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))).
     assert ((exists t : trace,
         exec_stmt ge e ((_t'1 <~ Vint i2) ((_t'3 <~ Vptr b ofs) le)) m switch_body t
           ((_value <~
             Vlong
               (inp_value * cast_int_long Signed (Int.repr 10) +
                cast_int_long Signed (i2 - zero_char)%int))
              ((_d <~ Vint (i2 - zero_char)%int)
                 ((_t'2 <~ Vint i2) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))
           m Out_continue)) as F by admit.
     pose proof (H F).
     destruct H0.
     repeat eexists.
     eapply exec_Sloop_loop.
     instantiate (1 := Out_continue).
     econstructor. (* Wrong local env instantiated  by repeat econstructor ??? *)
     econstructor.
     econstructor.
     repeat econstructor; try env_assumption.
     repeat econstructor; try env_assumption.
     try eassumption.
     econstructor.
     assert (sem_cmp Clt (Vptr b2 i1) (tptr tschar) (Vptr b ofs) (tptr tschar) m = Some Vtrue) by admit. (* follows from Dist *)
     eassumption.
     repeat econstructor.
     replace (negb (1 == 0)%int) with true by (auto with ints).
     econstructor.
     econstructor.
     repeat econstructor; try env_assumption; try eassumption.
     simpl.
     assert (Mem.load Mint8signed m b2 (Ptrofs.unsigned i1) = Some (Vint i2)) by admit. (* follows from Heqo - See Many32 semantics *)
     eassumption.
     econstructor.
     repeat econstructor.
     repeat env_assumption.
     repeat econstructor.
     fold f_asn_strtoimax_lim_loop.
     replace  (i0 + Ptrofs.repr (sizeof ge tschar) * ptrofs_of_int Signed (Int.repr 1))%ptrofs with (i0 + 1)%ptrofs.
     replace (inp_value * cast_int_long Signed (Int.repr 10) +
            cast_int_long Signed (i2 - zero_char)%int) with  (inp_value * int_to_int64 (Int.repr 10) +
                                                              int_to_int64 (i2 - zero_char)%int).
     
     eapply IH.
     simpl.
     unfold int_to_int64.
     admit. (* signed and unsigned ? *)
     auto with ptrofs.
     eassumption.
    + admit.
    + inversion Spec; clear Spec.
      unfold  Mem.loadv in *.
      assert (((_t'1 <~ Vint i2) ((_t'3 <~ Vptr b ofs) le)) ! _str = Some (Vptr b2 i1)) as LE by (repeat env_assumption).
      pose proof (switch_default_correct i2 switch_body switch_default  (PTree.set _t'1 (Vint i2) (PTree.set _t'3 (Vptr b ofs) le)) b2 i1  (Some (Vint 1%int, tint)) Heqo0 LE Heqb3 ((_t'1 <~ Vint i2) ((_t'3 <~ Vptr b ofs) le)) m') as SW.
       destruct SW.
      ++ repeat eexists.
         repeat econstructor.
         all: repeat env_assumption.
         repeat econstructor.
         econstructor.
         simpl.         
         replace (Int64.repr (Int.signed (Int.repr 1))) with (Int64.repr 1) by (auto with ints). 
         replace (Int64.repr 1 * inp_value) with (inp_value) by admit.
         rewrite <- H0.
         econstructor.
      ++
        repeat eexists.
        eapply exec_Sloop_stop1.
        econstructor. (* Wrong local env instantiated  by repeat econstructor ??? *)
        econstructor.
        econstructor.
        repeat econstructor; try env_assumption.
        repeat econstructor; try env_assumption.
        try eassumption.
        econstructor.
        simpl.
        assert (sem_cmp Clt (Vptr b2 i1) (tptr tschar) (Vptr b ofs) (tptr tschar) asn_strtoimax_lim_spec.m = Some Vtrue) by admit; eassumption.
        econstructor.
        econstructor.
        econstructor.
        repeat econstructor.
        1-2: env_assumption.
        env_assumption.
        eassumption.
        econstructor.
        repeat env_assumption.
        rewrite <- H0.
        eassumption.
         
Admitted.

Lemma asn_strtoimax_lim_loop_ASN_STRTOX_ERROR_RANGE_correct : forall dist b ofs le str fin intp inp_value  m',
    
    le!_str = Some (vptr str)  ->
    le!_end = Some (vptr fin) ->
    le!_intp = Some (vptr intp)  ->
    le!_value = Some (Vlong inp_value) ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    load_addr Mptr m fin = Some (Vptr b ofs) ->

    (distance str (b,ofs)) = dist ->

    asn_strtoimax_lim_loop str fin intp inp_value Unsigned last_digit_max dist m = Some (ASN_STRTOX_ERROR_RANGE, None, Some m') ->

    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m' (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_RANGE), tint))).         
Proof.
  
replace (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_RANGE) with (Int.repr (-3)) by (reflexivity).
  induction dist; intros until m'; intros Str End Intp Value UB Sign Load Dist Spec;
    unfold vptr in *; repeat break_let;  simpl in Spec.
  - break_match. all: congruence.
  - repeat break_match.
    all: try congruence.
    (* 3 cases *)
     + remember ((_str <~ Vptr b2 (i1 + 1)%ptrofs)
              ((_value <~ Vlong (inp_value * int_to_int64 (Int.repr 10) + int_to_int64 (i2 - zero_char)%int))
              ((_d <~ Vint (i2 - zero_char)%int)
              ((_t'2 <~ Vint i2) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))) as le''.
     pose proof (IHdist b ofs le'' (b2, (i1 + 1)%ptrofs) (b1, i0) intp 
           (inp_value * Int64.repr 10 + int_to_int64 (i2 - zero_char)%int)  
           m') as IH.
     clear IHdist.
     destruct IH as [t IH]; subst; try (repeat env_assumption || reflexivity).
     admit. (* follows from Dist *)    
     destruct IH as [le' IH].
      pose proof (switch_correct_continue i2 switch_body switch_default  (PTree.set _t'1 (Vint i2) (PTree.set _t'3 (Vptr b ofs) le)) b2 i1) as SW.
     replace asn_strtoimax_lim_spec.m  with m in * by admit.
      unfold switch in SW.
      assert (Mem.loadv Mint8signed m (Vptr b2 i1) = Some (Vint i2)) as M by admit.
      assert (((_t'1 <~ Vint i2) ((_t'3 <~ Vptr b ofs) le)) ! _str = Some (Vptr b2 i1)) as L by admit.
      pose proof (SW M L Heqb3  ((_value <~
      Vlong
        (inp_value * cast_int_long Signed (Int.repr 10) +
         cast_int_long Signed (i2 - zero_char)%int))
       ((_d <~ Vint (i2 - zero_char)%int)
          ((_t'2 <~ Vint i2) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))).
     assert ((exists t : trace,
         exec_stmt ge e ((_t'1 <~ Vint i2) ((_t'3 <~ Vptr b ofs) le)) m switch_body t
           ((_value <~
             Vlong
               (inp_value * cast_int_long Signed (Int.repr 10) +
                cast_int_long Signed (i2 - zero_char)%int))
              ((_d <~ Vint (i2 - zero_char)%int)
                 ((_t'2 <~ Vint i2) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))
           m Out_continue)) as F by admit.
     pose proof (H F).
     destruct H0.
     repeat eexists.
     eapply exec_Sloop_loop.
     instantiate (1 := Out_continue).
     econstructor. (* Wrong local env instantiated  by repeat econstructor ??? *)
     econstructor.
     econstructor.
     repeat econstructor; try env_assumption.
     repeat econstructor; try env_assumption.
     try eassumption.
     econstructor.
     assert (sem_cmp Clt (Vptr b2 i1) (tptr tschar) (Vptr b ofs) (tptr tschar) m = Some Vtrue) by admit. (* follows from Dist *)
     eassumption.
     repeat econstructor.
     replace (negb (1 == 0)%int) with true by (auto with ints).
     econstructor.
     econstructor.
     repeat econstructor; try env_assumption; try eassumption.
     simpl.
     assert (Mem.load Mint8signed m b2 (Ptrofs.unsigned i1) = Some (Vint i2)) by admit. (* follows from Heqo - See Many32 semantics *)
     eassumption.
     econstructor.
     repeat econstructor.
     repeat env_assumption.
     repeat econstructor.
     fold f_asn_strtoimax_lim_loop.
     replace  (i0 + Ptrofs.repr (sizeof ge tschar) * ptrofs_of_int Signed (Int.repr 1))%ptrofs with (i0 + 1)%ptrofs.
     replace (inp_value * cast_int_long Signed (Int.repr 10) +
            cast_int_long Signed (i2 - zero_char)%int) with  (inp_value * int_to_int64 (Int.repr 10) +
                                                              int_to_int64 (i2 - zero_char)%int).
     
     eapply IH.
     simpl.
     unfold int_to_int64.
     admit. (* signed and unsigned ? *)
     auto with ptrofs.
    + remember ((_str <~ Vptr b2 (i1 + 1)%ptrofs)
              ((_value <~ Vlong (inp_value * int_to_int64 (Int.repr 10) + int_to_int64 (i2 - zero_char)%int))
              ((_d <~ Vint (i2 - zero_char)%int)
              ((_t'2 <~ Vint i2) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))) as le''.
     pose proof (IHdist b ofs le'' (b2, (i1 + 1)%ptrofs) (b1, i0) intp 
           (inp_value * Int64.repr 10 + int_to_int64 (i2 - zero_char)%int)  
           m') as IH.
     clear IHdist.
     destruct IH as [t IH]; subst; try (repeat env_assumption || reflexivity).
     admit. (* follows from Dist *)    
     destruct IH as [le' IH].
      pose proof (switch_correct_continue i2 switch_body switch_default  (PTree.set _t'1 (Vint i2) (PTree.set _t'3 (Vptr b ofs) le)) b2 i1) as SW.
     replace asn_strtoimax_lim_spec.m  with m in * by admit.
      unfold switch in SW.
      assert (Mem.loadv Mint8signed m (Vptr b2 i1) = Some (Vint i2)) as M by admit.
      assert (((_t'1 <~ Vint i2) ((_t'3 <~ Vptr b ofs) le)) ! _str = Some (Vptr b2 i1)) as L by admit.
      pose proof (SW M L Heqb3  ((_value <~
      Vlong
        (inp_value * cast_int_long Signed (Int.repr 10) +
         cast_int_long Signed (i2 - zero_char)%int))
       ((_d <~ Vint (i2 - zero_char)%int)
          ((_t'2 <~ Vint i2) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))).
     assert ((exists t : trace,
         exec_stmt ge e ((_t'1 <~ Vint i2) ((_t'3 <~ Vptr b ofs) le)) m switch_body t
           ((_value <~
             Vlong
               (inp_value * cast_int_long Signed (Int.repr 10) +
                cast_int_long Signed (i2 - zero_char)%int))
              ((_d <~ Vint (i2 - zero_char)%int)
                 ((_t'2 <~ Vint i2) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))
           m Out_continue)) as F by admit.
     pose proof (H F).
     destruct H0.
     repeat eexists.
     eapply exec_Sloop_loop.
     instantiate (1 := Out_continue).
     econstructor. (* Wrong local env instantiated  by repeat econstructor ??? *)
     econstructor.
     econstructor.
     repeat econstructor; try env_assumption.
     repeat econstructor; try env_assumption.
     try eassumption.
     econstructor.
     assert (sem_cmp Clt (Vptr b2 i1) (tptr tschar) (Vptr b ofs) (tptr tschar) m = Some Vtrue) by admit. (* follows from Dist *)
     eassumption.
     repeat econstructor.
     replace (negb (1 == 0)%int) with true by (auto with ints).
     econstructor.
     econstructor.
     repeat econstructor; try env_assumption; try eassumption.
     simpl.
     assert (Mem.load Mint8signed m b2 (Ptrofs.unsigned i1) = Some (Vint i2)) by admit. (* follows from Heqo - See Many32 semantics *)
     eassumption.
     econstructor.
     repeat econstructor.
     repeat env_assumption.
     repeat econstructor.
     fold f_asn_strtoimax_lim_loop.
     replace  (i0 + Ptrofs.repr (sizeof ge tschar) * ptrofs_of_int Signed (Int.repr 1))%ptrofs with (i0 + 1)%ptrofs.
     replace (inp_value * cast_int_long Signed (Int.repr 10) +
            cast_int_long Signed (i2 - zero_char)%int) with  (inp_value * int_to_int64 (Int.repr 10) +
                                                              int_to_int64 (i2 - zero_char)%int).
     
     eapply IH.
     simpl.
     unfold int_to_int64.
     admit. (* signed and unsigned ? *)
     auto with ptrofs.
    + inversion Spec.
      unfold  Mem.loadv in *.
      assert (((_t'1 <~ Vint i2) ((_t'3 <~ Vptr b ofs) le)) ! _str = Some (Vptr b2 i1)) as LE by (repeat env_assumption).
      assert (Mem.loadv Mint8signed m (Vptr b2 i1) = Some (Vint i2)) as M by admit.
      assert (((_t'1 <~ Vint i2) ((_t'3 <~ Vptr b ofs) le)) ! _str = Some (Vptr b2 i1)) as L by admit.   pose proof (switch_correct_return i2 switch_body switch_default  (PTree.set _t'1 (Vint i2) (PTree.set _t'3 (Vptr b ofs) le)) b2 i1 ((Some (Vint (Int.repr (-3)), tint)))) as SW.
      replace asn_strtoimax_lim_spec.m  with m in * by admit.
     pose proof (SW M L Heqb3  ((_value <~
      Vlong
        (inp_value * cast_int_long Signed (Int.repr 10) +
         cast_int_long Signed (i2 - zero_char)%int))
       ((_d <~ Vint (i2 - zero_char)%int)
          ((_t'2 <~ Vint i2) ((_t'1 <~ Vint i2) ((_t'3 <~ Vptr b ofs) le)))))).
     
       destruct H.
      ++ admit. 
      ++
        repeat eexists.
        eapply exec_Sloop_stop1.
        econstructor. (* Wrong local env instantiated  by repeat econstructor ??? *)
        econstructor.
        econstructor.
        repeat econstructor; try env_assumption.
        repeat econstructor; try env_assumption.
        try eassumption.
        econstructor.
        simpl.
        assert (sem_cmp Clt (Vptr b2 i1) (tptr tschar) (Vptr b ofs) (tptr tschar) m = Some Vtrue) by admit. eassumption.
        econstructor.
        econstructor.
        econstructor.
        repeat econstructor.
        1-2: env_assumption.
        env_assumption.
        subst.
        eassumption.
        econstructor.

Admitted.

Lemma asn_strtoimax_lim_loop_correct : forall dist b ofs le str fin intp inp_value  m',
    
    le!_str = Some (vptr str)  ->
    le!_end = Some (vptr fin) ->
    le!_intp = Some (vptr intp)  ->
    le!_value = Some (Vlong inp_value) ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    load_addr Mptr m fin = Some (Vptr b ofs) ->

    (distance str (b,ofs)) = dist ->

    asn_strtoimax_lim_loop str fin intp inp_value Unsigned last_digit_max dist m = Some (ASN_STRTOX_ERROR_RANGE, None, Some m') ->

    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m' (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_RANGE), tint))).

Proof.


    
