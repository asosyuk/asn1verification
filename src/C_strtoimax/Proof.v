Require Import StructTact.StructTactics.
Require Import Core.Core Core.Notations Core.IntLemmas Core.PtrLemmas Core.Tactics.
Require Import AST Spec Switch SpecLemmas.

Import ListNotations.

Local Open Scope Int64Scope.

(* Lemmas for each `asn_strtox_result_e` case *)

(* ASN_STRTOX_ERROR_INVAL: str >= *end *)
Lemma asn_strtoimax_lim_ASN_STRTOX_ERROR_INVAL_correct :
  forall m ge e le b str_ofs fin_ofs intp_ofs m' p val,
    
    le ! _str = Some (Vptr b str_ofs)  ->
    le ! _end = Some (Vptr b fin_ofs) ->
    le ! _intp = Some (Vptr b intp_ofs)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    asn_strtoimax_lim m (b, str_ofs) (b, fin_ofs) (b, intp_ofs) =
    Some {| return_type := ASN_STRTOX_ERROR_INVAL;
            value := val;
            str_pointer := p; 
            memory := Some m' |} ->
    
    exists (t : trace) (le' : temp_env),
      exec_stmt ge e le m (fn_body f_asn_strtoimax_lim) t le' m'
                (Out_return (Some (Vint (asn_strtox_result_e_to_int 
                                           ASN_STRTOX_ERROR_INVAL), tint))).
Proof.
  intros until val; intros Str End Intp UB Sign Spec.
  unfold asn_strtoimax_lim in Spec.
  assert (forall dist str fin inp value s last_digit,
             asn_strtoimax_lim_loop m str fin inp value s last_digit dist m
             <> Some {|
                    return_type := ASN_STRTOX_ERROR_INVAL;
                    value := val;
                    str_pointer := p;
                    memory := Some m' |}) as Loop.
    { destruct dist as [dist|]. 
      - induction dist; intros; simpl. 
        + break_match; 
            congruence. 
        + repeat break_match;
          unfold asn_strtoimax_lim_loop in IHdist;
            congruence.
      - discriminate.
    } 
    repeat break_match; unfold store_result in *;
      repeat break_match; try congruence.
  unfold addr_ge in *.
  replace (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_INVAL)
    with (Int.repr (-2))
    by reflexivity.
  repeat eexists.
  exec_until_seq. 
  econstructor.
  repeat econstructor.
  econstructor.
  repeat econstructor.
  gss_simpl; econstructor.
  econstructor.
  econstructor.
  repeat econstructor.
  gso_simpl; gss_simpl; econstructor.
  econstructor.
  eapply exec_Sseq_2.
  Tactics.forward.
  cbn.
  unfold cmp_ptr.
  unfold ptr_ge in Heqo0.
  rewrite Heqo0.
  econstructor.
  econstructor.
  replace (negb (1 == 0)%int) with true by reflexivity.
  inversion_clear Spec.
  eapply exec_Sreturn_some.
  econstructor.
  discriminate.
Qed.


(* SN_STRTOX_EXPECT_MORE: reading + or - and reaching *end *)
(* ASN_STRTOX_EXPECT_MORE: reading + or - and reaching *end *)
Lemma asn_strtoimax_lim_ASN_STRTOX_EXPECT_MORE_correct :

  forall m ge e le b str_ofs fin_ofs intp_ofs m' p val,
    
    le ! _str = Some (Vptr b str_ofs)  ->
    le ! _end = Some (Vptr b fin_ofs) ->
    le ! _intp = Some (Vptr b intp_ofs)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    asn_strtoimax_lim m (b, str_ofs) (b, fin_ofs) (b, intp_ofs) =
    Some
      {|
        return_type := ASN_STRTOX_EXPECT_MORE;
        value := val;
        str_pointer := p;
        memory := Some m' |} ->
    
    exists (t : trace) (le' : temp_env),
      exec_stmt ge e le m (fn_body f_asn_strtoimax_lim) t le' m'
                (Out_return (Some (Vint (asn_strtox_result_e_to_int 
                                           ASN_STRTOX_EXPECT_MORE), tint))).
Proof.
  replace (asn_strtox_result_e_to_int ASN_STRTOX_EXPECT_MORE)
    with (Int.repr (-1)) by reflexivity.
  intros until val; intros Str End Intp UB Sign Spec.
  simpl in Spec.    
  assert (forall dist str fin intp v s last_digit m', 
             asn_strtoimax_lim_loop m str fin intp v s last_digit dist m <>
             Some {| return_type := ASN_STRTOX_EXPECT_MORE;
                     value := val;
                     str_pointer := p; 
                     memory := Some m' |}) as Loop.
    { destruct dist as [dist|].
      - induction dist; intros; simpl. 
        + break_match; congruence. 
        + repeat break_match. 
          repeat break_if. 
          all: try congruence; eapply IHdist.
      - discriminate.
    }
   unfold asn_strtoimax_lim in Spec.  
    repeat break_match;
      unfold store_result in *;
      repeat break_match; try congruence.
   inversion Spec; clear Spec.
  - (* case reading minus or plus *)
    destruct_orb_hyp.
    + repeat eexists.
      exec_until_seq.
      econstructor. (* cannot be simplified by forward, why? *)
      repeat econstructor.
      econstructor.
      repeat econstructor.
      env_assumption.
      econstructor.
      repeat econstructor.
      econstructor.
      repeat econstructor.
      all: repeat env_assumption.
      econstructor.
      econstructor.
      econstructor. (* cannot be simplified by forward, why? *)
      repeat econstructor.
        all: repeat env_assumption.
      econstructor.
      eapply ptr_ge_to_sem_cmp_false; eassumption.
      repeat econstructor.
      repeat econstructor.
      eapply exec_Sseq_2.
      Tactics.forward.
      replace (Out_return (Some (Vint (Int.repr (-1)), tint)))
        with (outcome_switch  (Out_return (Some (Vint (Int.repr (-1)), tint)))).
      Tactics.forward.
      switch_destruct i0.
      econstructor.
      exec_until_seq.
      Tactics.forward.
      eapply exec_Sseq_2.
      Tactics.forward.
      eapply ptr_ge_to_sem_cmp_true; eassumption.
      all: Tactics.forward; try discriminate.
    + repeat eexists.
      exec_until_seq.
      econstructor. (* cannot be simplified by forward, why? *)
      repeat econstructor.
      econstructor.
      repeat econstructor.
      env_assumption.
      econstructor.
      repeat econstructor.
      econstructor.
      repeat econstructor.
      all: repeat env_assumption.
      econstructor.
      econstructor.
      econstructor. (* cannot be simplified by forward, why? *)
      repeat econstructor.
        all: repeat env_assumption.
      econstructor.
      eapply ptr_ge_to_sem_cmp_false; eassumption.
      repeat econstructor.
      repeat econstructor.
      apply exec_Sseq_2.
      Tactics.forward.
      replace  (Out_return (Some (Vint (Int.repr (-1)), tint)))
        with (outcome_switch (Out_return (Some (Vint (Int.repr (-1)), tint)))).
      Tactics.forward.
      switch_destruct i0.
      eapply exec_Sseq_2.
      Tactics.forward.
      eapply ptr_ge_to_sem_cmp_true; eassumption.
      all: Tactics.forward; try discriminate.
  - pose proof (Loop (Some (n - 1)%nat) ((b, str_ofs) ++) 
                     (b, fin_ofs) (b, intp_ofs) 0 (sign i0) 
                     (max_sign (sign i0)) m'). 
    congruence.
  - pose proof (Loop (Some n) ((b, str_ofs)) 
                     (b, fin_ofs) (b, intp_ofs) 0 Unsigned 
                     last_digit_max m').
    congruence.
Qed.

(* Loop correctness cases *)
(* ASN_STRTOX_OK: conversion successfull *)
Lemma asn_strtoimax_lim_loop_ASN_STRTOX_OK_correct :
  forall m ge e dist b ofs le str_ofs fin_ofs intp_ofs strp_ofs inp_value m' val s,
    
   le ! _str = Some (Vptr b str_ofs)  ->
   le ! _end = Some (Vptr b fin_ofs) ->
   le ! _intp = Some (Vptr b intp_ofs) ->
   le ! _value = Some (Vlong inp_value) ->
   le ! _upper_boundary = Some (Vlong upper_boundary) ->
   le ! _sign = Some (Vint (Sign s)) ->

   load_addr Mptr m (b, fin_ofs) = Some (Vptr b ofs) ->

   distance m (b, str_ofs) (b, ofs) = dist ->

   asn_strtoimax_lim_loop m (b, str_ofs) (b, fin_ofs)
                            (b, intp_ofs) inp_value s (max_sign s) dist m =
   Some {| return_type := ASN_STRTOX_OK;
           value := Some val;
           str_pointer := Some (b, strp_ofs);
           memory := Some m' |}  ->

   exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m Out_normal
            /\ le' ! _end = Some (Vptr b fin_ofs)
            /\ le' ! _str = Some (Vptr b strp_ofs)
            /\ le' ! _sign = Some (Vint (Sign s))
            /\ le' ! _intp = Some (Vptr b intp_ofs)
            /\ le' ! _value = Some (Vlong val)
            /\ m' = m.
Admitted.
 
Lemma asn_strtoimax_lim_loop_ASN_STRTOX_ERROR_RANGE_correct :
  forall m ge e dist b ofs le str_ofs fin_ofs
    intp_ofs inp_value m' p val s,
   
   le ! _str = Some (Vptr b str_ofs)  ->
   le ! _end = Some (Vptr b fin_ofs) ->
   le ! _intp = Some (Vptr b intp_ofs) ->
   le ! _value = Some (Vlong inp_value) ->
   le ! _upper_boundary = Some (Vlong upper_boundary) ->
   le ! _sign = Some (Vint (Sign s)) ->

   load_addr Mptr m (b, fin_ofs) = Some (Vptr b ofs) ->

   (distance m (b, str_ofs) (b, ofs)) = dist ->

   asn_strtoimax_lim_loop m (b, str_ofs) (b, fin_ofs)
                            (b, intp_ofs) inp_value s (max_sign s) dist m =
   Some {| return_type := ASN_STRTOX_ERROR_RANGE;
           value := val;
           str_pointer := p;
           memory := Some m' |} ->

   exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m'
              (Out_return (Some (Vint
                (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_RANGE), tint))).
Admitted.

Lemma asn_strtoimax_lim_loop_ASN_STRTOX_EXTRA_DATA_correct :
  forall m ge e dist b ofs le str_ofs fin_ofs
    intp_ofs inp_value m' p val s,
   
   le ! _str = Some (Vptr b str_ofs)  ->
   le ! _end = Some (Vptr b fin_ofs) ->
   le ! _intp = Some (Vptr b intp_ofs) ->
   le ! _value = Some (Vlong inp_value) ->
   le ! _upper_boundary = Some (Vlong upper_boundary) ->
   le ! _sign = Some (Vint (Sign s)) ->
   le ! _last_digit_max = Some (Vlong (max_sign s)) ->

   load_addr Mptr m (b, fin_ofs) = Some (Vptr b ofs) ->

   (distance m (b, str_ofs) (b, ofs)) = dist ->
   
   asn_strtoimax_lim_loop m (b, str_ofs) (b, fin_ofs)
                            (b, intp_ofs) inp_value s (max_sign s) dist m =
   Some {| return_type := ASN_STRTOX_EXTRA_DATA;
           value := val;
           str_pointer := p;
           memory := Some m' |} ->

   exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m' 
              (Out_return (Some (Vint
                (asn_strtox_result_e_to_int ASN_STRTOX_EXTRA_DATA), tint))). 
Proof.
  replace (asn_strtox_result_e_to_int ASN_STRTOX_EXTRA_DATA)
    with Int.one by (reflexivity).
  destruct dist as [dist|]; [| discriminate].
  induction dist; intros until s;
    intros Str End Intp Value UB Sign LastD Load Dist Spec;
    simpl in Spec.
  - all: break_match; congruence.
  - repeat break_match;
    unfold store_result in *;
      repeat break_match; try congruence.
    (* 3 cases: do one loop and then apply IH *)
    + remember 
         (PTree.set _str
       (Vptr b
             (str_ofs + Ptrofs.repr (sizeof ge tschar)
                        * ptrofs_of_int Signed (Int.repr 1))%ptrofs)
       (PTree.set _value
          (Vlong
             (inp_value * cast_int_long Signed (Int.repr 10) +
              cast_int_long Signed (i - Int.repr 48)%int))
          (PTree.set _d (Vint (i - Int.repr 48)%int)
             (PTree.set _t'6 (Vint i)
                (PTree.set _t'2 Vtrue
                   (PTree.set _t'8 (Vint i)
                    (PTree.set _t'7 (Vint i) (PTree.set _t'9 (Vptr b ofs) le))))))))
        as le''.
      pose proof (IHdist b ofs le'' (str_ofs + 1)%ptrofs
                         fin_ofs intp_ofs
                         (digit_to_num Unsigned i inp_value) m' p val s) as IH.
      clear IHdist.
      repeat rewrite set_env_eq_ptree_set in Heqle''.
      destruct IH as [t IH]; subst;
        try (repeat env_assumption || reflexivity).
      {
        apply dist_succ.
        assumption.
        destruct dist; simpl in Spec; break_match;
          inversion Spec; clear H0 Spec.
        apply loaded_is_valid in Heqo0.
        assumption.
      }
      destruct IH as [le' IH]. 
      repeat rewrite set_env_eq_ptree_set in *.
      repeat eexists.
      eapply exec_Sloop_loop.
      instantiate (1 := Out_normal).
      econstructor. (* Wrong local env instantiated  by repeat econstructor ??? *)
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption.
      repeat econstructor; try env_assumption.
      try eassumption.
      econstructor.
      assert (sem_cmp Clt (Vptr b str_ofs) (tptr tschar)
                      (Vptr b ofs) (tptr tschar) m = Some Vtrue).
      { admit. }
      eassumption.
      repeat econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption; try eassumption.
      forward.
      simpl.
      unfold is_digit in Heqb0.
      destruct_andb_hyp.
      apply sem_Cle_Cge.
      apply int_le_sem_Cle.
      assumption.
      forward.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption; try eassumption.
      forward.
      forward.
      simpl.
      unfold is_digit in Heqb0.
      destruct_andb_hyp.
      rewrite H0.
      reflexivity.
      forward.
      simpl.
      rewrite Heqb1.
      econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      forward.
      econstructor.
      forward.
      fold f_asn_strtoimax_lim_loop.
      eapply IH.
    + admit.
    + admit.
    + clear IHdist.
      unfold is_digit, andb in Heqb0.
      break_if; eexists; eexists.
      * (* case when i > 57 *)
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor; eassumption.
        econstructor.
        econstructor.
        eassumption.
        econstructor.
        econstructor.
        econstructor; gso_simpl; eassumption.
        econstructor; gss_simpl; econstructor.
        simpl.
        assert (sem_cmp Clt (Vptr b str_ofs) (tptr tschar)
                        (Vptr b ofs) (tptr tschar) m = Some Vtrue)
          by admit.
        eassumption.
        econstructor.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor; gso_simpl; eassumption.
        econstructor.
        econstructor.
        eassumption.
        forward.
        cbn.
        rewrite Heqb1.
        simpl.
        econstructor.
        forward.
        cbn.
        rewrite Heqb0.
        simpl.
        econstructor.
        forward.
        inv Spec.
        simpl.
        unfold mult_sign, Spec.Sign.
        break_match; [reflexivity | ].
        replace (Int64.repr (Int.signed (Int.repr 1))) with (1)%int64 
          by (auto with ints).
        rewrite Int64.mul_commut.
        rewrite Int64.mul_one.
        reflexivity.
        econstructor.
      * (* i < 48 *)
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor; eassumption.
        econstructor.
        econstructor.
        eassumption.
        econstructor.
        econstructor.
        econstructor; gso_simpl; eassumption.
        econstructor; gss_simpl; econstructor.
        simpl.
        assert (sem_cmp Clt (Vptr b str_ofs) (tptr tschar)
                        (Vptr b ofs) (tptr tschar) m = Some Vtrue)
          by admit.
        eassumption.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor; gso_simpl; eassumption.
        econstructor.
        econstructor.
        eassumption.
        econstructor.
        econstructor.
        econstructor; gss_simpl; econstructor.
        econstructor.
        econstructor.
        simpl.
        rewrite Heqb1.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor; gss_simpl; econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor; gso_simpl; gso_simpl; gso_simpl; eassumption.
        econstructor; gso_simpl; gso_simpl; gso_simpl; eassumption.
        econstructor.
        econstructor.
        econstructor.
        eassumption.
        econstructor.
        econstructor.
        econstructor.
        econstructor; gso_simpl; gso_simpl; gso_simpl; eassumption.
        econstructor.
        econstructor; gso_simpl; gso_simpl; gso_simpl; eassumption.
        econstructor; gso_simpl; gso_simpl; gso_simpl; eassumption.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        inv Spec; cbn.
        unfold Spec.Sign; unfold mult_sign in H2; destruct s.
        eassumption.
        replace (Int64.repr (Int.signed (Int.repr 1))) with (1)%int64 
          by (auto with ints).
        rewrite Int64.mul_commut.
        rewrite Int64.mul_one.
        assumption.
        econstructor.
        econstructor.
        econstructor.
Admitted.

Lemma asn_strtoimax_lim_correct :
  forall m ge e le b str_ofs fin_ofs intp_ofs m' res p val,
    
    le ! _str = Some (Vptr b str_ofs)  ->
    le ! _end = Some (Vptr b fin_ofs) ->
    le ! _intp = Some (Vptr b intp_ofs)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    asn_strtoimax_lim m (b, str_ofs) (b, fin_ofs) (b, intp_ofs)
    = Some {| return_type := res;
              value := val;
              str_pointer := p;
              memory := Some m' |} -> 
    exists t le', exec_stmt ge e le m (fn_body f_asn_strtoimax_lim) t le' m'
                 (Out_return (Some ((Vint (asn_strtox_result_e_to_int res)), tint))).
Proof.
  induction res.
  - (* ASN_STRTOX_ERROR_RANGE *)
    intros until val; intros Str End Intp UB Sign Spec.
    unfold asn_strtoimax_lim in Spec.
    repeat break_match;
      unfold store_result in *;
      repeat break_match; try congruence.
    erewrite dist_pred in *.
    + destruct_orb_hyp.
      1 : (eapply exec_loop_minus).
      12: (eapply exec_loop_plus).
      all: repeat rewrite set_env_eq_ptree_set in *.
      all: repeat  eassumption.
        eapply asn_strtoimax_lim_loop_ASN_STRTOX_ERROR_RANGE_correct;
        repeat (env_assumption || econstructor);
     (switch_destruct i0);
     rewrite EQ in *; simpl in Heqo3.
       instantiate (1 := Signed).
       econstructor.
       simpl.
       inversion Spec; subst.
       eassumption.
       eapply asn_strtoimax_lim_loop_ASN_STRTOX_ERROR_RANGE_correct;
        repeat (env_assumption || econstructor);
     (switch_destruct i0);
     rewrite EQ in *; simpl in Heqo3.
       instantiate (1 := Unsigned).
       econstructor.
       simpl.
       inversion Spec; subst.
       eassumption.
    + eassumption. 
    + eassumption. 
    + destruct_orb_hyp.
      eapply exec_loop_none; try eassumption;
        eapply asn_strtoimax_lim_loop_ASN_STRTOX_ERROR_RANGE_correct;
         repeat rewrite set_env_eq_ptree_set in *;
        repeat (env_assumption || econstructor).                   
      instantiate (1 := Unsigned); simpl.
      inversion Spec.
      all: try (econstructor || eassumption).
      inversion Spec; subst; eassumption.
  - (* ASN_STRTOX_ERROR_INVAL *)
    eapply asn_strtoimax_lim_ASN_STRTOX_ERROR_INVAL_correct.     
  - (* ASN_STRTOX_EXPECT_MORE *)
    eapply asn_strtoimax_lim_ASN_STRTOX_EXPECT_MORE_correct. 
  - (*  ASN_STRTOX_EXTRA_DATA *)
     intros until val; intros Str End Intp UB Sign Spec.
    unfold asn_strtoimax_lim in Spec.
    repeat break_match;
      unfold store_result in *;
      repeat break_match; try congruence.
    erewrite dist_pred in *.
    + destruct_orb_hyp.
      1 : (eapply exec_loop_minus).
      12: (eapply exec_loop_plus).
      all: repeat rewrite set_env_eq_ptree_set in *.
      all: repeat  eassumption.
        eapply asn_strtoimax_lim_loop_ASN_STRTOX_EXTRA_DATA_correct;
        repeat (env_assumption || econstructor);
     (switch_destruct i0);
     rewrite EQ in *; simpl in Heqo3.
       instantiate (1 := Signed).
       econstructor.
       simpl.
       inversion Spec; subst.
       econstructor.
        inversion Spec; subst.
       eassumption.
       eapply asn_strtoimax_lim_loop_ASN_STRTOX_EXTRA_DATA_correct;
        repeat (env_assumption || econstructor);
     (switch_destruct i0);
     rewrite EQ in *; simpl in Heqo3.
       instantiate (1 := Unsigned).
       econstructor.
       simpl.
       inversion Spec; subst.
       econstructor.
        inversion Spec; subst.
       eassumption.
    + eassumption. 
    + eassumption. 
    + destruct_orb_hyp.
      eapply exec_loop_none; try eassumption;
        eapply asn_strtoimax_lim_loop_ASN_STRTOX_EXTRA_DATA_correct;
         repeat rewrite set_env_eq_ptree_set in *;
        repeat (env_assumption || econstructor).                   
      instantiate (1 := Unsigned); simpl.
      inversion Spec.
      all: try (econstructor || eassumption).
      inversion Spec; subst; eassumption.
      
- (* ASN_STRTOX_OK *)
    intros until val; intros Str End Intp UB Sign Spec.
    unfold asn_strtoimax_lim in Spec;
      repeat break_match;
      unfold store_result in *;
      repeat break_match; try congruence; inversion Spec; subst.
    + destruct_orb_hyp.
      * (* minus case *)
        destruct a0.
        switch_destruct i0.
        rewrite EQ in *.
        edestruct asn_strtoimax_lim_loop_ASN_STRTOX_OK_correct with
            (le :=  (PTree.set _value (Vlong (cast_int_long Signed (Int.repr 0)))
       (PTree.set _t'11 (Vptr b i)
          (PTree.set _str
             (Vptr str_b
                (str_ofs + 1)%ptrofs)
             (PTree.set _sign (Vint (Int.neg (Int.repr 1)))
                (PTree.set _last_digit_max
                   (Vlong last_digit_max_minus)
                   (PTree.set _t'10 (Vint minus_char)
                      (PTree.set _t'12 (Vptr b i)
                         (PTree.set _last_digit_max
                            (Vlong last_digit_max)
                            (PTree.set _upper_boundary
                               (Vlong
                                  ((Int64.not (cast_int_long Signed (Int.repr 0)) >>
                                    Int64.repr (Int.unsigned (Int.repr 1))) //
                                   cast_int_long Signed (Int.repr 10)))
                               (PTree.set _asn1_intmax_max
                                  (Vlong
                                     (Int64.not (cast_int_long Signed (Int.repr 0)) >>
                                      Int64.repr (Int.unsigned (Int.repr 1))))
                                  (PTree.set _sign (Vint (Int.repr 1)) le))))))))))));
          repeat env_assumption; try econstructor.
        erewrite dist_pred; auto.
        eassumption.
        eassumption.
        destruct H.
        break_and.
        repeat eexists.
        econstructor.
        repeat econstructor.
        econstructor.
        repeat econstructor.
        econstructor.
        repeat econstructor.
        repeat (eassumption || env_assumption).
        repeat econstructor.
        econstructor.
        econstructor.
        repeat econstructor.
        repeat env_assumption.
        econstructor.
        repeat econstructor.
        econstructor.
        repeat econstructor.
        repeat env_assumption.
        repeat env_assumption.
        repeat env_assumption.
        repeat env_assumption.
        repeat env_assumption.
        econstructor.
        unfold load_addr in *.
        unfold addr_ge in *.
        eapply ptr_ge_to_sem_cmp_false.
        eassumption.
        Tactics.forward.
        econstructor.
        econstructor.
        repeat econstructor.
        repeat env_assumption.
        eassumption.
        replace Out_normal with (outcome_switch Out_normal).
        econstructor.
        repeat econstructor.
        repeat env_assumption.
        eassumption.
        econstructor.
        econstructor.
        repeat econstructor.
        repeat env_assumption.
        econstructor.
        repeat econstructor.
        Tactics.forward.
        simpl.
        eapply ptr_ge_to_sem_cmp_false.
        eassumption.
        Tactics.forward.
        econstructor.
        reflexivity.
        eapply exec_Sseq_1.
        econstructor.
        repeat econstructor.
        break_and.
        eassumption.
        repeat eexists.
        forward.
        subst.
        eassumption.
      * (* plus case *)
        destruct a0.
        switch_destruct i0.
        rewrite EQ in *.
        edestruct asn_strtoimax_lim_loop_ASN_STRTOX_OK_correct with
            (le :=  (PTree.set _value (Vlong (cast_int_long Signed (Int.repr 0)))
       (PTree.set _t'11 (Vptr b i)
          (PTree.set _str
             (Vptr str_b
                (str_ofs +
                 Ptrofs.repr (sizeof ge tschar) * ptrofs_of_int Signed (Int.repr 1))%ptrofs)
             (PTree.set _t'10 (Vint plus_char)
                (PTree.set _t'12 (Vptr b i)
                   (PTree.set _last_digit_max
                      (Vlong last_digit_max)
                      (PTree.set _upper_boundary
                         (Vlong
                            ((Int64.not (cast_int_long Signed (Int.repr 0)) >>
                              Int64.repr (Int.unsigned (Int.repr 1))) //
                             cast_int_long Signed (Int.repr 10)))
                         (PTree.set _asn1_intmax_max
                            (Vlong
                               (Int64.not (cast_int_long Signed (Int.repr 0)) >>
                                Int64.repr (Int.unsigned (Int.repr 1))))
                            (PTree.set _sign (Vint (Int.repr 1)) le)))))))))) ;
          repeat env_assumption; try econstructor.
        erewrite dist_pred; auto.
        eassumption.
        eassumption.
        destruct H.
        break_and.
        repeat eexists.
        econstructor.
        repeat econstructor.
        econstructor.
        repeat econstructor.
        econstructor.
        repeat econstructor.
        repeat (eassumption || env_assumption).
        repeat econstructor.
        econstructor.
        econstructor.
        repeat econstructor.
        repeat env_assumption.
        econstructor.
        repeat econstructor.
        econstructor.
        repeat econstructor.
        repeat env_assumption.
        repeat env_assumption.
        repeat env_assumption.
        repeat env_assumption.
        repeat env_assumption.
        econstructor.
        unfold load_addr in *.
        unfold addr_ge in *.
        eapply ptr_ge_to_sem_cmp_false.
        eassumption.
        Tactics.forward.
        econstructor.
        econstructor.
        repeat econstructor.
        repeat env_assumption.
        eassumption.
        replace Out_normal with (outcome_switch Out_normal).
        econstructor.
        repeat econstructor.
        repeat env_assumption.
        eassumption.
        econstructor.
        econstructor.
        repeat econstructor.
        repeat env_assumption.
        econstructor.
        repeat env_assumption.
        eassumption.
        repeat env_assumption.
        econstructor.
        repeat env_assumption.
        econstructor.
        simpl.
        eapply ptr_ge_to_sem_cmp_false.
          eassumption.
        Tactics.forward.
        econstructor.
        econstructor.
        reflexivity.
        eapply exec_Sseq_1.
        econstructor.
        repeat econstructor.
        break_and.
        eassumption.
        repeat eexists.
        forward.
        subst.
        eassumption.
        simpl.
        replace (sign plus_char) with Unsigned.
        simpl.
        replace (Int64.repr (Int.signed (Int.repr 1)))
          with (Int64.repr 1) by auto with ints.
        replace  (Int64.repr 1 * i1) with i1.
        eassumption.
        symmetry.
        rewrite Int64.mul_commut.
        eapply Int64.mul_one.
        reflexivity.
    + pose proof (OK_None_contradiction_1
           (distance (str_b, str_ofs) (b, i) - 1)
           ((str_b, str_ofs) ++) (fin_b, fin_ofs)
           (intp_b, intp_ofs) 0
           (sign i0) (max_sign (sign i0))
           m m' (Some i1)).
      congruence. 
    + pose proof (OK_None_contradiction_2
           (distance (str_b, str_ofs) (b, i) - 1)
           ((str_b, str_ofs) ++) (fin_b, fin_ofs)
           (intp_b, intp_ofs) 0
           (sign i0) (max_sign (sign i0))
           m m').
      congruence. 
    + destruct_orb_hyp.
      destruct a0.
      edestruct asn_strtoimax_lim_loop_ASN_STRTOX_OK_correct with
       (le := (PTree.set _value (Vlong (cast_int_long Signed (Int.repr 0)))
         (PTree.set _t'10 (Vint i0)
            (PTree.set _t'12 (Vptr b i)
               (PTree.set _last_digit_max (Vlong last_digit_max)
                  (PTree.set _upper_boundary
                     (Vlong ((Int64.not (cast_int_long Signed (Int.repr 0)) >>
                          Int64.repr (Int.unsigned (Int.repr 1))) //
                         cast_int_long Signed (Int.repr 10)))
                     (PTree.set _asn1_intmax_max
                        (Vlong
                           (Int64.not (cast_int_long Signed (Int.repr 0)) >>
                            Int64.repr (Int.unsigned (Int.repr 1))))
                        (PTree.set _sign (Vint (Int.repr 1)) le)))))))) ;
        repeat (env_assumption).
      econstructor.
      econstructor.
      instantiate (1 := Unsigned);
        simpl.
      econstructor.
      econstructor.
      eassumption.
      break_exists.
      break_and.
      eapply exec_loop_none_out_normal;
        try eassumption.
      eexists.
      eassumption.
      repeat eexists.
      forward.
      subst.
      eassumption.
      simpl.
      replace (Int64.repr (Int.signed (Int.repr 1)))
        with (Int64.repr 1) by auto with ints.
      replace  (Int64.repr 1 * i1) with i1.
      eassumption.
      symmetry.
      rewrite Int64.mul_commut.
      eapply Int64.mul_one.
     + pose proof (OK_None_contradiction_1
           (distance (str_b, str_ofs) (b, i))
           ((str_b, str_ofs)) (fin_b, fin_ofs)
           (intp_b, intp_ofs) 0
           Unsigned last_digit_max
           m m' (Some i1)).
      congruence. 
    + pose proof (OK_None_contradiction_2
           (distance (str_b, str_ofs) (b, i))
           ((str_b, str_ofs)) (fin_b, fin_ofs)
           (intp_b, intp_ofs) 0
           Unsigned last_digit_max
           m m').
      congruence. 
Qed.
