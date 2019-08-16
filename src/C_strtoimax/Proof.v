Require Import StructTact.StructTactics.
Require Import Core.Core Core.IntLemmas Core.PtrLemmas Core.Tactics.
Require Import C_strtoimax.AST C_strtoimax.Spec C_strtoimax.Switch.

Import ListNotations.

Local Open Scope Int64Scope.

(* Lemmas for each `asn_strtox_result_e` case *)

(* ASN_STRTOX_ERROR_INVAL: str >= *end *)
Lemma asn_strtoimax_lim_ASN_STRTOX_ERROR_INVAL_correct :
  forall m ge e le str_b str_ofs fin_b fin_ofs intp_b intp_ofs m' val,
    
    le ! _str = Some (Vptr str_b str_ofs)  ->
    le ! _end = Some (Vptr fin_b fin_ofs) ->
    le ! _intp = Some (Vptr intp_b intp_ofs)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    asn_strtoimax_lim m (str_b, str_ofs) (fin_b,fin_ofs) (intp_b,intp_ofs) =
    Some {| return_type := ASN_STRTOX_ERROR_INVAL;
        value := val;
        memory := Some m' |} ->
    
    exists (t : trace) (le' : temp_env),
      exec_stmt ge e le m (fn_body f_asn_strtoimax_lim) t le' m'
                (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_INVAL), tint))).
Proof.
  intros until val; intros Str End Intp UB Sign Spec.
  simpl in Spec.                       
  unfold asn_strtoimax_lim in Spec.
  assert (forall dist str fin inp value s last_digit,
             asn_strtoimax_lim_loop m str fin inp value s last_digit dist m
             <> Some {|
                    return_type := ASN_STRTOX_ERROR_INVAL;
                    value := val;
                    memory := Some m' |}) as Loop.
    { induction dist; intros; simpl.
      + break_match;
        congruence.
      + repeat break_match;
          congruence.
    } 
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
Admitted.

(* SN_STRTOX_EXPECT_MORE: reading + or - and reaching *end *)
(* ASN_STRTOX_EXPECT_MORE: reading + or - and reaching *end *)
Lemma asn_strtoimax_lim_ASN_STRTOX_EXPECT_MORE_correct :

  forall m ge e le str_b str_ofs fin_b fin_ofs intp_b intp_ofs m' val,
    
    le!_str = Some (Vptr str_b str_ofs)  ->
    le!_end = Some (Vptr fin_b fin_ofs) ->
    le!_intp = Some (Vptr intp_b intp_ofs)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    asn_strtoimax_lim m (str_b, str_ofs) (fin_b,fin_ofs) (intp_b,intp_ofs) =
    Some
      {|
        return_type := ASN_STRTOX_EXPECT_MORE;
        value := val;
        memory := Some m' |} ->
    
    exists (t : trace) (le' : temp_env),
      exec_stmt ge e le m (fn_body f_asn_strtoimax_lim) t le' m'
                (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_EXPECT_MORE), tint))).
Proof.
  replace (asn_strtox_result_e_to_int ASN_STRTOX_EXPECT_MORE)
    with (Int.repr (-1)) by reflexivity.
  intros until val; intros Str End Intp UB Sign Spec.
  simpl in Spec.    
  assert (forall dist str fin intp v s last_digit m',
             asn_strtoimax_lim_loop m str fin intp v s last_digit dist m <>
             Some {| return_type := ASN_STRTOX_EXPECT_MORE;
                  value := val;
                  memory := Some m' |}) as Loop.
    { induction dist; intros; simpl.
      + break_match; congruence.
      + repeat break_match.
        repeat break_if.
        all: try congruence; eapply IHdist. }
   unfold asn_strtoimax_lim in Spec.  
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
  - pose proof (Loop (distance (str_b, str_ofs) (b, i) - 1)%nat ((str_b, str_ofs) ++)
                     (fin_b, fin_ofs) (intp_b, intp_ofs) 0 (sign i0)
                     (max_sign (sign i0)) m'). admit. (* congruence. *)
  - pose proof (Loop (distance (str_b, str_ofs) (b, i))%nat ((str_b, str_ofs))
                     (fin_b, fin_ofs) (intp_b, intp_ofs) 0  Unsigned
                     last_digit_max  m'). admit. (* congruence. *)
Admitted.

(* Loop correctness cases *)
(* ASN_STRTOX_OK: conversion successfull *)
Lemma asn_strtoimax_lim_loop_ASN_STRTOX_OK_correct :
  forall m ge e  dist b ofs le str_b str_ofs fin_b fin_ofs intp_b intp_ofs inp_value  m' val s,
    
    le!_str = Some (Vptr str_b str_ofs)  ->
    le!_end = Some (Vptr fin_b fin_ofs) ->
    le!_intp = Some (Vptr intp_b intp_ofs)  ->
    le!_value = Some (Vlong inp_value) ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Sign s)) ->

    load_addr Mptr m (fin_b, fin_ofs) = Some (Vptr b ofs) ->

    (distance (str_b, str_ofs) (b,ofs)) = dist ->

    asn_strtoimax_lim_loop m (str_b, str_ofs) (fin_b, fin_ofs) (intp_b, intp_ofs) inp_value s (max_sign s) dist m = Some {| return_type := ASN_STRTOX_OK;
              value := val;
              memory := Some m'; 
           |}  ->

    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m' Out_normal. 
 Proof.
 Admitted.

 

 Lemma asn_strtoimax_lim_loop_ASN_STRTOX_ERROR_RANGE_correct :
   forall m ge e dist b ofs le str_b str_ofs fin_b fin_ofs intp_b intp_ofs inp_value  m' val s,
    
    le!_str = Some (Vptr str_b str_ofs)  ->
    le!_end = Some (Vptr fin_b fin_ofs) ->
    le!_intp = Some (Vptr intp_b intp_ofs)  ->
    le!_value = Some (Vlong inp_value) ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Sign s)) ->

    load_addr Mptr m (fin_b, fin_ofs) = Some (Vptr b ofs) ->

    (distance (str_b, str_ofs) (b,ofs)) = dist ->

    asn_strtoimax_lim_loop m (str_b, str_ofs) (fin_b, fin_ofs) (intp_b, intp_ofs) inp_value s (max_sign s) dist m = Some {| return_type := ASN_STRTOX_ERROR_RANGE;
              value := val;
              memory := Some m'; 
           |}  ->

    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m' (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_RANGE), tint))).         
Admitted.


Lemma asn_strtoimax_lim_loop_ASN_STRTOX_EXTRA_DATA_correct :
  forall m ge e dist b ofs le str_b str_ofs fin_b 
    fin_ofs intp_b intp_ofs inp_value  m' val s,
    
    le ! _str = Some (Vptr str_b str_ofs)  ->
    le ! _end = Some (Vptr fin_b fin_ofs) ->
    le ! _intp = Some (Vptr intp_b intp_ofs)  ->
    le ! _value = Some (Vlong inp_value) ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Sign s)) ->
    le ! _last_digit_max = Some (Vlong (max_sign s)) ->
                                     
    load_addr Mptr m (fin_b, fin_ofs) = Some (Vptr b ofs) ->
    (distance (str_b, str_ofs) (b,ofs)) = dist ->
    
    asn_strtoimax_lim_loop m (str_b, str_ofs) (fin_b, fin_ofs) (intp_b, intp_ofs)
                           inp_value s (max_sign s) dist m =
    Some {| return_type := ASN_STRTOX_EXTRA_DATA;
            value := val;
            memory := Some m';|}  ->

    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m' 
                       (Out_return (Some (Vint (asn_strtox_result_e_to_int 
                                                  ASN_STRTOX_EXTRA_DATA), tint))). 
Proof.
  replace (asn_strtox_result_e_to_int ASN_STRTOX_EXTRA_DATA)
    with Int.one by (reflexivity).
  induction dist; intros until s;
    intros Str End Intp Value UB Sign LastD Load Dist Spec;
    simpl in Spec.
  - break_match. all: congruence.
  - repeat break_match; try congruence.
    (* 3 cases: do one loop and then apply IH *)
    + remember 
         (PTree.set _str
       (Vptr str_b
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
      pose proof (IHdist b ofs le'' str_b (str_ofs + 1)%ptrofs
                         fin_b fin_ofs intp_b intp_ofs
                         (digit_to_num Unsigned i inp_value) m' val s) as IH.
      clear IHdist.
      repeat rewrite set_env_eq_ptree_set in Heqle''.
      destruct IH as [t IH]; subst;
        try (repeat env_assumption || reflexivity).
      { eapply dist_succ; eassumption. }
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
      assert (sem_cmp Clt (Vptr str_b str_ofs) (tptr tschar)
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
      instantiate (1 := Vtrue). admit.
      (* follows from is_digit *)
      forward.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption; try eassumption.
      forward.
      forward.
      simpl.
      instantiate (1 := Vtrue). admit.
      (* follows from is_digit *)
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
    +
      clear IHdist.
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
        assert (sem_cmp Clt (Vptr str_b str_ofs) (tptr tschar)
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
        assert (sem_cmp Clt (Vptr str_b str_ofs) (tptr tschar)
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
        unfold Spec.Sign; unfold mult_sign in H1; destruct s.
        eassumption.
        replace (Int64.repr (Int.signed (Int.repr 1))) with (1)%int64 
          by (auto with ints).
        rewrite Int64.mul_commut.
        rewrite Int64.mul_one.
        assumption.
        econstructor.
        econstructor.
        econstructor.
    + inversion Spec; clear Spec.
      repeat rewrite set_env_eq_ptree_set in *.
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
      assert (sem_cmp Clt (Vptr str_b str_ofs) (tptr tschar)
                      (Vptr b ofs) (tptr tschar) m = Some Vtrue)
        by admit; eassumption.
      forward.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      forward.
      forward.
      simpl.
      instantiate (1 := false).
      admit. (* follows from is_digit i = false *)
      repeat forward.
      repeat forward.
      econstructor.
      repeat forward.
      all: repeat  (econstructor || eassumption || env_assumption).
      simpl.
      replace (Int64.repr (Int.signed (Spec.Sign s)) * inp_value) with
          (mult_sign s inp_value).
      eassumption.
      unfold mult_sign.
      destruct s.
      ++ simpl. auto with ints.
      ++ simpl. rewrite Int.signed_repr_eq.
         break_if.
        * replace  (1 mod Int.modulus) with 1%Z.
          symmetry. rewrite <- Int64.mul_commut.
          apply Int64.mul_one.
          cbn. nia.
        * cbn in g. nia.
Admitted.

Lemma asn_strtoimax_lim_correct :
  forall m ge e le str_b str_ofs fin_b fin_ofs intp_b intp_ofs m' res val,
    
    le ! _str = Some (Vptr str_b str_ofs)  ->
    le ! _end = Some (Vptr fin_b fin_ofs) ->
    le ! _intp = Some (Vptr intp_b intp_ofs)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    asn_strtoimax_lim m (str_b, str_ofs) (fin_b,fin_ofs) (intp_b,intp_ofs)
    = Some {| return_type := res;
              value := val;
              memory := Some m'; 
           |} -> 
    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim.(fn_body) t le' m'
                 (Out_return (Some ((Vint (asn_strtox_result_e_to_int res)), tint))).
Proof.
  induction res.
  - (* ASN_STRTOX_ERROR_RANGE *)
    intros until val; intros Str End Intp UB Sign Spec.
    unfold asn_strtoimax_lim in Spec.
    repeat break_match.
    all: try congruence.
    erewrite dist_pred in Spec.
    + destruct_orb_hyp.
      1 : (eapply exec_loop_minus).
      11: (eapply exec_loop_plus).
      all: repeat rewrite set_env_eq_ptree_set in *.
      all: repeat  eassumption;
        eapply asn_strtoimax_lim_loop_ASN_STRTOX_ERROR_RANGE_correct;
        repeat (env_assumption || econstructor);
     (switch_destruct i0);
       rewrite EQ in *; simpl in Spec; econstructor.
    + eassumption. 
    + eassumption. 
    + destruct_orb_hyp.
      all: repeat rewrite set_env_eq_ptree_set in *.
      eapply exec_loop_none; try eassumption.
       
      (*****************************************************************)
      (* eapply asn_strtoimax_lim_loop_ASN_STRTOX_ERROR_RANGE_correct; *)
      (*   repeat (env_assumption || econstructor).                    *)
      (* instantiate (1 := Unsigned); simpl.                           *)
      (* all: try (econstructor || eassumption).                       *)
      (*****************************************************************)
      admit.
  - (* ASN_STRTOX_ERROR_INVAL *)
    eapply asn_strtoimax_lim_ASN_STRTOX_ERROR_INVAL_correct.     
  - (* ASN_STRTOX_EXPECT_MORE *)
    eapply asn_strtoimax_lim_ASN_STRTOX_EXPECT_MORE_correct. 
  - (*  ASN_STRTOX_EXTRA_DATA *)
    intros until val; intros Str End Intp UB Sign Spec.
    unfold asn_strtoimax_lim in Spec.
    repeat break_match.
    all: try congruence.
    replace (distance (str_b, str_ofs) (b, i) - 1)%nat
      with (distance (str_b, (str_ofs + 1)%ptrofs) (b, i)) in Spec by admit.
    + destruct_orb_hyp.
      1 : (eapply exec_loop_minus).
      11: (eapply exec_loop_plus).
      all:
        repeat eassumption;
        eapply asn_strtoimax_lim_loop_ASN_STRTOX_EXTRA_DATA_correct;
        repeat (env_assumption || econstructor);
        switch_destruct i0;
        rewrite EQ in *; simpl in Spec;
          try reflexivity.
      (* 1-2: admit. *)
      all: admit.
    + destruct_orb_hyp.
      eapply exec_loop_none; try eassumption.
      (****************************************************************)
      (* eapply asn_strtoimax_lim_loop_ASN_STRTOX_EXTRA_DATA_correct; *)
      (*   repeat (env_assumption || econstructor).                   *)
      (* instantiate (1 := Unsigned); simpl.                          *)
      (* all: try (econstructor || eassumption).                      *)
      (* 1-2: admit.                                                  *)
      (****************************************************************)
      admit.
- (* ASN_STRTOX_OK *)
    intros until val; intros Str End Intp UB Sign Spec.
    unfold asn_strtoimax_lim in Spec;
      repeat break_match; try discriminate; subst.
    + destruct_orb_hyp; switch_destruct i0; subst.
      *
        remember (
    (PTree.set _value (Vlong (cast_int_long Signed (Int.repr 0)))
       (PTree.set _t'5 (Vptr b i)
          (PTree.set _str
             (Vptr str_b
                (str_ofs + Ptrofs.repr (sizeof ge tschar) * ptrofs_of_int Signed (Int.repr 1))%ptrofs)
             (PTree.set _sign (Vint (Int.neg (Int.repr 1)))
                (PTree.set _last_digit_max
                   (Vlong
                      (Int64.modu
                         (Int64.not (cast_int_long Signed (Int.repr 0)) >>
                          Int64.repr (Int.unsigned (Int.repr 1))) (cast_int_long Signed (Int.repr 10)) +
                       cast_int_long Signed (Int.repr 1)))
                   (PTree.set _t'4 (Vint minus_char)
                      (PTree.set _t'6 (Vptr b i)
                         (PTree.set _last_digit_max
                            (Vlong
                               (Int64.modu
                                  (Int64.not (cast_int_long Signed (Int.repr 0)) >>
                                   Int64.repr (Int.unsigned (Int.repr 1)))
                                  (cast_int_long Signed (Int.repr 10))))
                            (PTree.set _upper_boundary
                               (Vlong
                                  (Int64.divu
                                     (Int64.not (cast_int_long Signed (Int.repr 0)) >>
                                      Int64.repr (Int.unsigned (Int.repr 1)))
                                     (cast_int_long Signed (Int.repr 10))))
                               (PTree.set _sign (Vint (Int.repr 1)) le))))))))))
          )
          as X.
        

        pose proof asn_strtoimax_lim_loop_ASN_STRTOX_OK_correct m ge e (distance (str_b, str_ofs) (b, i) - 1)
          b i X str_b (str_ofs + 1)%ptrofs fin_b fin_ofs intp_b intp_ofs Int64.zero m' val (sign minus_char).
        destruct H as [t H]; subst X; repeat gso_simpl; repeat gss_simpl;
          try eassumption.
        auto with ptrofs.
        reflexivity.
        reflexivity.
        reflexivity.
        symmetry.
        eapply dist_pred; try eassumption.
        destruct H as [le'' H].

        eexists. eexists.
        simpl fn_body.
        fold f_asn_strtoimax_lim_loop.
        seq1; exec_until_seq.
        seq1; exec_until_seq.
        seq1; exec_until_seq.
        seq1; exec_until_seq.
        seq1; exec_until_seq.
        repeat gso_simpl; eassumption.
        unfold load_addr in Heqo; eassumption.
        repeat gso_simpl; eassumption.
        repeat gss_simpl; econstructor.
        unfold addr_ge, ptr_ge in Heqo0; cbn; unfold cmp_ptr; rewrite Heqo0; econstructor.
        econstructor.
        econstructor.
        seq1; exec_until_seq.
        seq1; exec_until_seq.
        repeat gso_simpl; eassumption.
        eassumption.
        replace Out_normal with (outcome_switch Out_normal).
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        repeat gso_simpl; eassumption.
        econstructor.
        econstructor.
        eassumption.
        econstructor.
        econstructor.
        repeat econstructor.
        repeat gso_simpl; repeat gss_simpl; econstructor.
        econstructor.

        repeat econstructor.
        repeat gso_simpl; eassumption.
        econstructor.
        repeat gso_simpl; eassumption.
        eassumption.
        gso_simpl; gss_simpl; econstructor.
        gss_simpl; econstructor.

        unfold addr_ge, ptr_ge in Heqo0; cbn; unfold cmp_ptr.
        replace (Ptrofs.repr 1 * Ptrofs.of_ints (Int.repr 1))%ptrofs
          with Ptrofs.one
          by (auto with ptrofs).
        cbn in Heqo2.
        unfold ptr_ge in Heqo2.
        rewrite Heqo2.
        econstructor.

        econstructor.

        econstructor.
        constructor.
        seq1. seq1.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        eassumption.
        repeat econstructor; try env_assumption.
Admitted.
