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
      + congruence.
      + repeat break_match.
        repeat break_if.
        all: try congruence; eapply IHdist. }
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
  - pose proof (Loop (distance (str_b, str_ofs) (b, i) - 1)%nat ((str_b, str_ofs) ++)
                     (fin_b, fin_ofs) (intp_b, intp_ofs) 0 (sign i0)
                     (max_sign (sign i0)) m'). congruence.
  - pose proof (Loop (distance (str_b, str_ofs) (b, i))%nat ((str_b, str_ofs))
                     (fin_b, fin_ofs) (intp_b, intp_ofs) 0  Unsigned
                     last_digit_max  m'). congruence.  
Qed.

(* Loop correctness cases *)
(* ASN_STRTOX_OK: conversion successfull *)
Lemma asn_strtoimax_lim_loop_ASN_STRTOX_OK_correct :
  forall m ge e dist b ofs le str_b str_ofs fin_b fin_ofs intp_b intp_ofs
         inp_value  m' val s,
    
    le!_str = Some (Vptr str_b str_ofs)  ->
    le!_end = Some (Vptr fin_b fin_ofs) ->
    le!_intp = Some (Vptr intp_b intp_ofs) ->
    le!_value = Some (Vlong inp_value) ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Sign s)) ->

    load_addr Mptr m (fin_b, fin_ofs) = Some (Vptr b ofs) ->

    (distance (str_b, str_ofs) (b,ofs)) = dist ->

    asn_strtoimax_lim_loop m (str_b, str_ofs) (fin_b, fin_ofs)
                           (intp_b, intp_ofs) inp_value s (max_sign s) dist m =
    Some {| return_type := ASN_STRTOX_OK;
            value := Some val;
            memory := Some m'; 
         |}  ->

    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m Out_normal
             /\ le'! _end = Some (Vptr fin_b fin_ofs)
             /\ le'! _str = Some (Vptr b ofs)
             /\ le'! _sign = Some (Vint (Sign s))
             /\ le'! _intp = Some (Vptr intp_b intp_ofs)
             /\ le'! _value = Some (Vlong val).
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
  forall m ge e dist b ofs le str_b str_ofs fin_b fin_ofs intp_b intp_ofs inp_value  m' val s,
    
    le!_str = Some (Vptr str_b str_ofs)  ->
    le!_end = Some (Vptr fin_b fin_ofs) ->
    le!_intp = Some (Vptr intp_b intp_ofs)  ->
    le!_value = Some (Vlong inp_value) ->
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

    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m' (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_EXTRA_DATA), tint))). 
Proof.
  replace (asn_strtox_result_e_to_int ASN_STRTOX_EXTRA_DATA)
    with Int.one by (reflexivity).
  induction dist; intros until s;
    intros Str End Intp Value UB Sign LastD Load Dist Spec;
    simpl in Spec.
  -  all: congruence.
  - repeat break_match;
    unfold store_result in *;
      repeat break_match; try congruence.
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
    repeat break_match;
      unfold store_result in *;
      repeat break_match; try congruence.
    erewrite dist_pred in *.
    + destruct_orb_hyp.
      1 : (eapply exec_loop_minus).
      11: (eapply exec_loop_plus).
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
      11: (eapply exec_loop_plus).
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
    + admit.
    + admit. (* contradiction *)
    + destruct_orb_hyp.
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
      destruct H2.
      break_and.
      eapply exec_loop_none_out_normal;
        try eassumption.
      eexists.
      eassumption.
      repeat eexists.
      repeat econstructor.
      eassumption.
      eassumption.
      repeat econstructor.
      admit. admit.
Admitted.
         
