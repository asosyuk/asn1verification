(*Require Import StructTact.StructTactics.
Require Import Core.Core Core.Notations Core.IntLemmas Core.PtrLemmas
        Core.IntPtrLemmas Core.Tactics.
Require Import AST Spec Switch SpecLemmas AbstractSpec.

Import ListNotations.

Local Open Scope Int64Scope.

(* Lemmas for each `asn_strtox_result_e` case *)

  Lemma asn_strtoimax_lim_loop_ASN_STRTOX_EXTRA_DATA_correct :
  forall m ge e dist b ofs le str_b str_ofs fin_b 
    fin_ofs intp_b intp_ofs inp_value  m' val p s' s,
    
    le ! _str = Some (Vptr str_b str_ofs)  ->
    le ! _end = Some (Vptr fin_b fin_ofs) ->
    le ! _intp = Some (Vptr intp_b intp_ofs)  ->
    le ! _value = Some (Vlong inp_value) ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (sign_to_int s)) ->
    le ! _last_digit_max = Some (Vlong (max_sign s)) ->
                                     
    load_addr Mptr m (fin_b, fin_ofs) = Some (Vptr b ofs) ->
    (distance m (str_b, str_ofs) (b,ofs)) = Some dist ->
    
    asn_strtoimax_lim_loop m (str_b, str_ofs) (fin_b, fin_ofs) (intp_b, intp_ofs)
                           inp_value s (max_sign s) (Some dist) m =
    Some {| return_type := ASN_STRTOX_EXTRA_DATA;
            value := val;
            str_pointer := p;
            memory := Some m';
            sign := s' |}  ->

   exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m' 
              (Out_return (Some (Vint
                                   (asn_strtox_result_e_to_int
                                      ASN_STRTOX_EXTRA_DATA), tint))).
Proof.
  replace (asn_strtox_result_e_to_int ASN_STRTOX_EXTRA_DATA)
    with Int.one by (reflexivity).
  induction dist; intros until s;
    intros Str End Intp Value UB Sign LastD Load Dist Spec;
    simpl in Spec.
  - all: try break_match; congruence.
  - repeat break_match;
    unfold store_result in *;
      repeat break_match; try congruence.
    (* 4 cases *)
    + (* Case   Heqb0 : Spec.is_digit i = true
         Heqb1 : (inp_value < upper_boundary) = true *)
      remember 
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
                         (digit_to_num Unsigned i inp_value) m' val p s' s) as IH.
      clear IHdist.
      repeat rewrite set_env_eq_ptree_set in Heqle''.
      destruct IH as [t IH]; subst;
        try (repeat env_assumption || reflexivity).
      eapply dist_succ_load;
        eassumption.
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
      eapply distance_to_sem_cmp_lt;
        eassumption.
      repeat econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption; try eassumption.
      forward.
      simpl.
      unfold Spec.is_digit in Heqb0.
      destruct_andb_hyp.
      instantiate (1 := (Val.of_bool true)).
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
      unfold Spec.is_digit in Heqb0.
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
      all: break_and; eassumption.
    + (* (inp_value == upper_boundary) 
&& (int_to_int64 (i - Spec.zero_char)%int <= max_sign Signed) = true, Signed
          do one loop and return *)
      replace b0 with b in *
        by (eapply mem_load_inj_ptr;
         eassumption).
      replace i0 with ofs in *
        by (eapply mem_load_inj_ptr;
         eassumption).
      unfold max_sign in *.
      unfold Spec.is_digit in *.
      destruct_andb_hyp.
      destruct_andb_hyp.
      destruct (Int.repr 48 <= i1)%int eqn : I148.
      destruct (i1 <= Int.repr 57)%int eqn : I157.
      all: try intuition.
      * (* replace b0 with b in *;
        by (eapply mem_load_inj_ptr;
         eassumption).
      replace i0 with ofs in *
        by (eapply mem_load_inj_ptr;
         eassumption). *)
        inversion Spec.
        repeat eexists.
        eapply exec_Sloop_stop1.
        instantiate (1 := (Out_return (Some ((Vint Int.one), tint)))).
        econstructor. (* Wrong local env instantiated  by repeat econstructor ??? *)
        econstructor.
        econstructor.
        repeat econstructor; try env_assumption.
        repeat econstructor; try env_assumption.
        try eassumption.
        econstructor.
        eapply distance_to_sem_cmp_lt.
        eassumption.
        repeat econstructor.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        econstructor.
        econstructor.
        repeat econstructor.
        repeat env_assumption; try eassumption.
        eassumption.
        env_assumption.
        econstructor.
        apply sem_Cle_Cge.
        apply int_le_sem_Cle.
        eassumption.
        forward.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        econstructor.
        econstructor.
        repeat econstructor.
        repeat env_assumption; try eassumption.
        eassumption.
        env_assumption.
        econstructor.
        forward.
        simpl.
        bool_rewrite.
        reflexivity.
        forward.
        simpl.
        bool_rewrite.
        econstructor.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        forward.
        simpl.
        bool_rewrite.
        econstructor.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        forward.
        simpl.
        unfold int_to_int64 in *.
        unfold Spec.zero_char in *.
        bool_rewrite.
        forward.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        econstructor.
        forward.
        econstructor.
        forward.
        eapply exec_Sseq_2.
        econstructor.
        forward.
        forward.
        eapply addr_lt_to_sem_cmp_lt;
          eassumption.
         all: repeat (match goal with
                     | [|- context[bool_val]]=> simpl; bool_rewrite
                     | [|- context[Val.of_bool]] => simpl; bool_rewrite
                     end ||
                         forward ||
                         replace (negb (1 == 0)%int) with true
                    by (auto with ints)).
        simpl.
        remember (Int64.neg inp_value * Int64.repr (Int.signed (Int.repr 10)) - 
                  Int64.repr (Int.signed (i - Int.repr 48)%int)) as res.
        replace (Int64.repr (Int.signed (Int.repr 1)) * res) with res.
        subst.
        simpl.
        eassumption.
        replace (Int64.repr (Int.signed (Int.repr 1))) with (1)%int64
          by (auto with ints).       
        symmetry.
        rewrite Int64.mul_commut.
        eapply Int64.mul_one.
        discriminate.
      * inversion Spec.
        repeat eexists.
               eapply exec_Sloop_stop1.
        instantiate (1 := (Out_return (Some ((Vint Int.one), tint)))).
        econstructor. (* Wrong local env instantiated  by repeat econstructor ??? *)
        econstructor.
        econstructor.
        repeat econstructor; try env_assumption.
        repeat econstructor; try env_assumption.
        try eassumption.
        econstructor.
        eapply distance_to_sem_cmp_lt.
        eassumption.
        repeat econstructor.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        econstructor.
        econstructor.
        repeat econstructor.
        repeat env_assumption; try eassumption.
        eassumption.
        env_assumption.
        econstructor.
        apply sem_Cle_Cge.
        apply int_le_sem_Cle.
        eassumption.
        forward.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        econstructor.
        econstructor.
        repeat econstructor.
        repeat env_assumption; try eassumption.
        eassumption.
        env_assumption.
        econstructor.
        forward.
        simpl.
        bool_rewrite.
        reflexivity.
        forward.
        simpl.
        bool_rewrite.
        econstructor.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        forward.
        simpl.
        bool_rewrite.
        econstructor.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        forward.
        simpl.
        unfold int_to_int64 in *.
        unfold Spec.zero_char in *.
        bool_rewrite.
        forward.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        econstructor.
        forward.
        econstructor.
        forward.
        eapply exec_Sseq_2.
        econstructor.
        forward.
        forward.
        eapply addr_lt_to_sem_cmp_lt;
          eassumption.
        all: repeat (match goal with
                     | [|- context[bool_val]]=> simpl; bool_rewrite
                     | [|- context[Val.of_bool]] => simpl; bool_rewrite
                     end ||
                         forward ||
                         replace (negb (1 == 0)%int) with true
                    by (auto with ints)).
        simpl.
        unfold int_to_int64 in *.
        remember (Int64.neg inp_value * Int64.repr (Int.signed (Int.repr 10)) - 
                  Int64.repr (Int.signed (i - Int.repr 48)%int)) as res.
        replace (Int64.repr (Int.signed (Int.repr 1)) * res) with res.
        subst.
        eassumption.
        replace (Int64.repr (Int.signed (Int.repr 1))) with (1)%int64
          by (auto with ints).
        symmetry.
        rewrite Int64.mul_commut.
        eapply Int64.mul_one.
        discriminate.
     + (* (inp_value == upper_boundary) 
&& (int_to_int64 (i - Spec.zero_char)%int <= max_sign Signed) = true, UnSigned
          do one loop and return *)
      replace b0 with b in *
        by (eapply mem_load_inj_ptr;
         eassumption).
      replace i0 with ofs in *
        by (eapply mem_load_inj_ptr;
         eassumption).
      unfold max_sign in *.
      unfold Spec.is_digit in *.
      destruct_andb_hyp.
      destruct_andb_hyp.
      destruct (Int.repr 48 <= i1)%int eqn : I148.
      destruct (i1 <= Int.repr 57)%int eqn : I157.
      all: try intuition.
      * (* replace b0 with b in *;
        by (eapply mem_load_inj_ptr;
         eassumption).
      replace i0 with ofs in *
        by (eapply mem_load_inj_ptr;
         eassumption). *)
        inversion Spec.
        repeat eexists.
        eapply exec_Sloop_stop1.
        instantiate (1 := (Out_return (Some ((Vint Int.one), tint)))).
        econstructor. (* Wrong local env instantiated  by repeat econstructor ??? *)
        econstructor.
        econstructor.
        repeat econstructor; try env_assumption.
        repeat econstructor; try env_assumption.
        try eassumption.
        econstructor.
        eapply distance_to_sem_cmp_lt.
        eassumption.
        repeat econstructor.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        econstructor.
        econstructor.
        repeat econstructor.
        repeat env_assumption; try eassumption.
        eassumption.
        env_assumption.
        econstructor.
        apply sem_Cle_Cge.
        apply int_le_sem_Cle.
        eassumption.
        forward.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        econstructor.
        econstructor.
        repeat econstructor.
        repeat env_assumption; try eassumption.
        eassumption.
        env_assumption.
        econstructor.
        forward.
        simpl.
        bool_rewrite.
        reflexivity.
        forward.
        simpl.
        bool_rewrite.
        econstructor.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        forward.
        simpl.
        bool_rewrite.
        econstructor.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        forward.
        simpl.
        unfold int_to_int64 in *.
        unfold Spec.zero_char in *.
        bool_rewrite.
        forward.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        econstructor.
        forward.
        econstructor.
        forward.
        eapply exec_Sseq_2.
        econstructor.
        forward.
        forward.
        eapply addr_lt_to_sem_cmp_lt;
          eassumption.
        all: repeat (match goal with
                     | [|- context[bool_val]]=> simpl; bool_rewrite
                     | [|- context[Val.of_bool]] => simpl; bool_rewrite
                     end ||
                         forward ||
                         replace (negb (1 == 0)%int) with true
                    by (auto with ints)).
        unfold int_to_int64 in *.
        simpl.
        remember (inp_value * Int64.repr (Int.signed (Int.repr 10)) +
                  Int64.repr (Int.signed (i - Int.repr 48)%int))  as res.
        replace (Int64.repr (Int.signed (Int.repr 1)) * res) with res.
        subst.
        simpl.
        eassumption.
        replace (Int64.repr (Int.signed (Int.repr 1))) with (1)%int64
          by (auto with ints).
        symmetry.
        rewrite Int64.mul_commut.
        eapply Int64.mul_one.
        discriminate.
      * inversion Spec.
        repeat eexists.
               eapply exec_Sloop_stop1.
        instantiate (1 := (Out_return (Some ((Vint Int.one), tint)))).
        econstructor. (* Wrong local env instantiated  by repeat econstructor ??? *)
        econstructor.
        econstructor.
        repeat econstructor; try env_assumption.
        repeat econstructor; try env_assumption.
        try eassumption.
        econstructor.
        eapply distance_to_sem_cmp_lt.
        eassumption.
        repeat econstructor.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        econstructor.
        econstructor.
        repeat econstructor.
        repeat env_assumption; try eassumption.
        eassumption.
        env_assumption.
        econstructor.
        apply sem_Cle_Cge.
        apply int_le_sem_Cle.
        eassumption.
        forward.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        econstructor.
        econstructor.
        repeat econstructor.
        repeat env_assumption; try eassumption.
        eassumption.
        env_assumption.
        econstructor.
        forward.
        simpl.
        bool_rewrite.
        reflexivity.
        forward.
        simpl.
        bool_rewrite.
        econstructor.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        forward.
        simpl.
        bool_rewrite.
        econstructor.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        forward.
        simpl.
        unfold int_to_int64 in *.
        unfold Spec.zero_char in *.
        bool_rewrite.
        forward.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        econstructor.
        forward.
        econstructor.
        forward.
        eapply exec_Sseq_2.
        econstructor.
        forward.
        forward.
        eapply addr_lt_to_sem_cmp_lt;
          eassumption.
        forward.
        all: repeat (match goal with
                     | [|- context[bool_val]]=> simpl; bool_rewrite
                     | [|- context[Val.of_bool]] => simpl; bool_rewrite
                     end ||
                         forward ||
                         replace (negb (1 == 0)%int) with true
                    by (auto with ints)).
        simpl.
        unfold int_to_int64 in *.
        remember (inp_value * Int64.repr (Int.signed (Int.repr 10)) +
         Int64.repr (Int.signed (i - Int.repr 48)%int)) as res.
        replace (Int64.repr (Int.signed (Int.repr 1)) * res) with res.
        subst.
        eassumption.
        replace (Int64.repr (Int.signed (Int.repr 1))) with (1)%int64
          by (auto with ints).
        symmetry.
        rewrite Int64.mul_commut.
        eapply Int64.mul_one.
        discriminate.
     + clear IHdist.
      unfold Spec.is_digit, andb in Heqb0.
      break_if; eexists; eexists.
      * (* case when i > 57 *)
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
         eassumption.
         econstructor.
         econstructor.
        eassumption.
        econstructor.
        econstructor.
        econstructor; gso_simpl; eassumption.
        econstructor; gss_simpl; econstructor.
        simpl.
        eapply distance_to_sem_cmp_lt;
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
        unfold mult_sign, sign_to_int.
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
        econstructor.
        eassumption.
        econstructor.
        econstructor.
        eassumption.
        econstructor.
        econstructor.
        econstructor; gso_simpl; eassumption.
        econstructor; gss_simpl; econstructor.
        simpl.
        eapply distance_to_sem_cmp_lt;
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
        econstructor; repeat gso_simpl; eassumption.
        econstructor; repeat gso_simpl; eassumption.
        econstructor.
        econstructor.
        econstructor.
        eassumption.
        econstructor.
        econstructor.
        econstructor.
        econstructor; repeat gso_simpl; eassumption.
        econstructor.
        econstructor; repeat gso_simpl; eassumption.
        econstructor; repeat gso_simpl; eassumption.
        econstructor.
        econstructor.
        econstructor.
        econstructor.
        inv Spec; cbn.
        unfold  sign_to_int; unfold mult_sign in *; destruct s'.
        eassumption.
        replace (Int64.repr (Int.signed (Int.repr 1))) with (1)%int64 
          by (auto with ints).
        rewrite Int64.mul_commut.
        rewrite Int64.mul_one.
        assumption.
        econstructor.
        econstructor.
        econstructor.
        Qed.

(* ASN_STRTOX_ERROR_INVAL: str >= *end *)
Lemma asn_strtoimax_lim_ASN_STRTOX_ERROR_INVAL_correct :
  forall m ge e le str_b str_ofs fin_b fin_ofs intp_b intp_ofs m' p s' val,
    
    le ! _str = Some (Vptr str_b str_ofs)  ->
    le ! _end = Some (Vptr fin_b fin_ofs) ->
    le ! _intp = Some (Vptr intp_b intp_ofs)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    asn_strtoimax_lim m (str_b, str_ofs) (fin_b, fin_ofs) (intp_b, intp_ofs) =
    Some {| return_type := ASN_STRTOX_ERROR_INVAL;
            value := val;
            str_pointer := p; 
            memory := Some m';
            sign := s' |} ->    
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
                    memory := Some m';
                    sign := s'; |}) as Loop.
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
  forall m ge e le str_b fin_b intp_b str_ofs fin_ofs intp_ofs m' p s' val,
    
    le ! _str = Some (Vptr str_b str_ofs)  ->
    le ! _end = Some (Vptr fin_b fin_ofs) ->
    le ! _intp = Some (Vptr intp_b intp_ofs)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    asn_strtoimax_lim m (str_b, str_ofs) (fin_b, fin_ofs) (intp_b, intp_ofs) =
    Some
      {|
        return_type := ASN_STRTOX_EXPECT_MORE;
        value := val;
        str_pointer := p;
        memory := Some m';
        sign := s';
      |} ->
    
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
                     memory := Some m';
                     sign := s';|}) as Loop.
    { destruct dist as [dist|].
      - induction dist; intros; simpl. 
        + try break_match; congruence. 
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
      eapply ptr_ge_to_sem_cmp; eassumption.
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
      eapply ptr_ge_to_sem_cmp; eassumption.
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
      eapply ptr_ge_to_sem_cmp; eassumption.
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
      eapply ptr_ge_to_sem_cmp; eassumption.
      all: Tactics.forward; try discriminate.
  - pose proof (Loop (Some (n - 1)%nat) ((str_b, str_ofs) ++) 
                     (fin_b, fin_ofs) (intp_b, intp_ofs) 0 (char_to_sign i0) 
                     (max_sign (char_to_sign i0)) m'). 
      congruence.
  - pose proof (Loop (Some n) ((str_b, str_ofs)) 
                     (fin_b, fin_ofs) (intp_b, intp_ofs) 0 Unsigned 
                     last_digit_max m'). congruence.
Qed.

(* Loop correctness cases *)
(* ASN_STRTOX_OK: conversion successfull *)
Lemma asn_strtoimax_lim_loop_ASN_STRTOX_OK_correct :
  forall m ge e dist b ofs le strp_b strp_ofs str_b str_ofs fin_b fin_ofs intp_b intp_ofs
         inp_value  m' val s' s,
    
    le!_str = Some (Vptr str_b str_ofs)  ->
    le!_end = Some (Vptr fin_b fin_ofs) ->
    le!_intp = Some (Vptr intp_b intp_ofs) ->
    le!_value = Some (Vlong inp_value) ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (sign_to_int s)) ->
    le ! _last_digit_max = Some (Vlong (max_sign s)) ->

    load_addr Mptr m (fin_b, fin_ofs) = Some (Vptr b ofs) ->
    
    (distance m (str_b, str_ofs) (b,ofs)) = Some dist ->

    asn_strtoimax_lim_loop m (str_b, str_ofs) (fin_b, fin_ofs)
                           (intp_b, intp_ofs) inp_value s (max_sign s) (Some dist) m =
    Some {| return_type := ASN_STRTOX_OK;
            value := Some val;
            str_pointer := Some (strp_b, strp_ofs);
            memory := Some m';
            sign := s';
         |}  ->

    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m' Out_normal
             /\ le'! _end = Some (Vptr fin_b fin_ofs)
             /\ le'! _str = Some (Vptr strp_b strp_ofs)
             /\ le'! _sign = Some (Vint (sign_to_int s'))
             /\ le'! _intp = Some (Vptr intp_b intp_ofs)
             /\ le'! _value = Some (Vlong val)
             /\ m' = m.
Proof.
  induction dist; intros until s;
  intros Str End Intp Value UB Sign LastD Load Dist Spec;
  simpl in Spec.
  - all:
      repeat break_match; try congruence.
    inversion Spec.
    rewrite <- H3.
    (* break from the loop, follows from distance *)
    repeat eexists.
    eapply exec_Sloop_stop1.
    eapply exec_Sseq_2.
    forward.
    pose proof (distance_O m str_b b str_ofs ofs) as K.
    assert ((ofs <u ofs)%ptrofs = false) as Ofs.
    { unfold Ptrofs.ltu.
      break_if.
      nia.
      auto. }
    inversion K as [J1 J2].
    destruct (J1 Dist). clear J1 J2 K.
    inversion H.
    simpl.
    unfold sem_cmp, cmp_ptr, Val.cmplu_bool,
    Ptrofs.cmpu; try (rewrite Ofs);
      repeat break_match;
      repeat (congruence || intuition || discriminate).
    simpl.
    rewrite H7 in H5.
    rewrite H8 in H5.
    unfold Mem.weak_valid_pointer in H5.
    repeat break_if; simpl; try intuition.
    f_equal.
    bool_rewrite.
    intuition.
    destruct_andb_hyp; intuition; congruence.
    
    forward.
    all: repeat (env_assumption || econstructor
                 || discriminate).
    rewrite <- H1.
    rewrite <- H2.
    assumption.
    rewrite <- H4.
    eassumption.
    rewrite <- H0.
    eassumption.
  - repeat break_match;
    unfold store_result in *;
      repeat break_match; try congruence.
    + (* Case   Heqb0 : Spec.is_digit i = true
         Heqb1 : (inp_value < upper_boundary) = true *)
      remember 
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
      pose proof (IHdist b ofs le'' strp_b strp_ofs str_b (str_ofs + 1)%ptrofs
                         fin_b fin_ofs intp_b intp_ofs
                         (digit_to_num Unsigned i inp_value) m' val s' s) as IH.
      clear IHdist.
      repeat rewrite set_env_eq_ptree_set in Heqle''.
      destruct IH as [t IH]; subst;
        try (repeat env_assumption || reflexivity).
      eapply dist_succ_load;
        eassumption.
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
      eapply distance_to_sem_cmp_lt;
        eassumption.
      repeat econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption; try eassumption.
      forward.
      simpl.
      unfold Spec.is_digit in Heqb0.
      destruct_andb_hyp.
      apply sem_Cle_Cge.
      apply int_le_sem_Cle.
      eassumption.
      forward.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption; try eassumption.
      forward.
      forward.
      simpl.
      unfold Spec.is_digit in Heqb0.
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
      all: break_and; eassumption.
    + (* Case (inp_value == upper_boundary) 
           && (int_to_int64 (i - Spec.zero_char)%int <= last_digit_max) = true 
         addr_lt m (str_b, (str_ofs + 1)%ptrofs) (b0, i0) = Some false
         Signed 
       *) (* go through one loop and break *)
      replace b0 with b in *
        by (eapply mem_load_inj_ptr;
         eassumption).
      replace i0 with ofs in *
        by (eapply mem_load_inj_ptr;
         eassumption).
      unfold max_sign in *.
      unfold Spec.is_digit in *.
      repeat destruct_andb_hyp.
      inversion Spec.
      rewrite <- H7.
      repeat eexists.
      eapply exec_Sloop_stop1.
      instantiate (1 := Out_break).
      econstructor. (* Wrong local env instantiated  by repeat econstructor ??? *)
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption.
      repeat econstructor; try env_assumption.
      try eassumption.
      econstructor.
      eapply distance_to_sem_cmp_lt.
      eassumption.
      repeat econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption; try eassumption.
      forward.
      simpl.
      apply sem_Cle_Cge.
      apply int_le_sem_Cle.
      eassumption.
      forward.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption; try eassumption.
      forward.
      forward.
      simpl.
      bool_rewrite.
      reflexivity.
      forward.
      simpl.
      bool_rewrite.
      econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      forward.
      simpl.
      repeat destruct_andb_hyp.
      bool_rewrite.
      econstructor.
      forward.
      simpl.
      unfold int_to_int64 in *.
      unfold Spec.zero_char in *.
      bool_rewrite.
      forward.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      forward.
      simpl.
      eapply addr_lt_to_sem_cmp_lt.
      eassumption.
      forward.
      econstructor.
       all: repeat (env_assumption || econstructor
                    || discriminate).
       all: inversion Spec;
         try reflexivity.   
    + (* Case (inp_value == upper_boundary) 
           && (int_to_int64 (i - Spec.zero_char)%int <= last_digit_max) = true 
         addr_lt m (str_b, (str_ofs + 1)%ptrofs) (b0, i0) = Some false
         Unsigned *)
      (* go through one loop and break *)
      replace b0 with b in *
        by (eapply mem_load_inj_ptr;
         eassumption).
      replace i0 with ofs in *
        by (eapply mem_load_inj_ptr;
         eassumption).
      unfold max_sign in *.
      unfold Spec.is_digit in *.
      repeat destruct_andb_hyp.
      repeat eexists.
      eapply exec_Sloop_stop1.
      instantiate (1 := Out_break).
      econstructor. 
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption.
      repeat econstructor; try env_assumption.
      try eassumption.
      econstructor.
      eapply distance_to_sem_cmp_lt.
      eassumption.
      repeat econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption; try eassumption.
      forward.
      simpl.
      apply sem_Cle_Cge.
      apply int_le_sem_Cle.
      eassumption.
      forward.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption; try eassumption.
      forward.
      forward.
      simpl.
      bool_rewrite.
      reflexivity.
      forward.
      simpl.
      bool_rewrite.
      econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      forward.
      simpl.
      repeat destruct_andb_hyp.
      bool_rewrite.
      econstructor.
      forward.
      simpl.
      unfold int_to_int64 in *.
      unfold Spec.zero_char in *.
      bool_rewrite.
      forward.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      forward.
      eapply addr_lt_to_sem_cmp_lt.
      eassumption.
      forward.
      all: inversion Spec;
        repeat (env_assumption || econstructor
                || discriminate).
Qed.

Lemma asn_strtoimax_lim_loop_ASN_STRTOX_ERROR_RANGE_correct :
   forall m ge e dist b ofs le str_b str_ofs fin_b fin_ofs
          intp_b intp_ofs inp_value  m' p val s' s,
    
    le!_str = Some (Vptr str_b str_ofs)  ->
    le!_end = Some (Vptr fin_b fin_ofs) ->
    le!_intp = Some (Vptr intp_b intp_ofs)  ->
    le!_value = Some (Vlong inp_value) ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (sign_to_int s)) ->
    le ! _last_digit_max = Some (Vlong (max_sign s)) ->

    load_addr Mptr m (fin_b, fin_ofs) = Some (Vptr b ofs) ->
    (distance m (str_b, str_ofs) (b,ofs)) = Some dist ->

    asn_strtoimax_lim_loop m (str_b, str_ofs) (fin_b, fin_ofs)
                           (intp_b, intp_ofs) inp_value s (max_sign s) (Some dist) m =
    Some {| return_type := ASN_STRTOX_ERROR_RANGE;
            value := val;
            str_pointer := p;
            memory := Some m';
            sign := s';
           |}  ->

    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m'
                       (Out_return
                          (Some (Vint (asn_strtox_result_e_to_int
                                               ASN_STRTOX_ERROR_RANGE), tint))).
   Proof.
replace (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_RANGE)
    with (Int.repr (-3)) by (reflexivity).
  induction dist; intros until s;
    intros Str End Intp Value UB Sign LastD Load Dist Spec;
    simpl in Spec.
  - all: try break_match; congruence.
  - repeat break_match;
    unfold store_result in *;
      repeat break_match; try congruence.
    (* 4 cases *)
    + (* Case   Heqb0 : Spec.is_digit i = true
         Heqb1 : (inp_value < upper_boundary) = true *)
      remember 
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
      pose proof (IHdist b ofs le''  str_b (str_ofs + 1)%ptrofs
                         fin_b fin_ofs intp_b intp_ofs
                         (digit_to_num Unsigned i inp_value) m' p val s' s) as IH.
      clear IHdist.
      repeat rewrite set_env_eq_ptree_set in Heqle''.
      destruct IH as [t IH]; subst;
        try (repeat env_assumption || reflexivity).
      eapply dist_succ_load;
        eassumption.
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
      eapply distance_to_sem_cmp_lt;
        eassumption.
      repeat econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption; try eassumption.
      forward.
      simpl.
      unfold Spec.is_digit in Heqb0.
      destruct_andb_hyp.
      apply sem_Cle_Cge.
      apply int_le_sem_Cle.
      eassumption.
      forward.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption; try eassumption.
      forward.
      forward.
      simpl.
      unfold Spec.is_digit in Heqb0.
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
      all: break_and; eassumption.
    + (* (inp_value == upper_boundary) && (int_to_int64 (i - Spec.zero_char)%int <= max_sign Signed) = true, Signed
          do one loop and return
       *)
      (* Case (inp_value == upper_boundary) 
           && (int_to_int64 (i - Spec.zero_char)%int <= last_digit_max) = true 
         addr_lt m (str_b, (str_ofs + 1)%ptrofs) (b0, i0) = Some false
         Signed 
       *) (* go through one loop and break *)
      replace b0 with b in *
        by (eapply mem_load_inj_ptr;
         eassumption).
      replace i0 with ofs in *
        by (eapply mem_load_inj_ptr;
         eassumption).
      unfold max_sign in *.
      unfold Spec.is_digit in *.
      repeat destruct_andb_hyp.
      inversion Spec.
      repeat eexists.
      eapply exec_Sloop_stop1.
      instantiate (1 := (Out_return (Some (Vint (Int.repr (-3)), tint)))).
      econstructor. (* Wrong local env instantiated  by repeat econstructor ??? *)
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption.
      repeat econstructor; try env_assumption.
      try eassumption.
      econstructor.
      eapply distance_to_sem_cmp_lt.
      eassumption.
      repeat econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor.
      repeat env_assumption; try eassumption.
      eassumption.
      env_assumption.
      econstructor.
      apply sem_Cle_Cge.
      apply int_le_sem_Cle.
      eassumption.
      forward.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor.
      repeat env_assumption; try eassumption.
      eassumption.
      env_assumption.
      econstructor.
      forward.
      simpl.
      bool_rewrite.
      reflexivity.
      forward.
      simpl.
      bool_rewrite.
      econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      forward.
      simpl.
      bool_rewrite.
      econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      forward.
      simpl.
      unfold int_to_int64 in *.
      unfold Spec.zero_char in *.
      bool_rewrite.
      forward.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      forward.
      econstructor.
      forward.
      eapply exec_Sseq_2.
      econstructor.
      forward.
      forward.
      eapply addr_lt_to_sem_cmp_lt;
        eassumption.  
      all: repeat (match goal with
                     | [|- context[bool_val]]=> simpl; bool_rewrite
                     | [|- context[Val.of_bool]] => simpl; bool_rewrite
                     end ||
                         forward ||
                         replace (negb (1 == 0)%int) with true
                    by (auto with ints)).
      rewrite H8.
      forward.
      discriminate.
    + (* (inp_value == upper_boundary) && (int_to_int64 (i - Spec.zero_char)%int <= max_sign Signed) = true, Unsigned
          do one loop and return
       *)
      replace b0 with b in *
        by (eapply mem_load_inj_ptr;
         eassumption).
      replace i0 with ofs in *
        by (eapply mem_load_inj_ptr;
            eassumption).
      unfold max_sign in *.
      unfold Spec.is_digit in *.
      repeat destruct_andb_hyp.
      inversion Spec.
      repeat eexists.
      eapply exec_Sloop_stop1.
      instantiate (1 := (Out_return (Some (Vint (Int.repr (-3)), tint)))).
      econstructor. (* Wrong local env instantiated  by repeat econstructor ??? *)
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption.
      repeat econstructor; try env_assumption.
      try eassumption.
      econstructor.
      eapply distance_to_sem_cmp_lt.
      eassumption.
      repeat econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor.
      repeat env_assumption; try eassumption.
      eassumption.
      env_assumption.
      econstructor.
      apply sem_Cle_Cge.
      apply int_le_sem_Cle.
      eassumption.
      forward.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor.
      repeat env_assumption; try eassumption.
      eassumption.
      env_assumption.
      econstructor.
      forward.
      simpl.
      bool_rewrite.
      reflexivity.
      forward.
      simpl.
      bool_rewrite.
      econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      forward.
      simpl.
      bool_rewrite.
      econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      forward.
      simpl.
      unfold int_to_int64 in *.
      unfold Spec.zero_char in *.
      bool_rewrite.
      forward.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      forward.
      econstructor.
      forward.
      eapply exec_Sseq_2.
      econstructor.
      forward.
      forward.
      eapply addr_lt_to_sem_cmp_lt;
        eassumption.
       all: repeat (match goal with
                     | [|- context[bool_val]]=> simpl; bool_rewrite
                     | [|- context[Val.of_bool]] => simpl; bool_rewrite
                     end ||
                         forward ||
                         replace (negb (1 == 0)%int) with true
                    by (auto with ints)).
      rewrite H8.
      forward.
      discriminate.
    + (* Spec.is_digit i = true , return from the loop *)
      clear IHdist.
      unfold max_sign in *.
      unfold Spec.is_digit in *.
      destruct_andb_hyp.
      destruct (inp_value == upper_boundary) eqn : S.
      simpl in Heqb2.
      * inversion Spec; clear Spec.
        unfold int_to_int64 in *; unfold Spec.zero_char in *.
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
        eapply distance_to_sem_cmp_lt;
          eassumption.
       all: repeat (match goal with
                     | [|- context[bool_val]]=> simpl; bool_rewrite
                     | [|- context[Val.of_bool]] => simpl; bool_rewrite
                     end ||
                         forward ||
                         replace (negb (1 == 0)%int) with true
                      by (auto with ints)).
      * inversion Spec; clear Spec.
        repeat rewrite set_env_eq_ptree_set in *.
        repeat eexists.
        eapply exec_Sloop_stop1.
        econstructor. 
        econstructor.
        econstructor.
        repeat econstructor; try env_assumption.
        repeat econstructor; try env_assumption.
        try eassumption.
        econstructor.
        simpl.
        eapply distance_to_sem_cmp_lt;
          eassumption.
        all: repeat (match goal with
                     | [|- context[bool_val]]=> simpl; bool_rewrite
                     | [|- context[Val.of_bool]] => simpl; bool_rewrite
                     end ||
                         forward ||
                         replace (negb (1 == 0)%int) with true
                      by (auto with ints)).
       Qed.

Lemma asn_strtoimax_lim_loop_ASN_STRTOX_EXTRA_DATA_correct' :
  forall m ge e dist b ofs le str_b str_ofs fin_b 
    fin_ofs intp_b intp_ofs inp_value  m' val p s' s,
    
    le ! _str = Some (Vptr str_b str_ofs)  ->
    le ! _end = Some (Vptr fin_b fin_ofs) ->
    le ! _intp = Some (Vptr intp_b intp_ofs)  ->
    le ! _value = Some (Vlong inp_value) ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (sign_to_int s)) ->
    le ! _last_digit_max = Some (Vlong (max_sign s)) ->
                                     
    load_addr Mptr m (fin_b, fin_ofs) = Some (Vptr b ofs) ->
    (distance m (str_b, str_ofs) (b,ofs)) = Some dist ->
    
    asn_strtoimax_lim_loop m (str_b, str_ofs) (fin_b, fin_ofs) (intp_b, intp_ofs)
                           inp_value s (max_sign s) (Some dist) m =
    Some {| return_type := ASN_STRTOX_EXTRA_DATA;
            value := val;
            str_pointer := p;
            memory := Some m';
            sign := s' |}  ->

   exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m' 
              (Out_return (Some (Vint
                                   (asn_strtox_result_e_to_int
                                      ASN_STRTOX_EXTRA_DATA), tint))).
Proof.
  Admitted.


  Lemma asn_strtoimax_lim_correct :
  forall m ge e le str_b str_ofs fin_b fin_ofs intp_b intp_ofs m' res p s' val,
    
    le ! _str = Some (Vptr str_b str_ofs)  ->
    le ! _end = Some (Vptr fin_b fin_ofs) ->
    le ! _intp = Some (Vptr intp_b intp_ofs)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    asn_strtoimax_lim m (str_b, str_ofs) (fin_b, fin_ofs) (intp_b, intp_ofs)
    = Some {| return_type := res;
              value := val;
              str_pointer := p;
              memory := Some m';
              sign := s';
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
    + inversion Spec.
      rewrite H2 in *.
      destruct_orb_hyp.
      1 : (eapply exec_loop_minus).
      12: (eapply exec_loop_plus).
      all: repeat rewrite set_env_eq_ptree_set in *.
      all: repeat  eassumption.
        all: eapply asn_strtoimax_lim_loop_ASN_STRTOX_ERROR_RANGE_correct;
        repeat (env_assumption || econstructor);
     (switch_destruct i0);
     rewrite EQ in *; simpl in Heqo3; try econstructor;
       eapply dist_pred;
         try eassumption;
       eapply ptr_ge_is_valid in Heqo3;
       eassumption.
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
    + inversion Spec.
      rewrite H2 in *.
      destruct_orb_hyp.
      1 : (eapply exec_loop_minus).
      12: (eapply exec_loop_plus).
      all: repeat rewrite set_env_eq_ptree_set in *.
      all: repeat  eassumption.
        all: eapply asn_strtoimax_lim_loop_ASN_STRTOX_EXTRA_DATA_correct';
        repeat (env_assumption || econstructor);
     (switch_destruct i0);
     rewrite EQ in *; simpl in Heqo3; try econstructor;
       eapply dist_pred;
         try eassumption;
       eapply ptr_ge_is_valid in Heqo3;
       eassumption.
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
    unfold asn_strtoimax_lim in Spec.
    repeat break_match;
      unfold store_result in *;
      repeat break_match; try congruence.
     + inversion Spec.
       destruct_orb_hyp.
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
                   (PTree.set _t'10 (Vint Spec.minus_char)
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
                                  (PTree.set _sign (Vint (Int.repr 1)) le)))))))))))).
        repeat env_assumption.
        econstructor.
        all : try  repeat env_assumption; try econstructor.
        eapply dist_pred;
          try eassumption;
          eapply ptr_ge_is_valid in Heqo3;
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
        eapply ptr_ge_to_sem_cmp.
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
        eapply ptr_ge_to_sem_cmp.
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
        simpl.
        unfold mult_sign, sign_to_int.
        break_match; try eassumption.
        replace (Int64.repr (Int.signed (Int.repr 1))) with (1)%int64 
          by (auto with ints).
        replace (1 * i1) with i1.
        eassumption.
        rewrite Int64.mul_commut.
        rewrite Int64.mul_one.
        reflexivity.
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
             (PTree.set _t'10 (Vint Spec.plus_char)
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
                            (PTree.set _sign (Vint (Int.repr 1)) le)))))))))).
        repeat env_assumption.
        econstructor.
        all : try  repeat env_assumption; try econstructor.
        eapply dist_pred;
          try eassumption;
          eapply ptr_ge_is_valid in Heqo3;
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
        eapply ptr_ge_to_sem_cmp.
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
        eapply ptr_ge_to_sem_cmp.
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
         unfold mult_sign, sign_to_int.
         break_match; try eassumption.
         simpl.
        replace (Int64.repr (Int.signed (Int.repr 1))) with (1)%int64 
          by (auto with ints).
        replace (1 * i1) with i1.
        eassumption.
        rewrite Int64.mul_commut.
        rewrite Int64.mul_one.
        reflexivity.
     + pose proof (OK_None_ptr_contradiction
           (Some (n-1)%nat)
           ((str_b, str_ofs) ++) (fin_b, fin_ofs)
           (intp_b, intp_ofs) 0
           (char_to_sign i0) (max_sign (char_to_sign i0))
           m m' s').
      congruence. 
    + pose proof (OK_None_val_contradiction
           (Some (n-1)%nat)
           ((str_b, str_ofs) ++) (fin_b, fin_ofs)
           (intp_b, intp_ofs) 0
           (char_to_sign i0) (max_sign (char_to_sign i0))
           m m' s').
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
      simpl.
      unfold mult_sign, sign_to_int.
         break_match; try eassumption.
         simpl.
         inversion Spec.
         reflexivity.
         inversion Spec.
        replace (Int64.repr (Int.signed (Int.repr (1)))) with (1)%int64 
          by (auto with ints).
        replace (1 * i1) with i1.
        reflexivity.
        rewrite Int64.mul_commut.
        rewrite Int64.mul_one.
        reflexivity.
    + pose proof (OK_None_ptr_contradiction
           (Some (n)%nat)
           ((str_b, str_ofs)) (fin_b, fin_ofs)
           (intp_b, intp_ofs) 0
           Unsigned last_digit_max
           m m' s').
      congruence. 
    + pose proof (OK_None_val_contradiction
           (Some (n)%nat)
           ((str_b, str_ofs)) (fin_b, fin_ofs)
           (intp_b, intp_ofs) 0
           Unsigned last_digit_max
           m m' s').
      congruence.
Qed.


(* Correctness wrt abstract spec *)
 Lemma asn_strtoimax_lim_correct_R :
  forall m ge e le str_b str_ofs fin_b fin_ofs intp_b intp_ofs m' res,
    
    le ! _str = Some (Vptr str_b str_ofs)  ->
    le ! _end = Some (Vptr fin_b fin_ofs) ->
    le ! _intp = Some (Vptr intp_b intp_ofs)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    asn_strtoimax_lim_R m (str_b, str_ofs) (fin_b, fin_ofs) (intp_b, intp_ofs) m' res ->
    
    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim.(fn_body) t le' m'
                  (Out_return (Some ((Vint (asn_strtox_result_e_to_int res)), tint))).
   
    (* /\ (res = ASN_STRTOX_OK  ->
           Mem.loadv Mint64 m' (Vptr intp_b intp_ofs) = Some val -> 
           le'!_value = Some val) *)
   Admitted.
*)
