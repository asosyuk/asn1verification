From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import IntNotations asn_strtoimax_lim IntLemmas Tactics asn_strtoimax_lim_spec.
Require Import switch_statements.
Local Open Scope Int64Scope.

(* Lemmas for each `asn_strtox_result_e` case *)

(* ASN_STRTOX_ERROR_INVAL: str >= *end *)
Lemma asn_strtoimax_lim_ASN_STRTOX_ERROR_INVAL_correct :

  forall le str_b str_ofs fin_b fin_ofs intp_b intp_ofs m' val ip,
    
    le!_str = Some (Vptr str_b str_ofs)  ->
    le!_end = Some (Vptr fin_b fin_ofs) ->
    le!_intp = Some (Vptr intp_b intp_ofs)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    asn_strtoimax_lim (str_b, str_ofs) (fin_b,fin_ofs) (intp_b,intp_ofs) =
    Some
      {|
        return_type := ASN_STRTOX_ERROR_INVAL;
        value := val;
        intp := ip;
        memory := Some m' |} ->
    
    exists (t : trace) (le' : temp_env),
      exec_stmt ge e le m (fn_body f_asn_strtoimax_lim) t le' m'
                (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_INVAL), tint))).
Proof.
  intros until ip; intros Str End Intp UB Sign Spec.
  simpl in Spec.                       
  unfold asn_strtoimax_lim in Spec.
  assert (forall dist str fin inp value s last_digit,
             asn_strtoimax_lim_loop str fin inp value s last_digit dist m
             <> Some {|
                    return_type := ASN_STRTOX_ERROR_INVAL;
                    value := val;
                    intp := ip;
                    memory := Some m' |}) as Loop.
    { induction dist; intros; simpl.
      + break_match;
        congruence.
      + repeat break_match;
        repeat break_if;
        congruence. } 
  repeat break_match; try congruence.
  unfold addr_ge in *.
  replace (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_INVAL)
    with (Int.repr (-2)) by reflexivity.
  repeat eexists.
  exec_until_seq. 
  econstructor.
  exec_until_seq.
  econstructor.
  exec_until_seq.
  eapply exec_Sseq_2.
  forward.
  assert (option_map Val.of_bool (ptr_ge str_b b str_ofs i) = (option_map Val.of_bool (Some true))).
  { f_equal.
    eassumption. }
  eassumption.
  forward.
  inversion Spec; subst;
    repeat econstructor.
  congruence.
Qed.

(* SN_STRTOX_EXPECT_MORE: reading + or - and reaching *end *)
Lemma asn_strtoimax_lim_ASN_STRTOX_EXPECT_MORE_correct :

  forall le str_b str_ofs fin_b fin_ofs intp_b intp_ofs m' val ip,
    
    le!_str = Some (Vptr str_b str_ofs)  ->
    le!_end = Some (Vptr fin_b fin_ofs) ->
    le!_intp = Some (Vptr intp_b intp_ofs)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    asn_strtoimax_lim (str_b, str_ofs) (fin_b,fin_ofs) (intp_b,intp_ofs) =
    Some
      {|
        return_type := ASN_STRTOX_EXPECT_MORE;
        value := val;
        intp := ip;
        memory := Some m' |} ->
    
    exists (t : trace) (le' : temp_env),
      exec_stmt ge e le m (fn_body f_asn_strtoimax_lim) t le' m'
                (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_EXPECT_MORE), tint))).
Proof.
  replace (asn_strtox_result_e_to_int ASN_STRTOX_EXPECT_MORE)
    with (Int.repr (-1)) by reflexivity.
  intros until ip; intros Str End Intp UB Sign Spec.
  simpl in Spec.    
  assert (forall dist str fin intp v s last_digit  m',
             asn_strtoimax_lim_loop str fin intp v s last_digit dist m <>
             Some {| return_type := ASN_STRTOX_EXPECT_MORE;
                  value := val;
                  intp := ip;
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
      econstructor.
      repeat econstructor.
      all: repeat env_assumption.
      econstructor.
      eapply ptr_ge_to_sem_cmp_false; eassumption.
      repeat econstructor.
      repeat econstructor.
      eapply exec_Sseq_2.
      forward.
      replace (Out_return (Some (Vint (Int.repr (-1)), tint)))
        with (outcome_switch  (Out_return (Some (Vint (Int.repr (-1)), tint)))).
      forward.
      switch_destruct i0.
      econstructor.
      exec_until_seq.
      forward.
      eapply exec_Sseq_2.
      forward.
      eapply ptr_ge_to_sem_cmp_true; eassumption.
      all: forward; try discriminate.
    + repeat eexists.
      exec_until_seq.
      econstructor.
      repeat econstructor.
      econstructor.
      repeat econstructor.
      econstructor.
      repeat econstructor.
      all: repeat env_assumption.
      econstructor.
      eapply ptr_ge_to_sem_cmp_false; eassumption.
      repeat econstructor.
      repeat econstructor.
      apply exec_Sseq_2.
      forward.
      replace  (Out_return (Some (Vint (Int.repr (-1)), tint)))
        with (outcome_switch (Out_return (Some (Vint (Int.repr (-1)), tint)))).
      forward.
      switch_destruct i0.
      eapply exec_Sseq_2.
      forward.
      eapply ptr_ge_to_sem_cmp_true; eassumption.
      all: forward; try discriminate.
  - pose proof (Loop (distance (str_b, str_ofs) (b, i) - 1)%nat ((str_b, str_ofs) ++)
                     (fin_b, fin_ofs) (intp_b, intp_ofs) 0 (sign i0)
                     (max_sign (sign i0)) m'). congruence.
  - pose proof (Loop (distance (str_b, str_ofs) (b, i))%nat ((str_b, str_ofs))
                     (fin_b, fin_ofs) (intp_b, intp_ofs) 0  Unsigned
                     last_digit_max  m'). congruence.  
Qed.

(* Loop correctness cases *)
(* ASN_STRTOX_OK: conversion successfull *)
Lemma asn_strtoimax_lim_loop_ASN_STRTOX_OK_correct :   forall dist b ofs le str_b str_ofs fin_b fin_ofs intp_b intp_ofs inp_value  m' val s ip,
    
    le!_str = Some (Vptr str_b str_ofs)  ->
    le!_end = Some (Vptr fin_b fin_ofs) ->
    le!_intp = Some (Vptr intp_b intp_ofs)  ->
    le!_value = Some (Vlong inp_value) ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Sign s)) ->

    load_addr Mptr m (fin_b, fin_ofs) = Some (Vptr b ofs) ->

    (distance (str_b, str_ofs) (b,ofs)) = dist ->

    asn_strtoimax_lim_loop (str_b, str_ofs) (fin_b, fin_ofs) (intp_b, intp_ofs) inp_value s (max_sign s) dist m = Some {| return_type := ASN_STRTOX_OK;
              value := val;
              intp := ip;
              memory := Some m'; 
           |}  ->

    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m' Out_normal. 
 Proof.
(*   induction dist; intros until ip; intros Str End Value UB LastD Sign Load Dist Spec; unfold vptr in *; repeat break_let; subst; simpl in Spec.
   - (* Base case *)
     
     break_match.
     inversion Spec.
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
     unfold distance in *.
     simpl in Dist.
     simpl.
        
     assert ( (Ptrofs.unsigned i0) < (Ptrofs.unsigned ofs))%Z.
     { assert  ((Z.to_nat (Ptrofs.unsigned i0) < Z.to_nat (Ptrofs.unsigned ofs) )%nat) by
         lia.  
       unfold Ptrofs.unsigned in *.
       destruct ofs, i0; simpl in *.
       pose proof (Z2Nat.inj_lt intval0 intval) as Inj.
       destruct Inj.
       all: try lia. }
     assert (Ptrofs.unsigned i0 < Ptrofs.max_unsigned)%Z.
     {  assert (Ptrofs.unsigned ofs <= Ptrofs.max_unsigned)%Z.
         pose proof (Ptrofs.unsigned_range_2 ofs).
         all: try lia.
     }
     (* Dist *)
     assert (i0 <> Ptrofs.repr Ptrofs.max_unsigned) by admit.
     assert ((i0 + 1)%ptrofs <> Ptrofs.zero ) as S by admit.
     assert (non_zero_surj_ptrofs : forall i, Ptrofs.add i Ptrofs.one <> Ptrofs.zero -> Ptrofs.unsigned (Ptrofs.add i Ptrofs.one) = (Ptrofs.unsigned i + 1)%Z) by admit. (* there is a proof in IntLemmas *)
     pose proof (non_zero_surj_ptrofs i0 S) as Surj.
     rewrite Surj.
     (* follows from Dist *)    
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
     eassumption. *)
     Admitted.

 

Lemma asn_strtoimax_lim_loop_ASN_STRTOX_ERROR_RANGE_correct : forall dist b ofs le str_b str_ofs fin_b fin_ofs intp_b intp_ofs inp_value  m' val s ip,
    
    le!_str = Some (Vptr str_b str_ofs)  ->
    le!_end = Some (Vptr fin_b fin_ofs) ->
    le!_intp = Some (Vptr intp_b intp_ofs)  ->
    le!_value = Some (Vlong inp_value) ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Sign s)) ->

    load_addr Mptr m (fin_b, fin_ofs) = Some (Vptr b ofs) ->

    (distance (str_b, str_ofs) (b,ofs)) = dist ->

    asn_strtoimax_lim_loop (str_b, str_ofs) (fin_b, fin_ofs) (intp_b, intp_ofs) inp_value s (max_sign s) dist m = Some {| return_type := ASN_STRTOX_ERROR_RANGE;
              value := val;
              intp := ip;
              memory := Some m'; 
           |}  ->

    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m' (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_RANGE), tint))).         
Proof.
  replace (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_RANGE) with (Int.repr (-3)) by (reflexivity).
  induction dist; intros until ip; intros Str End Intp Value UB Sign Load Dist Spec;
    unfold vptr in *; repeat break_let;  simpl in Spec.
  - break_match. all: congruence.
  - repeat break_match.
    all: try congruence.
    (* 3 cases *)
     + remember ((_str <~ Vptr str_b (str_ofs + 1)%ptrofs)
              ((_value <~ Vlong (inp_value * int_to_int64 (Int.repr 10) + int_to_int64 (i - zero_char)%int))
              ((_d <~ Vint (i - zero_char)%int)
              ((_t'2 <~ Vint i) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))) as le''.
     pose proof (IHdist b ofs le'' str_b (str_ofs + 1)%ptrofs fin_b fin_ofs intp_b intp_ofs 
           (inp_value * Int64.repr 10 + int_to_int64 (i - zero_char)%int)  
           m' val s ip) as IH.
     clear IHdist.
     destruct IH as [t IH]; subst; try (repeat env_assumption || reflexivity).
     admit. (* follows from Dist *)    
     destruct IH as [le' IH].
     pose proof (switch_correct_continue i switch_body switch_default (PTree.set _t'1 (Vint i) (PTree.set _t'3 (Vptr b ofs) le))  str_b str_ofs) as SW.
      unfold switch in SW.
      assert (Mem.loadv Mint8signed m (Vptr str_b str_ofs) = Some (Vint i)) as M by (simpl; eassumption).
      assert (((_t'1 <~ Vint i) ((_t'3 <~ Vptr b ofs) le)) ! _str = Some (Vptr str_b str_ofs)) as L by (repeat env_assumption).
      pose proof (SW M L Heqb0  ((_value <~
      Vlong
        (inp_value * cast_int_long Signed (Int.repr 10) +
         cast_int_long Signed (i - zero_char)%int))
       ((_d <~ Vint (i - zero_char)%int)
          ((_t'2 <~ Vint i) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))).
     assert ((exists t : trace,
         exec_stmt ge e ((_t'1 <~ Vint i) ((_t'3 <~ Vptr b ofs) le)) m switch_body t
           ((_value <~
             Vlong
               (inp_value * cast_int_long Signed (Int.repr 10) +
                cast_int_long Signed (i - zero_char)%int))
              ((_d <~ Vint (i - zero_char)%int)
                 ((_t'2 <~ Vint i) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))
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
     assert (sem_cmp Clt (Vptr str_b str_ofs) (tptr tschar) (Vptr b ofs) (tptr tschar) m = Some Vtrue) by admit. (* follows from Dist *)
     eassumption.
     repeat econstructor.
     replace (negb (1 == 0)%int) with true by (auto with ints).
     econstructor.
     econstructor.
     repeat econstructor; try env_assumption; try eassumption.
     eassumption.
     econstructor.
     econstructor.
     repeat econstructor.
     repeat env_assumption.
     repeat econstructor.
     fold f_asn_strtoimax_lim_loop.
     replace  (str_ofs + Ptrofs.repr (sizeof ge tschar) * ptrofs_of_int Signed (Int.repr 1))%ptrofs with (str_ofs + 1)%ptrofs.
     replace (inp_value * cast_int_long Signed (Int.repr 10) +
            cast_int_long Signed (i - zero_char)%int) with  (inp_value * int_to_int64 (Int.repr 10) +
                                                              int_to_int64 (i - zero_char)%int).
     
     eapply IH.
     simpl.
     unfold int_to_int64.
     admit. (* signed and unsigned ? *)
     auto with ptrofs.
  (*   +

   remember ((_str <~ Vptr str_b (str_ofs + 1)%ptrofs)
              ((_value <~ Vlong (inp_value * int_to_int64 (Int.repr 10) + int_to_int64 (i - zero_char)%int))
              ((_d <~ Vint (i - zero_char)%int)
              ((_t'2 <~ Vint i) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))) as le''.
     pose proof (IHdist b ofs le'' (str_b, (str_ofs + 1)%ptrofs) (fin_b, i0) intp 
           (inp_value * Int64.repr 10 + int_to_int64 (i - zero_char)%int)  
           m' val s ip) as IH.
     clear IHdist.
     destruct IH as [t IH]; subst; try (repeat env_assumption || reflexivity).
     admit. (* follows from Dist *)    
     destruct IH as [le' IH].
      pose proof (switch_correct_continue i switch_body switch_default  (PTree.set _t'1 (Vint i) (PTree.set _t'3 (Vptr b ofs) le)) str_b str_ofs) as SW.
      unfold switch in SW.
      assert (Mem.loadv Mint8signed m (Vptr str_b str_ofs) = Some (Vint i)) as M by (simpl; eassumption).
      assert (((_t'1 <~ Vint i) ((_t'3 <~ Vptr b ofs) le)) ! _str = Some (Vptr str_b str_ofs)) as L by (repeat env_assumption).
      pose proof (SW M L Heqb3  ((_value <~
      Vlong
        (inp_value * cast_int_long Signed (Int.repr 10) +
         cast_int_long Signed (i - zero_char)%int))
       ((_d <~ Vint (i - zero_char)%int)
          ((_t'2 <~ Vint i) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))).
     assert ((exists t : trace,
         exec_stmt ge e ((_t'1 <~ Vint i) ((_t'3 <~ Vptr b ofs) le)) m switch_body t
           ((_value <~
             Vlong
               (inp_value * cast_int_long Signed (Int.repr 10) +
                cast_int_long Signed (i - zero_char)%int))
              ((_d <~ Vint (i - zero_char)%int)
                 ((_t'2 <~ Vint i) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))
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
     assert (sem_cmp Clt (Vptr str_b str_ofs) (tptr tschar) (Vptr b ofs) (tptr tschar) m = Some Vtrue) by admit. (* follows from Dist *)
     eassumption.
     repeat econstructor.
     replace (negb (1 == 0)%int) with true by (auto with ints).
     econstructor.
     econstructor.
     repeat econstructor; try env_assumption; try eassumption.
     simpl.
     assert (Mem.load Mint8signed m str_b (Ptrofs.unsigned str_ofs) = Some (Vint i)) by  (simpl; eassumption). 
     eassumption.
     econstructor.
     repeat econstructor.
     repeat env_assumption.
     repeat econstructor.
     fold f_asn_strtoimax_lim_loop.
     replace  (i0 + Ptrofs.repr (sizeof ge tschar) * ptrofs_of_int Signed (Int.repr 1))%ptrofs with (i0 + 1)%ptrofs.
     replace (inp_value * cast_int_long Signed (Int.repr 10) +
            cast_int_long Signed (i - zero_char)%int) with  (inp_value * int_to_int64 (Int.repr 10) +
                                                              int_to_int64 (i - zero_char)%int).
     
     eapply IH.
     simpl.
     unfold int_to_int64.
     admit. (* signed and unsigned ? *)
     auto with ptrofs.

    + inversion Spec.
      unfold  Mem.loadv in *.
      assert (((_t'1 <~ Vint i) ((_t'3 <~ Vptr b ofs) le)) ! _str = Some (Vptr str_b str_ofs)) as LE by (repeat env_assumption).
      assert (Mem.loadv Mint8signed asn_strtoimax_lim_spec.m (Vptr str_b str_ofs) = Some (Vint i)) as M by (simpl; eassumption).
      assert (((_t'1 <~ Vint i) ((_t'3 <~ Vptr b ofs) le)) ! _str = Some (Vptr str_b str_ofs)) as L by (repeat env_assumption).
      pose proof (switch_correct_return i switch_body switch_default  (PTree.set _t'1 (Vint i) (PTree.set _t'3 (Vptr b ofs) le))  str_b str_ofs ((Some (Vint (Int.repr (-3)), tint)))) as SW.
     
     pose proof (SW M L Heqb3  ((_value <~
      Vlong
        (inp_value * cast_int_long Signed (Int.repr 10) +
         cast_int_long Signed (i - zero_char)%int))
       ((_d <~ Vint (i - zero_char)%int)
          ((_t'2 <~ Vint i) ((_t'1 <~ Vint i) ((_t'3 <~ Vptr b ofs) le))))) m).
     
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
        assert (sem_cmp Clt (Vptr str_b str_ofs) (tptr tschar) (Vptr b ofs) (tptr tschar) asn_strtoimax_lim_spec.m = Some Vtrue) by admit. eassumption.
        econstructor.
        econstructor.
        econstructor.
        repeat econstructor.
        1-2: env_assumption.
        env_assumption.
        replace m' with m by auto.
        unfold switch in H.
        eassumption.
        econstructor. *)
Admitted.


Lemma spec_to_valid_pointers :
  forall dist b ofs str_b str_ofs fin_b fin_ofs intp_b intp_ofs m' val  ip,
    asn_strtoimax_lim (str_b, str_ofs) (fin_b, fin_ofs) (intp_b, intp_ofs) =
    
     Some {| return_type := ASN_STRTOX_EXTRA_DATA;
            value := val;
            intp := ip;
            memory := Some m';|}

    ->
    load_addr Mptr m (fin_b, fin_ofs) = Some (Vptr b ofs) ->
    (distance (str_b, str_ofs) (b,ofs)) = dist ->
    (forall i, (i < dist)%nat ->
               Mem.valid_pointer m str_b
                                 (Ptrofs.unsigned str_ofs + (Z.of_nat i)) = true).
Proof.
  Admitted.  

Lemma asn_strtoimax_lim_loop_ASN_STRTOX_EXTRA_DATA_correct :
  forall dist b ofs le str_b str_ofs fin_b fin_ofs intp_b intp_ofs inp_value  m' val s ip,
    
    le!_str = Some (Vptr str_b str_ofs)  ->
    le!_end = Some (Vptr fin_b fin_ofs) ->
    le!_intp = Some (Vptr intp_b intp_ofs)  ->
    le!_value = Some (Vlong inp_value) ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Sign s)) ->
    le ! _last_digit_max = Some (Vlong (max_sign s)) ->
                                     
    load_addr Mptr m (fin_b, fin_ofs) = Some (Vptr b ofs) ->
    (distance (str_b, str_ofs) (b,ofs)) = dist ->
    (forall i, (i < dist)%nat ->
          Mem.valid_pointer m str_b (Ptrofs.unsigned str_ofs + (Z.of_nat i)) = true) ->
    
    asn_strtoimax_lim_loop (str_b, str_ofs) (fin_b, fin_ofs) (intp_b, intp_ofs)
                           inp_value s (max_sign s) dist m =
    Some {| return_type := ASN_STRTOX_EXTRA_DATA;
            value := val;
            intp := ip;
            memory := Some m';|}  ->

    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m' (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_EXTRA_DATA), tint))). 
Proof.
  replace (asn_strtox_result_e_to_int ASN_STRTOX_EXTRA_DATA)
    with Int.one by (reflexivity).
  induction dist; intros until ip;
    intros Str End Intp Value UB Sign LastD Load Dist Valid Spec;
    simpl in Spec. 
  - break_match. all: congruence.
  - repeat break_match; try congruence.
    (* 3 cases: do one loop and then apply IH *)
    + remember ((_str <~ Vptr str_b (str_ofs + 1)%ptrofs)
                  ((_value <~ Vlong (inp_value * int_to_int64 (Int.repr 10)
                                     + int_to_int64 (i - zero_char)%int))
                    ((_d <~ Vint (i - zero_char)%int)
                       ((_t'2 <~ Vint i)
                          ((_t'1 <~ Vint i)
                              ((_t'3 <~ Vptr b ofs) le)))))) as le''.
      pose proof (IHdist b ofs le'' str_b (str_ofs + 1)%ptrofs
                         fin_b fin_ofs intp_b intp_ofs
                         (inp_value * Int64.repr 10 + int_to_int64 (i - zero_char)%int) m' val s ip) as IH.    clear IHdist.
      destruct IH as [t IH]; subst; try (repeat env_assumption || reflexivity).
      { eapply dist_succ; eassumption. }
      { intros j Lj.
        assert  (j + 1 < S dist)%nat as Lj1 by omega.
        pose proof (Valid (j + 1)%nat Lj1).
        (* same proof as for dist_succ *)
        admit. }
      destruct IH as [le' IH]. 
      pose proof (switch_correct_continue i switch_body switch_default
                 (PTree.set _t'1 (Vint i) (PTree.set _t'3 (Vptr b ofs) le))
                                          str_b str_ofs) as SW.
      unfold switch in SW.
      assert (Mem.loadv Mint8signed m (Vptr str_b str_ofs) = Some (Vint i))
        as M by eassumption.
      assert (((_t'1 <~ Vint i) ((_t'3 <~ Vptr b ofs) le)) ! _str
              = Some (Vptr str_b str_ofs)) as L
          by (repeat env_assumption).
      remember ((_value <~ Vlong (inp_value * cast_int_long Signed (Int.repr 10) +
         cast_int_long Signed (i - zero_char)%int))
                  ((_d <~ Vint (i - zero_char)%int)
                   ((_t'2 <~ Vint i)
                      ((_t'1 <~ Vint i)
                         ((_t'3 <~ Vptr b ofs) le)))))
                as le''_eq.
      pose proof (SW M L Heqb0  le''_eq).
      (* move this to a lemma *)
      assert ((exists t : trace,
                  exec_stmt ge e ((_t'1 <~ Vint i) ((_t'3 <~ Vptr b ofs) le))
                            m switch_body t le''_eq m Out_continue)) as F.
      { rewrite Heqle''_eq. 
        repeat eexists.
        forward. simpl.
        bool_rewrite. forward.
        replace (negb (1 == 0)%int) with true by (auto with ints).
        forward.
           }
      destruct (H F).
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
      assert (sem_cmp Clt (Vptr str_b str_ofs) (tptr tschar)
                      (Vptr b ofs) (tptr tschar) m = Some Vtrue).
      { (* we have  Dist : distance (str_b, str_ofs) (b, ofs) = S dist *)
        cbn.
        unfold cmp_ptr.
        break_if.
        cbn.
        repeat break_match; simpl; try congruence. admit.
        simpl.
        f_equal.
        pose proof (dist_to_lt _ _ _ _ _ Dist).
        unfold Ptrofs.ltu.
        break_if.
        reflexivity.
        nia.
        (* str_b, str_ofs or b, ofs is weak invalid *)
        fold Mem.weak_valid_pointer in *.
        admit.
        (* point to different blocks, incomparable, but valid *)
        admit. (* same *)
        admit.
        all: admit.
      }
      
      (* follows from Dist *)
      eassumption.
      repeat econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption; try eassumption.
      eassumption.
      econstructor.
      forward.
      rewrite Heqle''_eq; repeat env_assumption.
      forward.
      fold f_asn_strtoimax_lim_loop.
      rewrite Heqle''_eq.
      replace (str_ofs + Ptrofs.repr (sizeof ge tschar) *
                         ptrofs_of_int Signed (Int.repr 1))%ptrofs
        with (str_ofs + 1)%ptrofs by auto with ptrofs.
      replace (inp_value * cast_int_long Signed (Int.repr 10) +
               cast_int_long Signed (i - zero_char)%int) with
          (inp_value * int_to_int64 (Int.repr 10) +
           int_to_int64 (i - zero_char)%int).
      eapply IH.
      simpl.
      admit.
    + remember ((_str <~ Vptr str_b (str_ofs + 1)%ptrofs)
                  ((_value <~ Vlong (inp_value * int_to_int64 (Int.repr 10)
                                     + int_to_int64 (i - zero_char)%int))
                    ((_d <~ Vint (i - zero_char)%int)
                       ((_t'2 <~ Vint i)
                          ((_t'1 <~ Vint i)
                              ((_t'3 <~ Vptr b ofs) le)))))) as le''.
      pose proof (IHdist b ofs le'' str_b (str_ofs + 1)%ptrofs
                         fin_b fin_ofs intp_b intp_ofs
                         (inp_value * Int64.repr 10 + int_to_int64 (i - zero_char)%int) m' val s ip) as IH.    clear IHdist.
      destruct IH as [t IH]; subst; try (repeat env_assumption || reflexivity).
      eapply dist_succ; eassumption.
      admit.
      destruct IH as [le' IH]. 
      pose proof (switch_correct_continue i switch_body switch_default
                 (PTree.set _t'1 (Vint i) (PTree.set _t'3 (Vptr b ofs) le))
                                          str_b str_ofs) as SW.
      unfold switch in SW.
      assert (Mem.loadv Mint8signed m (Vptr str_b str_ofs) = Some (Vint i))
        as M by eassumption.
      assert (((_t'1 <~ Vint i) ((_t'3 <~ Vptr b ofs) le)) ! _str
              = Some (Vptr str_b str_ofs)) as L
          by (repeat env_assumption).
      remember ((_value <~ Vlong (inp_value * cast_int_long Signed (Int.repr 10) +
         cast_int_long Signed (i - zero_char)%int))
                  ((_d <~ Vint (i - zero_char)%int)
                   ((_t'2 <~ Vint i)
                      ((_t'1 <~ Vint i)
                         ((_t'3 <~ Vptr b ofs) le)))))
                as le''_eq.
      pose proof (SW M L Heqb0  le''_eq).
      (* move this to a lemma *)
      assert ((exists t : trace,
                  exec_stmt ge e ((_t'1 <~ Vint i) ((_t'3 <~ Vptr b ofs) le))
                            m switch_body t le''_eq  m Out_continue)) as F.
      {  rewrite Heqle''_eq. 
         repeat eexists.
         destruct_andb_hyp.
         forward. simpl.
         bool_rewrite. forward.
         forward. simpl.
         bool_rewrite. forward.
         replace (negb (1 == 0)%int) with true by (auto with ints).
         forward. simpl.
         unfold int_to_int64 in *. rewrite Int.signed_eq_unsigned.
         bool_rewrite; econstructor.
         admit. (* int signed and unsigned *)
         break_ife_true.
         forward.
         simpl.
         destruct s; simpl.
         econstructor.
         auto with ints.
         admit.
         forward.
         (* need to deal with sign *)
         all: admit.
      }
      destruct (H F).
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
      assert (sem_cmp Clt (Vptr str_b str_ofs) (tptr tschar) (Vptr b ofs) (tptr tschar) m = Some Vtrue) by admit. (* follows from Dist *)
      eassumption.
      repeat econstructor.
      replace (negb (1 == 0)%int) with true by (auto with ints).
      econstructor.
      econstructor.
      repeat econstructor; try env_assumption; try eassumption.
      eassumption.
      econstructor.
      forward.
      rewrite Heqle''_eq; repeat env_assumption.
      forward.
      fold f_asn_strtoimax_lim_loop.
      rewrite Heqle''_eq.
      replace (str_ofs + Ptrofs.repr (sizeof ge tschar) *
                         ptrofs_of_int Signed (Int.repr 1))%ptrofs
        with (str_ofs + 1)%ptrofs by auto with ptrofs.
      replace (inp_value * cast_int_long Signed (Int.repr 10) +
               cast_int_long Signed (i - zero_char)%int) with
          (inp_value * int_to_int64 (Int.repr 10) +
           int_to_int64 (i - zero_char)%int).
      eapply IH.
      simpl.
      admit.
    + inversion Spec; clear Spec.
      assert (((_t'1 <~ Vint i) ((_t'3 <~ Vptr b ofs) le)) ! _str
              = Some (Vptr str_b str_ofs)) as LE by (repeat env_assumption).
      destruct (switch_default_correct i switch_body switch_default
                  (PTree.set _t'1 (Vint i) (PTree.set _t'3 (Vptr b ofs) le))
                   str_b str_ofs  (Some (Vint 1%int, tint))
                   Heqo LE Heqb0 ((_t'1 <~ Vint i) ((_t'3 <~ Vptr b ofs) le)) m').
      ++ forward.
         simpl.
         destruct s; simpl in H2; simpl.
      * replace (Int64.repr (Int.signed (Int.neg (Int.repr 1))) * inp_value)
          with  (Int64.neg inp_value) by admit.
        eassumption.
      * replace  (Int64.repr (Int.signed (Int.repr 1))) with (Int64.repr 1)
          by auto with ints.
        replace (Int64.repr 1 * inp_value) with (inp_value) by admit.
        eassumption.
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
        assert (sem_cmp Clt (Vptr str_b str_ofs) (tptr tschar) (Vptr b ofs) (tptr tschar) asn_strtoimax_lim_spec.m = Some Vtrue) by admit; eassumption.
        forward.
        econstructor.
        econstructor.
        repeat econstructor.
        all: repeat  (eassumption || env_assumption).
        econstructor.
Admitted.

Lemma asn_strtoimax_lim_correct :
  forall le str_b str_ofs fin_b fin_ofs intp_b intp_ofs m' res val ip,
    
    le!_str = Some (Vptr str_b str_ofs)  ->
    le!_end = Some (Vptr fin_b fin_ofs) ->
    le!_intp = Some (Vptr intp_b intp_ofs)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->

    asn_strtoimax_lim (str_b, str_ofs) (fin_b,fin_ofs) (intp_b,intp_ofs)
    = Some {| return_type := res;
              value := val;
              intp := ip;
              memory := Some m'; 
           |} -> 
    exists t le', exec_stmt ge e le m f_asn_strtoimax_lim.(fn_body) t le' m'
                 (Out_return (Some ((Vint (asn_strtox_result_e_to_int res)), tint))).
Proof.
  induction res.
  - (* ASN_STRTOX_ERROR_RANGE *)
    intros until ip; intros Str End Intp UB Sign Spec.
    unfold asn_strtoimax_lim in Spec.
    repeat break_match.
    all: try congruence.
    assert ((distance (str_b, str_ofs) (b, i) - 1)%nat = 
    (distance (str_b, (str_ofs + 1)%ptrofs) (b, i))).
    {
      remember (distance (str_b, str_ofs) (b, i) - 1)%nat as
          dist.
      symmetry.
      apply dist_succ.
      rewrite Heqdist.
      unfold distance; simpl.
      rewrite <-Nat.add_1_l.
      repeat replace 1%nat with (Z.to_nat 1)%Z by reflexivity.
      repeat rewrite <-Z2Nat.inj_sub.
      rewrite <-Z2Nat.inj_add.
      f_equal.
      all: try lia.
      2: apply Ptrofs.unsigned_range.
    }
    replace (distance (str_b, str_ofs) (b, i) - 1)%nat
      with (distance (str_b, (str_ofs + 1)%ptrofs) (b, i)) in Spec.
    + destruct_orb_hyp.
      1 : (eapply exec_loop_minus).
      11: (eapply exec_loop_plus).
      all:
        repeat  eassumption;
        eapply asn_strtoimax_lim_loop_ASN_STRTOX_ERROR_RANGE_correct;
        repeat (env_assumption || econstructor);
        switch_destruct i0;
        rewrite EQ in *; simpl in Spec;
          reflexivity.
    + destruct_orb_hyp.
      eapply exec_loop_none; try eassumption.
      eapply asn_strtoimax_lim_loop_ASN_STRTOX_ERROR_RANGE_correct;
        repeat (env_assumption || econstructor).
      instantiate (1 := Unsigned); simpl.
      all: try (econstructor || eassumption).
  - (* ASN_STRTOX_ERROR_INVAL *)
    eapply asn_strtoimax_lim_ASN_STRTOX_ERROR_INVAL_correct.     
  - (* ASN_STRTOX_EXPECT_MORE *)
    eapply asn_strtoimax_lim_ASN_STRTOX_EXPECT_MORE_correct. 
  - (*  ASN_STRTOX_EXTRA_DATA *)
    intros until ip; intros Str End Intp UB Sign Spec.
    unfold asn_strtoimax_lim in Spec.
    repeat break_match.
    all: try congruence.
    replace (distance (str_b, str_ofs) (b, i) - 1)%nat
      with (distance (str_b, (str_ofs + 1)%ptrofs) (b, i)) in Spec by admit.
    + destruct_orb_hyp.
      1 : (eapply exec_loop_minus).
      11: (eapply exec_loop_plus).
      all:
        repeat  eassumption;
        eapply asn_strtoimax_lim_loop_ASN_STRTOX_EXTRA_DATA_correct;
        repeat (env_assumption || econstructor);
        switch_destruct i0;
        rewrite EQ in *; simpl in Spec;
          try reflexivity.
      1-2: admit.      
    + destruct_orb_hyp.
      eapply exec_loop_none; try eassumption.
      eapply asn_strtoimax_lim_loop_ASN_STRTOX_EXTRA_DATA_correct;
        repeat (env_assumption || econstructor).
      instantiate (1 := Unsigned); simpl.
      all: try (econstructor || eassumption).
      1-2: admit.     
  - (* ASN_STRTOX_OK *)
    intros until ip; intros Str End Intp UB Sign Spec.
    unfold asn_strtoimax_lim in Spec.
    repeat break_match.
    all: try congruence.
    replace (distance (str_b, str_ofs) (b, i) - 1)%nat
      with (distance (str_b, (str_ofs + 1)%ptrofs) (b, i)) in Spec by admit.
    + destruct_orb_hyp.
      admit.
Admitted.








