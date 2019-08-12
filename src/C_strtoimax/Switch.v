Require Import Core.Core Core.Tactics Core.PtrLemmas.
Require Import C_strtoimax.AST C_strtoimax.Spec.
Require Import StructTact.StructTactics.

Import ListNotations.

Local Open Scope Int64Scope.

(* Dealing with the switch statement *)
Definition switch s1 s2 :=
  (Sswitch (Ederef (Etempvar _str (tptr tschar)) tschar)
    (LScons (Some 48)
      Sskip
      (LScons (Some 49)
        Sskip
        (LScons (Some 50)
          Sskip
          (LScons (Some 51) Sskip
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
                       s1 (LScons None
                          s2
                          LSnil)))))))))))).

(* If reading i a digit then we enter the correct branch and continue *)
Lemma switch_correct_continue : forall m ge e i s1 s2 le b ofs,
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

(* If reading i a digit then we enter the correct branch and continue *)
Lemma switch_default_correct : forall m ge e i s1 s2 le b ofs out,
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

Definition switch_1 := (Sswitch (Ederef (Etempvar _str (tptr tschar)) tschar)
              (LScons (Some 45)
                (Ssequence
                  (Sset _last_digit_max
                    (Ebinop Oadd (Etempvar _last_digit_max tlong)
                      (Econst_int (Int.repr 1) tint) tlong))
                  (Sset _sign
                    (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
                (LScons (Some 43)
                  (Ssequence
                    (Sset _str
                      (Ebinop Oadd (Etempvar _str (tptr tschar))
                        (Econst_int (Int.repr 1) tint) (tptr tschar)))
                    (Ssequence
                      (Sset _t'5
                        (Ederef (Etempvar _end (tptr (tptr tschar)))
                          (tptr tschar)))
                      (Sifthenelse (Ebinop Oge (Etempvar _str (tptr tschar))
                                     (Etempvar _t'5 (tptr tschar)) tint)
                        (Ssequence
                          (Sassign
                            (Ederef (Etempvar _end (tptr (tptr tschar)))
                              (tptr tschar)) (Etempvar _str (tptr tschar)))
                          (Sreturn (Some (Econst_int (Int.repr (-1)) tint))))
                        Sskip)))
                  LSnil))).

Lemma switch_default_correct_1 : forall m ge e i le b ofs,
    Mem.loadv Mint8signed m (Vptr b ofs) = Some (Vint i) ->
    le ! _str = Some (Vptr b ofs) ->
    (i == minus_char)%int = false ->
    (i == plus_char)%int = false ->
                (exists t, exec_stmt ge e le m switch_1 t le m Out_normal).
Proof.
  unfold plus_char, minus_char.
  intros until ofs; intros Mem Str Min Plus.
  repeat eexists.
  replace (Out_normal) with (outcome_switch (Out_normal)) by (reflexivity).
  econstructor.
  repeat econstructor; try eassumption.
  econstructor.
  repeat (switch_destruct i).
  try (rewrite Int.unsigned_repr in *).
  unfold select_switch.
  unfold select_switch_default.
  unfold select_switch_case.
  repeat break_if.
  all: try congruence.
  econstructor.
  all: cbn;  try lia.
Qed.     

Lemma switch_correct_return : forall m ge e i s1 s2 le b ofs out,
    Mem.loadv Mint8signed m (Vptr b ofs) = Some (Vint i) ->
    le ! _str = Some (Vptr b ofs) ->
    is_digit i = true ->
    forall le' m', (exists t, exec_stmt ge e le m s1 t le' m' (Out_return out)) ->
    (exists t, exec_stmt ge e le m (switch s1 s2) t le' m' (Out_return out)).
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

Lemma exec_loop_minus : forall m ge e le b ofs str_b str_ofs fin_b fin_ofs intp_b intp_ofs i out s1 s2,
    le!_str = Some (Vptr str_b str_ofs)  ->
    le!_end = Some (Vptr fin_b fin_ofs) ->
    le!_intp = Some (Vptr intp_b intp_ofs)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->
    
    load_addr Mptr m (fin_b, fin_ofs) = Some (Vptr b ofs) ->
    addr_ge m (str_b, str_ofs) (b, ofs) = Some false ->
    load_addr Mint8signed m (str_b, str_ofs) = Some (Vint i) ->
    
    (i == minus_char)%int = true ->
    
    forall m', (exists t le', exec_stmt ge e
                              (in le set [
                                   _value <~ Vlong 0%int64 ;
                                   _t'5 <~ Vptr b ofs ;
                                   _str <~ Vptr str_b (str_ofs + 1)%ptrofs ;
                                   _sign <~ Vint (Int.neg (Int.repr 1)) ;
                                   _last_digit_max <~ Vlong last_digit_max_minus ;
                                   _t'4 <~ Vint minus_char ;
                                   _t'6 <~ Vptr b ofs ;
                                   _last_digit_max <~ Vlong last_digit_max ;
                                   _upper_boundary <~ Vlong upper_boundary ;
                                   _sign <~ Vint (Int.repr 1)])
                              m s1 t le' m' (Out_return out)) ->
        exists t le', exec_stmt ge e le m (pre_loop s1 s2) t le' m' (Out_return out).
Proof.
  intros until s2.
  intros Str End Intp UB Sign LA AG LA' Char m' S1.
  break_exists.
  unfold pre_loop.
  repeat eexists.
  econstructor.
  repeat econstructor.
  econstructor.
  repeat econstructor.
  econstructor.
  repeat econstructor.
  econstructor.
  repeat econstructor.
  Tactics.forward.
  unfold load_addr in *.
  eassumption.
  repeat env_assumption.
  env_assumption.
  econstructor.
  repeat econstructor.
 assert (sem_binary_operation ge Oge (Vptr str_b str_ofs) (typeof (Etempvar _str (tptr tschar)))
                              (Vptr b ofs) (typeof (Etempvar _t'6 (tptr tschar))) m = Some Vfalse)  by admit; eassumption.
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
 replace i with (minus_char) by admit.
 econstructor.
 repeat econstructor.
 repeat env_assumption.
 econstructor.
 repeat econstructor.
 Tactics.forward.
 simpl.
 assert (sem_cmp Cge (Vptr str_b (str_ofs + Ptrofs.repr 1 * Ptrofs.of_ints (Int.repr 1))%ptrofs)
                 (tptr tschar) (Vptr b ofs) (tptr tschar) m = Some Vfalse) by admit; eassumption.
 Tactics.forward.
 econstructor.
 reflexivity.
 apply exec_Sseq_2.
 econstructor.
 repeat econstructor.
 eapply H.
 discriminate.
Admitted.

Lemma exec_loop_plus : forall m ge e le b ofs str_b str_ofs fin_b fin_ofs intp_b intp_ofs i out s1 s2,
    le!_str = Some (Vptr str_b str_ofs)  ->
    le!_end = Some (Vptr fin_b fin_ofs) ->
    le!_intp = Some (Vptr intp_b intp_ofs)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->
    
    load_addr Mptr m (fin_b, fin_ofs) = Some (Vptr b ofs) ->
    addr_ge m (str_b, str_ofs) (b, ofs) = Some false ->
    load_addr Mint8signed m (str_b, str_ofs) = Some (Vint i) ->
    
    (i == plus_char)%int = true ->
    
    forall m', (exists t le', exec_stmt ge e
                              (in le set [
                              _value <~ Vlong 0%int64 ;
                              _t'5 <~ Vptr b ofs ;
                              _str <~ Vptr str_b (str_ofs + 1)%ptrofs ;
                              _t'4 <~ Vint plus_char ;
                              _t'6 <~ Vptr b ofs ;
                              _last_digit_max <~ Vlong last_digit_max ;
                              _upper_boundary <~ Vlong upper_boundary ; 
                              _sign <~ Vint (Int.repr 1)])
                              (*(_value <~ Vlong 0%int64)
                                 ((_t'5 <~ Vptr b ofs)
                                    ((_str <~ Vptr str_b (str_ofs + 1)%ptrofs)
                                       ((_t'4 <~ Vint plus_char)
                                          ((_t'6 <~ Vptr b ofs)
                                             ((_last_digit_max <~ Vlong last_digit_max)
                                                ((_upper_boundary <~ Vlong upper_boundary)
                                                   ((_sign <~ Vint (Int.repr 1)) le)))))))*)
                              m s1 t le' m' (Out_return out)) ->
          exists t le', exec_stmt ge e le m (pre_loop s1 s2) t le' m' (Out_return out).
Proof.
  intros until s2.
  intros Str End Intp UB Sign LA AG LA' Char m' S1.
  break_exists.
  unfold pre_loop.
  repeat eexists.
  econstructor.
  repeat econstructor.
  econstructor.
  repeat econstructor.
  econstructor.
  repeat econstructor.
  econstructor.
  repeat econstructor.
  Tactics.forward.
  unfold load_addr in *.
  eassumption.
  repeat env_assumption.
  env_assumption.
  econstructor.
  repeat econstructor.
  assert (sem_binary_operation ge Oge (Vptr str_b str_ofs) (typeof (Etempvar _str (tptr tschar)))
                               (Vptr b ofs) (typeof (Etempvar _t'6 (tptr tschar))) m = Some Vfalse) by admit; eassumption.
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
  replace i with (plus_char) by admit.
  econstructor.
  repeat econstructor.
  repeat env_assumption.
  econstructor.
  repeat econstructor.
  Tactics.forward.
  simpl.
  assert (sem_cmp Cge (Vptr str_b (str_ofs + Ptrofs.repr 1 * Ptrofs.of_ints (Int.repr 1))%ptrofs)
                  (tptr tschar) (Vptr b ofs) (tptr tschar) m = Some Vfalse) by admit; eassumption.
  Tactics.forward.
  Tactics.forward.
  simpl.
  assert (sem_cmp Cge (Vptr str_b (str_ofs + Ptrofs.repr 1 * Ptrofs.of_ints (Int.repr 1))%ptrofs)
                  (tptr tschar) (Vptr b ofs) (tptr tschar) m = Some Vfalse) by admit; eassumption.
  repeat econstructor.
  econstructor.
  econstructor.
  reflexivity.
  apply exec_Sseq_2.
  econstructor.
  repeat econstructor.
  eapply H.
  discriminate.
Admitted.

Lemma exec_loop_none : forall m ge e le b ofs str_b str_ofs fin_b fin_ofs intp_b intp_ofs i out s1 s2,
    le!_str = Some (Vptr str_b str_ofs)  ->
    le!_end = Some (Vptr fin_b fin_ofs) ->
    le!_intp = Some (Vptr intp_b intp_ofs)  ->
    le ! _upper_boundary = Some (Vlong upper_boundary) ->
    le ! _sign = Some (Vint (Int.repr 1)) ->
    
    load_addr Mptr m (fin_b, fin_ofs) = Some (Vptr b ofs) ->
    addr_ge m (str_b, str_ofs) (b, ofs) = Some false ->
    load_addr Mint8signed m (str_b, str_ofs) = Some (Vint i) ->
    
    (i == plus_char)%int = false ->
    (i == minus_char)%int = false ->
    
    forall le' m', (exists t, exec_stmt ge e
                              (in le set [
                                _value <~ Vlong (cast_int_long Signed (Int.repr 0)) ;
                                _t'4 <~ Vint i ;
                                _t'6 <~ Vptr b ofs ;
                                _last_digit_max <~ Vlong (Int64.modu 
                                                         (Int64.not (cast_int_long Signed (Int.repr 0)) >> 
                                                         Int64.repr (Int.unsigned (Int.repr 1))) 
                                                         (cast_int_long Signed (Int.repr 10))) ;
                                _upper_boundary <~ Vlong (Int64.divu
                                                         (Int64.not (cast_int_long Signed (Int.repr 0)) >> 
                                                         Int64.repr (Int.unsigned (Int.repr 1))) 
                                                         (cast_int_long Signed (Int.repr 10))) ;
                                _sign <~ Vint (Int.repr 1) ])
                              m s1 t le' m' (Out_return out)) ->
                   
          exists t le', exec_stmt ge e le m (pre_loop s1 s2) t le' m' (Out_return out).
Proof.
  intros until s2.
  intros Str End Intp UB Sign LA AG LA' CharP CharM  m' S1.
  destruct S1.
  unfold pre_loop.
  destruct (switch_default_correct_1 m ge e i (in le set [
                                                  _t'4 <~ Vint i ;
                                                  _t'6 <~ Vptr b ofs ;
                                                  _last_digit_max <~ Vlong
                                                                  (Int64.modu
                                                                     (Int64.not (cast_int_long Signed (Int.repr 0)) >>
                                                                              Int64.repr (Int.unsigned (Int.repr 1)))
                                                                     (cast_int_long Signed (Int.repr 10))) ;
                                                  _upper_boundary <~ Vlong
                                                                  (Int64.divu
                                                                     (Int64.not (cast_int_long Signed (Int.repr 0)) >>
                                                                              Int64.repr (Int.unsigned (Int.repr 1))) 
                                                                     (cast_int_long Signed (Int.repr 10))) ;
                                                  _sign <~ Vint (Int.repr 1)])
                                     str_b str_ofs).
  all: try eassumption; env_assumption.
  repeat rewrite set_env_eq_ptree_set.
  
  repeat env_assumption.
  repeat rewrite set_env_eq_ptree_set in H.
  destruct H.
  repeat eexists.
  econstructor.
  repeat econstructor.
  econstructor.
  repeat econstructor.
  econstructor.
  repeat econstructor.
  econstructor.
  repeat econstructor.
  Tactics.forward.
  unfold load_addr in *.
  eassumption.
  repeat env_assumption.
  env_assumption.
  econstructor.
  repeat econstructor.
  assert (sem_binary_operation ge Oge (Vptr str_b str_ofs) (typeof (Etempvar _str (tptr tschar)))
                               (Vptr b ofs) (typeof (Etempvar _t'6 (tptr tschar))) m = Some Vfalse)
    by admit;
    eassumption.
  Tactics.forward.
  econstructor.
  econstructor.
  econstructor.
  repeat econstructor.
  repeat env_assumption.
  eassumption.
  (* something breakes here after I added notation
  eassumption.
  apply exec_Sseq_2.
  econstructor.
  repeat econstructor.
  eassumption.
  congruence.*)
Admitted.
