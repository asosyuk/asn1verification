Require Import StructTact.StructTactics.
Require Import Core.Core Core.Tactics Core.PtrLemmas.
Require Import C_strtoimax.AST C_strtoimax.Spec.

Import ListNotations.

Local Open Scope Int64Scope.

(* Dealing with the switch statement *)

Definition switch :=
(Sswitch (Ederef (Etempvar _str (tptr tschar)) tschar)
       (LScons (Some 45)
          (Ssequence
             (Sset _last_digit_max
                (Ebinop Oadd (Etempvar _last_digit_max tlong) (Econst_int (Int.repr 1) tint)
                   tlong)) (Sset _sign (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
          (LScons (Some 43)
             (Ssequence
                (Sset _str
                   (Ebinop Oadd (Etempvar _str (tptr tschar)) (Econst_int (Int.repr 1) tint)
                      (tptr tschar)))
                (Ssequence
                   (Sset _t'11 (Ederef (Etempvar _end (tptr (tptr tschar))) (tptr tschar)))
                   (Sifthenelse
                      (Ebinop Oge (Etempvar _str (tptr tschar)) (Etempvar _t'11 (tptr tschar))
                         tint)
                      (Ssequence
                         (Sassign (Ederef (Etempvar _end (tptr (tptr tschar))) (tptr tschar))
                            (Etempvar _str (tptr tschar)))
                         (Sreturn (Some (Econst_int (Int.repr (-1)) tint)))) Sskip))) LSnil))).

Lemma switch_default_correct : forall m ge e i le b ofs,
    Mem.loadv Mint8signed m (Vptr b ofs) = Some (Vint i) ->
    le ! _str = Some (Vptr b ofs) ->
    (i == minus_char)%int = false ->
    (i == plus_char)%int = false ->
                (exists t, exec_stmt ge e le m switch t le m Out_normal).
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
       
Lemma exec_loop_minus : forall m ge e le b ofs str_b str_ofs fin_b fin_ofs
                                    intp_b intp_ofs i out s1 s2,
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
Admitted.

Lemma exec_loop_plus : forall m ge e le b ofs str_b str_ofs fin_b fin_ofs
                              intp_b intp_ofs i out s1 s2,
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
                            m s1 t le' m' (Out_return out)) ->
        exists t le', exec_stmt ge e le m (pre_loop s1 s2) t le' m' (Out_return out).
Admitted.


Lemma exec_loop_none : forall m ge e le b ofs str_b str_ofs fin_b fin_ofs
                              intp_b intp_ofs i out s1 s2,
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
    
    forall m', (exists t le', exec_stmt ge e
      (PTree.set _value (Vlong (cast_int_long Signed (Int.repr 0)))
       (PTree.set _t'10 (Vint i)
          (PTree.set _t'12 (Vptr b ofs)
             (PTree.set _last_digit_max (Vlong last_digit_max)
                (PTree.set _upper_boundary
                   (Vlong
                      ((Int64.not (cast_int_long Signed (Int.repr 0)) >>
                        Int64.repr (Int.unsigned (Int.repr 1))) //
                       cast_int_long Signed (Int.repr 10)))
                   (PTree.set _asn1_intmax_max
                      (Vlong
                         (Int64.not (cast_int_long Signed (Int.repr 0)) >>
                          Int64.repr (Int.unsigned (Int.repr 1))))
                      (PTree.set _sign (Vint (Int.repr 1)) le)))))))
                          m s1 t le' m' (Out_return out)) ->
                   
     exists t le', exec_stmt ge e le m (pre_loop s1 s2) t le' m' (Out_return out).
Proof.
  intros until s2.
  intros Str End Intp UB Sign LA AG LA' CharP CharM  m' S1.
  destruct S1.
  unfold pre_loop.
  edestruct (switch_default_correct m ge e i
              (PTree.set _t'10 (Vint i)
       (PTree.set _t'12 (Vptr b ofs)
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
                   (PTree.set _sign (Vint (Int.repr 1)) le))))))).
  all: repeat rewrite set_env_eq_ptree_set in *;
    repeat (eassumption || env_assumption).
  destruct H.
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
  eapply (ptr_ge_to_sem_cmp_false _ _ _ _ _ AG).
  econstructor.
  econstructor.
  econstructor.
  repeat econstructor.
  repeat env_assumption.
  repeat env_assumption.
  eassumption.
  apply exec_Sseq_2.
  econstructor.
  repeat econstructor.
  eassumption.
  congruence.
Qed.
  

Lemma exec_loop_none_out_normal : forall m ge e le b ofs str_b str_ofs fin_b fin_ofs
                              intp_b intp_ofs i out s1 s2,
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
    
    forall m' le', (exists t, exec_stmt ge e
                          (PTree.set _value (Vlong (cast_int_long Signed (Int.repr 0)))
       (PTree.set _t'10 (Vint i)
          (PTree.set _t'12 (Vptr b ofs)
             (PTree.set _last_digit_max (Vlong last_digit_max)
                (PTree.set _upper_boundary
                   (Vlong
                      ((Int64.not (cast_int_long Signed (Int.repr 0)) >>
                        Int64.repr (Int.unsigned (Int.repr 1))) //
                       cast_int_long Signed (Int.repr 10)))
                   (PTree.set _asn1_intmax_max
                      (Vlong
                         (Int64.not (cast_int_long Signed (Int.repr 0)) >>
                          Int64.repr (Int.unsigned (Int.repr 1))))
                      (PTree.set _sign (Vint (Int.repr 1)) le)))))))
                          m s1 t le' m' Out_normal) ->
                    (exists t le'', exec_stmt ge e le'
       
                                   m' s2 t le'' m' (Out_return out)) ->
                    
                   
          exists t le'', exec_stmt ge e le m (pre_loop s1 s2) t le'' m' (Out_return out).
Proof.
  intros until s2.
  intros Str End Intp UB Sign LA AG LA' CharP CharM m' le' S1 S2.
  destruct S1.
  destruct S2.
  destruct H0.
  unfold pre_loop.
  edestruct (switch_default_correct m ge e i
              (PTree.set _t'10 (Vint i)
       (PTree.set _t'12 (Vptr b ofs)
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
                   (PTree.set _sign (Vint (Int.repr 1)) le))))))).
  all: repeat rewrite set_env_eq_ptree_set in *;
    repeat (eassumption || env_assumption).
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
  repeat econstructor.
  repeat env_assumption.
  repeat env_assumption.
  repeat env_assumption.
  repeat env_assumption.
  repeat env_assumption.
  econstructor.
  unfold load_addr in *.
  eapply (ptr_ge_to_sem_cmp_false _ _ _ _ _ AG).
  forward.
  econstructor.
  repeat env_assumption.
  repeat env_assumption.
  eassumption.
  eassumption.
  eassumption.
  Qed.
  
