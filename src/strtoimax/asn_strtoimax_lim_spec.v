From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import IntNotations asn_strtoimax_lim Tactics.
Local Open Scope Int64Scope.

(* Functional specification of INTEGER.c/asn_strtoimax_lim *)

(* Informal spec:
 
 Parse the number in the given string until the given end position,
  returning the position after the last parsed character back using the
  same (end) pointer. WARNING: This behavior is different from the standard strtol/strtoimax(3). *)

(* Output type, see INTEGER.h  *)

Inductive asn_strtox_result_e :=
  | ASN_STRTOX_ERROR_RANGE (* Input outside of supported numeric range *)
  | ASN_STRTOX_ERROR_INVAL (* Invalid data encountered (e.g., "+-") *)
  | ASN_STRTOX_EXPECT_MORE (* More data expected (e.g. "+") *)
  | ASN_STRTOX_EXTRA_DATA (* Conversion succeded, but the string has extra stuff *)
  | ASN_STRTOX_OK. (* Conversion succeded, number ends at (end) *) 

(* C light outputs directly int *)

Definition asn_strtox_result_e_to_int (s : asn_strtox_result_e) : int :=
  match s with
    | ASN_STRTOX_ERROR_RANGE => Int.repr (-3)  
    | ASN_STRTOX_ERROR_INVAL => Int.repr (-2)
    | ASN_STRTOX_EXPECT_MORE => Int.repr (-1)
    | ASN_STRTOX_EXTRA_DATA => Int.repr 1 
    | ASN_STRTOX_OK => Int.repr 0
  end.


(* Useful notations and definitions *)
(* Address [b,ofs] *)
Definition addr : Type := (block*ptrofs).
Definition vptr (a : addr) := match a with (b,ofs) => Vptr b ofs end.
Definition load_addr (chunk : memory_chunk) (m : mem) (a : addr) := match a with (b,ofs) =>  Mem.loadv chunk m (Vptr b ofs) end.
Definition next_addr (a : addr) := match a with (b,ofs) => (b, Ptrofs.add ofs Ptrofs.one) end.
Definition add_addr (a : addr) (i : ptrofs) := match a with (b,ofs) => (b, Ptrofs.add ofs i) end.
Notation "a ++" := (next_addr a) (at level 20).
Notation minus_char := (Int.repr 45).
Notation plus_char := (Int.repr 43).
Notation zero_char := (Int.repr 48).

(* Representing negative and positive int *)
Definition mult_sign s value :=
  match s with
  | Signed => Int64.neg value
  | Unsigned => value
  end.

(* Memory, global and local env are fixed *)
Parameter m : mem.
Parameter ge : genv.
Parameter e : env.

(* Pointer comparison *)
(* Abstract spec : [b1,ofs1] >= [b2,ofs2] *)
Definition ptr_ge_spec (b1 b2 : block) (ofs1 ofs2 : ptrofs) :=
  if eq_block b1 b2 then Some (ofs2 <= ofs1)%ptrofs else None.
(* Spec using Compcert semantic values *)
Definition ptr_ge (b1 b2 : block) (ofs1 ofs2 : ptrofs) :=
  if Archi.ptr64
  then Val.cmplu_bool (Mem.valid_pointer m) Cge (Vptr b1 ofs1) (Vptr b2 ofs2)
  else Val.cmpu_bool (Mem.valid_pointer m) Cge (Vptr b1 ofs1) (Vptr b2 ofs2).

Definition addr_ge (a1 a2 : addr) := match a1, a2 with (b1,ofs1), (b2,ofs2) => ptr_ge b1 b2 ofs1 ofs2 end.

(* Both specs can be used interchangeably *)
Proposition ptr_ge_refine : forall (b1 b2 : block) (ofs1 ofs2 : ptrofs),
    Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
    Mem.weak_valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
    ptr_ge_spec b1 b2 ofs1 ofs2 = ptr_ge b1 b2 ofs1 ofs2.
Proof.
  intros.
  unfold ptr_ge.
  simpl; unfold Mem.weak_valid_pointer in *.
  destruct Archi.ptr64 eqn: A; simpl.
  all: rewrite H; rewrite H0; simpl;
    destruct (Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) &&
                                Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2)); auto.
Qed.

Definition ASN1_INTMAX_MAX :=(Int64.not 0) >> 1.

Fact shift_pow2_div :  (Int64.shru (Int64.not Int64.zero) Int64.one) = Int64.repr (Int64.max_unsigned / 2).
  replace (Int64.not Int64.zero) with (Int64.repr Int64.max_unsigned) by (auto with ints).
  unfold Int64.shru.
  f_equal.
  Qed.

Definition upper_boundary := ASN1_INTMAX_MAX // (Int64.repr 10).
Definition last_digit_max := ASN1_INTMAX_MAX % (Int64.repr 10).
Definition last_digit_max_minus := (ASN1_INTMAX_MAX % (Int64.repr 10)) + 1.
(* digits [0-9]*)
Definition digits := map Int.repr [48;49;50;51;52;53;54;55;56;57].
Definition is_digit (i : int) := existsb (fun j => Int.eq i j) digits.
(* distance between the addresses *)
Definition distance (a1 a2 : addr) : nat :=
  ((Z.to_nat (Ptrofs.unsigned (snd a2))) - (Z.to_nat (Ptrofs.unsigned (snd a1))))%nat.
Definition int_to_int64 (i : int) := Int64.repr (Int.unsigned i).

(* Functional spec *)
(* Loop: *)
Fixpoint asn_strtoimax_lim_loop (str : addr) (fin : addr) (value : int64) (s: signedness) (last_digit : int64) (dist : nat) (m' : mem) {struct dist} : option (asn_strtox_result_e*(option(int64*signedness))*(option mem)) :=
  let m' := (Mem.storev Mptr m (vptr fin) (vptr str)) in
     match dist with
                | O => Some (ASN_STRTOX_OK, Some (value, s), m')
                | S n => match load_addr Many32 m str with
                        | Some (Vint i) =>
                          if is_digit i
                          then
                            let d := int_to_int64 (i - zero_char)%int in
                            let v := (value*(Int64.repr 10) + d) in
                            if value < upper_boundary
                            then asn_strtoimax_lim_loop (str++) fin v s last_digit n m
                            else if (value == upper_boundary) && (d <= last_digit)
                                 then asn_strtoimax_lim_loop (str++) fin v s last_digit n m
                                 else Some (ASN_STRTOX_ERROR_RANGE, Some (value,s),m') 
                          else Some (ASN_STRTOX_EXTRA_DATA, Some (value,s),m')
                        | Some _   =>  Some (ASN_STRTOX_EXTRA_DATA, Some (value,s),m')
                        | None => None
                        end
  end.

(* Spec: *)
Definition asn_strtoimax_lim (str fin : addr) : option (asn_strtox_result_e*(option(int64*signedness))*(option mem)) :=
  match load_addr Mptr m fin with (* derefencing **fin *)
  | Some (Vptr b ofs) =>  
             match addr_ge str (b,ofs) with (* compare str and *fin *)
             | Some true => Some (ASN_STRTOX_ERROR_INVAL, None, None)
             | Some false => let dist := distance str (b,ofs) in
                            match load_addr Mint8signed m str with
                            | Some (Vint i) =>
                              if (i == minus_char)%int
                              then match addr_ge (str++) (b,ofs) with
                                   | Some true => Some (ASN_STRTOX_EXPECT_MORE, None, (Mem.storev Mptr m (vptr fin) (vptr (str++))))
                                   | Some false => asn_strtoimax_lim_loop (str++) fin 0 Signed last_digit_max_minus (dist - 1)%nat m
                                   | None => None
                                   end
                              else if (i == plus_char)%int
                                   then match addr_ge (str++) (b,ofs) with
                                      | Some true => Some (ASN_STRTOX_EXPECT_MORE, None, (Mem.storev Mptr m (vptr fin) (vptr (str++))))
                                      | Some false => asn_strtoimax_lim_loop (str++) fin 0 Unsigned last_digit_max (dist - 1)%nat m
                                      | None => None
                                     end
                                   else asn_strtoimax_lim_loop str fin 0 Unsigned last_digit_max dist m
                            | _ => None (* fail of memory load on str: wrong type or not enough permission *)
                            end
             | None => None (* error in pointer comparison *)
             end
   | _ => None (* fail of pointer to fin *) 
  end.

(* Lemmas for each `asn_strtox_result_e` case *)
(* Case ASN_STRTOX_ERROR_INVAL: str >= *end *)
Lemma asn_strtoimax_lim_ASN_STRTOX_ERROR_INVAL_correct : forall le str fin,
    
    asn_strtoimax_lim str fin = Some (ASN_STRTOX_ERROR_INVAL, None, None) ->
    
     exists t le', le!_str = Some (vptr str)  ->
              le!_end = Some (vptr fin) ->
              
             exec_stmt ge e le m f_asn_strtoimax_lim.(fn_body) t le' m (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_INVAL), tint))).
Proof.
  intros.
  unfold asn_strtoimax_lim in H.
   assert (forall dist str fin value s last_digit, asn_strtoimax_lim_loop str fin value s last_digit dist m <> Some (ASN_STRTOX_ERROR_INVAL, None, None)) as Loop.
    { induction dist.
      intros.
      simpl.
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

Lemma strtoimax_loop_inv : forall n str fin outp m' value,
    asn_strtoimax_lim_loop str fin value Signed last_digit_max_minus (S n) m =
    Some (ASN_STRTOX_OK, outp, m') ->
    exists i, asn_strtoimax_lim_loop (str ++) fin  (value * Int64.repr 10 + int_to_int64 (i - zero_char)%int) Signed last_digit_max_minus n m =
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
Lemma asn_strtoimax_lim_ASN_STRTOX_EXPECT_MORE_correct : forall le str fin m',
    
    asn_strtoimax_lim str fin = Some (ASN_STRTOX_EXPECT_MORE, None, Some m') ->
    exists t le', le!_str = Some (vptr str)  ->
             le!_end = Some (vptr fin) ->
             le! _last_digit_max = Some (Vlong last_digit_max) -> 
      
             exec_stmt ge e le m f_asn_strtoimax_lim.(fn_body) t le' m' (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_EXPECT_MORE), tint))).
Proof.
  replace (asn_strtox_result_e_to_int ASN_STRTOX_EXPECT_MORE) with (Int.repr (-1)) by (cbv; auto).
  assert (forall dist str fin v s last_digit  m',
             asn_strtoimax_lim_loop str fin v s last_digit dist m <>  Some (ASN_STRTOX_EXPECT_MORE, None, Some m')) as Loop.
    { induction dist.
      intros.
      simpl.
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
  eapply e0.
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

  pose proof (Loop  (distance (b, i) (b1, i1) - 1)%nat ((b, i) ++) (b0, i0) 0 Signed last_digit_max_minus). congruence.
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
  eapply e0.
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

  pose (Loop (distance (b, i) (b1, i1) - 1)%nat  ((b, i) ++) (b0, i0) 0 Unsigned last_digit_max).  congruence.
  pose (Loop  (distance (b, i) (b1, i1)) (b, i) (b0, i0) 0 Unsigned last_digit_max m' ).  congruence.
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
Lemma switch_correct : forall i 
                       s1 s2 le b ofs,
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
 
 Lemma asn_strtoimax_lim_loop_ASN_STRTOX_OK_correct : forall dist b ofs le str fin inp_value out_value m',
     le!_str = Some (vptr str)  ->
     le!_end = Some (vptr fin) ->
     le!_value = Some (Vlong inp_value) ->
     le ! _upper_boundary = Some (Vlong upper_boundary) ->
     load_addr Mptr m fin = Some (Vptr b ofs) ->
     (distance str (b,ofs)) = dist ->
    asn_strtoimax_lim_loop str (b,ofs) inp_value Unsigned last_digit_max dist m = Some (ASN_STRTOX_OK, Some (out_value,Unsigned), Some m') ->
    
     exists t le',  exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m Out_normal
                             /\ le'!_value = Some (Vlong out_value).
 Proof.
   induction dist; intros until m'; intros Str End Value UB Load Dist Spec; unfold vptr in *;
     repeat break_let; subst.
   - (* Base case *)
     inversion Spec; clear Spec.
     rewrite <- H0.
     repeat eexists.
     eapply exec_Sloop_stop1.
     eapply exec_Sseq_2.
     repeat econstructor; repeat env_assumption; try econstructor.
     assert (sem_cmp Clt (Vptr b1 i0) (tptr tschar) (Vptr b ofs) (tptr tschar) m = Some Vfalse) by admit. (* follows from Dist, may need assumptions about validity of pointers and their comparison *)
     eassumption.
     all: try (repeat econstructor); repeat env_assumption; try discriminate.      
   - (* I.S. *)
     simpl in Spec.
     repeat break_match.
     all: try congruence.
     (* Case (inp_value < upper_boundary) *)
     (* Using Induction Hypothesis *)
     remember ((_str <~ Vptr b1 (i0 + 1)%ptrofs)
              ((_value <~ Vlong (inp_value * int_to_int64 (Int.repr 10) + int_to_int64 (i1 - zero_char)%int))
              ((_d <~ Vint (i1 - zero_char)%int)
              ((_t'2 <~ Vint i1) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))) as le''.
     pose proof (IHdist b ofs le'' (b1, (i0 + 1)%ptrofs) (b0, i) 
           (inp_value * Int64.repr 10 + int_to_int64 (i1 - zero_char)%int)  out_value 
           m') as IH.
     clear IHdist.
     destruct IH as [t IH]; subst; try (repeat env_assumption || reflexivity).
     admit. (* follows from Dist *)    
     destruct IH as [le' IH]; destruct IH as [IH LE'].
     (* Executing one loop *)
      (* dealing with switch statement: FIX *)
      pose proof (switch_correct i1 switch_body switch_default  (PTree.set _t'1 (Vint i1) (PTree.set _t'3 (Vptr b ofs) le)) b1 i0) as SW.
      unfold switch in SW.
      assert (Mem.loadv Mint8signed m (Vptr b1 i0) = Some (Vint i1)) as M by admit.
      assert (((_t'1 <~ Vint i1) ((_t'3 <~ Vptr b ofs) le)) ! _str = Some (Vptr b1 i0)) as L by admit.
     pose proof (SW M L Heqb2  ((_value <~
      Vlong
        (inp_value * cast_int_long Signed (Int.repr 10) +
         cast_int_long Signed (i1 - zero_char)%int))
       ((_d <~ Vint (i1 - zero_char)%int)
          ((_t'2 <~ Vint i1) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))).
     assert ((exists t : trace,
         exec_stmt ge e ((_t'1 <~ Vint i1) ((_t'3 <~ Vptr b ofs) le)) m switch_body t
           ((_value <~
             Vlong
               (inp_value * cast_int_long Signed (Int.repr 10) +
                cast_int_long Signed (i1 - zero_char)%int))
              ((_d <~ Vint (i1 - zero_char)%int)
                 ((_t'2 <~ Vint i1) ((_t'1 <~ Vint zero_char) ((_t'3 <~ Vptr b ofs) le)))))
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
     assert (sem_cmp Clt (Vptr b1 i0) (tptr tschar) (Vptr b ofs) (tptr tschar) m = Some Vtrue) by admit. (* follows from Dist *)
     eassumption.
     repeat econstructor.
     replace (negb (1 == 0)%int) with true by admit.
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
     admit.
    
     (* Case  (inp_value == upper_boundary) && (int_to_int64 (i1 - zero_char)%int <= last_digit_max) : same as before *)
 Admitted.

 (* Case ASN_STRTOX_EXTRA_DATA: go through the loop until a non-digit encountered *)
 (* Return condition: *)
 Lemma inver_EXTRA_DATA:  forall dist str fin inp_value out_value s m',
    asn_strtoimax_lim_loop str fin inp_value s last_digit_max dist m = Some (ASN_STRTOX_EXTRA_DATA, Some (out_value,s), Some m') ->
    exists i, (i < dist)%nat /\ (forall j, load_addr Many32 m (add_addr str (Ptrofs.repr (Z.of_nat i))) = Some (Vint j) -> is_digit j = false).
 Proof.
   induction dist.
   intros.
   unfold asn_strtoimax_lim_loop in H.
   congruence.
   intros.
   unfold  asn_strtoimax_lim_loop in H.
   repeat break_match.
   exists 0%nat.
   split.
   omega.
   replace (Ptrofs.repr (Z.of_nat 0)) with Ptrofs.zero by (auto with ptrofs).
   intros.
   unfold add_addr in H0.
   break_let.
   replace (i + 0)%ptrofs with i%ptrofs in H0.
   congruence.
   symmetry. auto with ptrofs. admit.
    fold  asn_strtoimax_lim_loop in H.
   pose (IHdist  (str ++) fin
        (inp_value * Int64.repr 10 + int_to_int64 (i - zero_char)%int) out_value s
        m' H) as IH.
   destruct IH. destruct H0.
   exists (x + 1)%nat.
   split.
   omega.
   replace (add_addr str (Ptrofs.repr (Z.of_nat (x + 1)))) with (add_addr (str ++) (Ptrofs.repr (Z.of_nat x))). 
   assumption.
   unfold add_addr.
   repeat break_let.
   inversion Heqp.
   f_equal.
   replace (Z.of_nat (x + 1)) with (Z.of_nat x + 1)%Z by lia.
   admit.
   Admitted.
 
Lemma asn_strtoimax_lim_loop_ASN_STRTOX_EXTRA_DATA_correct : forall dist b ofs le str fin inp_value out_value s last_digit m',
    load_addr Mptr m fin = Some (Vptr b ofs) -> 
    asn_strtoimax_lim_loop str (b,ofs) inp_value s last_digit dist m = Some (ASN_STRTOX_EXTRA_DATA, Some (out_value,s), Some m') ->
    
     exists t le', le!_str = Some (vptr str)  ->
                   le!_end = Some (vptr fin) ->
                   le!_value = Some (Vlong inp_value) ->
              
                   exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m'
                             (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_EXTRA_DATA), tint))).
Proof.
  intros.
  unfold asn_strtoimax_lim_loop in H0.
  Print memory_chunk.
  
  induction dist.
  intros.
  simpl in H0. congruence.
  intros.
   
  simpl in H0.                           
  repeat break_match.
  all: try congruence.
  
  pose (IHdist b ofs le (str ++) fin (inp_value * Int64.repr 10 + int_to_int64 (i - zero_char)%int) out_value s last_digit m' H H0). (* TODO: change le *)
  destruct e0.
  destruct H0.
  unfold vptr in *.
  repeat break_let.
  simpl in  Heqp.
  inversion  Heqp.
  rewrite H2 in *.
  repeat eexists.
  intros.
  repeat econstructor.
  apply H4.
  simpl in H.
  simpl.
  apply H.
  rewrite PTree.gso.
  apply H0.
  cbv; congruence.
  apply PTree.gss.
  simpl.
  assert (sem_cmp Clt (Vptr b0 i2) (tptr tschar) (Vptr b ofs) (tptr tschar) m = Some Vtrue) as T by admit.
  apply T.
  repeat econstructor.
  econstructor.
  rewrite PTree.gso.
  apply H0.
  cbv; congruence.
  simpl in Heqo.
  apply Heqo.
  repeat  rewrite PTree.gso.
  apply H0.
  1-2: cbv; congruence.
  apply Heqo.
  econstructor.
  replace i with (Int.repr 48) by admit. (* follows from is_digit *)
  repeat econstructor.
    repeat  rewrite PTree.gso.
    apply H0.
    1-2:  cbv; congruence.
     apply Heqo.
     apply PTree.gss.
     econstructor.
     repeat  rewrite PTree.gso.
  apply H5.
  1-4: cbv; congruence.
  assert (le! _upper_boundary = Some (Vlong upper_boundary)) by admit.
  repeat  rewrite PTree.gso.
  apply H6.
  1-4: cbv; congruence.
  econstructor.
  simpl.
  rewrite Heqb1.
  econstructor.
   econstructor.
  repeat econstructor.
  repeat  rewrite PTree.gso.
  apply H5.
  1-4: cbv; congruence.
  repeat econstructor.
  apply PTree.gss.
  repeat econstructor.
  (* Continue *)
   eapply exec_Scontinue.
  repeat  rewrite PTree.gso.
  apply H5.
  1-4: cbv; congruence.
  assert (le! _upper_boundary = Some (Vlong (Int64.repr (Int.unsigned upper_boundary)))) by admit. (* TODO: change to Int64 *)
  repeat  rewrite PTree.gso.
  apply H6.
  1-4: cbv; congruence.
  repeat econstructor.
  unfold tlong.
  simpl.
  Admitted.



    
