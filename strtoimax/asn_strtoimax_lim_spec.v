From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import IntNotations.
Require Import asn_strtoimax_lim.
Local Open Scope IntScope.

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

(* Address [b,ofs] *)
Definition addr : Type := (block*ptrofs).
(* Memory, global and local env are fixed *)
Parameter m : mem.
Parameter ge : genv.
Parameter e : env.

(* Pointer comparison *)
(* Abstract spec : [b1,ofs1] >= [b2,ofs2] *)
Definition ptr_ge_spec (b1 b2 : block) (ofs1 ofs2 : ptrofs) :=
  if eq_block b1 b2 then Some (ofs2 <= ofs1)%ptrofs else None.

(* Concrete spec using Compcert semantic values *)
Definition ptr_ge (b1 b2 : block) (ofs1 ofs2 : ptrofs) :=
  if Archi.ptr64
  then Val.cmplu_bool (Mem.valid_pointer m) Cge (Vptr b1 ofs1) (Vptr b2 ofs2)
  else Val.cmpu_bool (Mem.valid_pointer m) Cge (Vptr b1 ofs1) (Vptr b2 ofs2).

Definition addr_ge (a1 a2 : addr) := match a1, a2 with (b1,ofs1), (b2,ofs2) => ptr_ge b1 b2 ofs1 ofs2 end.

Proposition ptr_ge_refine : forall (b1 b2 : block) (ofs1 ofs2 : ptrofs),
    Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
    Mem.weak_valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
    ptr_ge_spec b1 b2 ofs1 ofs2 = ptr_ge b1 b2 ofs1 ofs2.
Proof.
  intros.
  unfold ptr_ge.
  simpl; unfold Mem.weak_valid_pointer in *.
  destruct Archi.ptr64 eqn: A; simpl.
  all: rewrite H;
    rewrite H0;
    simpl;
    destruct (Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) &&
                                Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2));
    auto.
Qed.

Definition vptr (a : addr) := match a with (b,ofs) => Vptr b ofs end.
    
(* We are reading a char type from the memory *)
Definition load_addr (chunk : memory_chunk) (m : mem) (a : addr) := match a with (b,ofs) =>  Mem.loadv chunk m (Vptr b ofs) end.

Definition next_addr (a : addr) := match a with (b,ofs) => (b, Ptrofs.add ofs Ptrofs.one) end.
Definition add_addr (a : addr) (i : ptrofs) := match a with (b,ofs) => (b, Ptrofs.add ofs i) end.

Notation "a ++" := (next_addr a) (at level 20).
Notation minus_char := (Int.repr 45).
Notation plus_char := (Int.repr 43).
Notation zero_char := (Int.repr 48).

Definition ASN1_INTMAX_MAX :=(Int.not 0) >> 1.

Fact shift_pow2_div :  (Int64.shru (Int64.not Int64.zero) Int64.one) = Int64.repr (Int64.max_unsigned / 2).
  replace (Int64.not Int64.zero) with (Int64.repr Int64.max_unsigned) by (auto with ints).
  unfold Int64.shru.
  f_equal.
  Qed.

Definition upper_boundary := ASN1_INTMAX_MAX // (Int.repr 10).
Definition last_digit_max_plus := ASN1_INTMAX_MAX % (Int.repr 10).
Definition last_digit_max_minus := (ASN1_INTMAX_MAX % (Int.repr 10)) + 1.
(* [0-9]*)
Definition digits := map Int.repr [48;49;50;51;52;53;54;55;56;57].
Definition is_digit (i : int) := existsb (fun j => Int.eq i j) digits.
Definition distance (a1 a2 : addr) : nat :=
  ((Z.to_nat (Ptrofs.unsigned (snd a2))) - (Z.to_nat (Ptrofs.unsigned (snd a1))))%nat.

(* Functional spec *)
Fixpoint asn_strtoimax_lim_loop (str : addr) (fin : addr) (value : int) (s: signedness) (last_digit : int) (dist : nat) (m' : mem) {struct dist} : option (asn_strtox_result_e*(option(int*signedness))*(option mem)) :=
  let m' := (Mem.storev Mptr m (vptr fin) (vptr str)) in
     match dist with
                | O => Some (ASN_STRTOX_OK, Some (value, s), m')
                | S n => match load_addr Mint8signed m str with
                        | Some (Vint i) =>
                          if is_digit i
                          then
                            let d := i - zero_char in
                            let v := (value*(Int.repr 10) + d) in
                            if value < upper_boundary
                            then asn_strtoimax_lim_loop (str++) fin v s last_digit n m
                            else if (value == upper_boundary) && (d <= last_digit)
                                 then asn_strtoimax_lim_loop (str++) fin v s last_digit n m
                                 else Some (ASN_STRTOX_ERROR_RANGE, Some (value,s),m') 
                          else Some (ASN_STRTOX_EXTRA_DATA, Some (value,s),m')
                        | _  => None
                        end
  end.
    
Definition asn_strtoimax_lim (str fin : addr) : option (asn_strtox_result_e*(option(int*signedness))*(option mem)) :=
  match load_addr Mptr m fin with (* derefencing **fin *)
  | Some (Vptr b ofs) =>  
             match addr_ge str (b,ofs) with (* compare str and *fin *)
             | Some true => Some (ASN_STRTOX_ERROR_INVAL, None, None)
             | Some false => let dist := distance str (b,ofs) in
                            match load_addr Mint8signed m str with
                            | Some (Vint i) =>
                              if (i == minus_char)
                              then asn_strtoimax_lim_loop (str++) fin 0 Signed last_digit_max_minus (dist - 1)%nat m
                              else if (i == plus_char)
                                   then
                                     if addr_ge (str++) (b,ofs)
                                     then Some (ASN_STRTOX_EXPECT_MORE, None, (Mem.storev Mptr m (vptr fin) (vptr (str++))))
                                     else  asn_strtoimax_lim_loop (str++) fin 0 Unsigned last_digit_max_plus (dist - 1)%nat m
                                   else asn_strtoimax_lim_loop str fin 0 Unsigned last_digit_max_plus dist m
                            | _ => None (* fail of memory load on str: wrong type or not enough permission *)
                            end
             | None => None (* error in pointer comparison *)
             end
   | _ => None (* fail of pointer to fin *) 
  end.

(* Useful lemmas about the spec *)
(* Inversion lemmas *)
Lemma strtoimax_loop_inv : forall n str fin outp m' value,
    asn_strtoimax_lim_loop str fin value Signed last_digit_max_minus (S n) m =
    Some (ASN_STRTOX_OK, outp, m') ->
    exists i, asn_strtoimax_lim_loop (str ++) fin  (value * Int.repr 10 + (i - zero_char)) Signed last_digit_max_minus n m =
    Some (ASN_STRTOX_OK, outp, m').
Proof.
  intros.
  simpl in H.
  break_if.
  all: repeat break_match; try congruence; exists i; assumption.
Qed.

Lemma strtoimax_inv_mem : forall n str fin outp m' value, 
  asn_strtoimax_lim_loop str fin value Signed last_digit_max_minus n m = Some (ASN_STRTOX_OK, outp, m') ->
  forall i, (i < n)%nat -> exists v, load_addr Mint8signed m (add_addr str (Ptrofs.repr (Z.of_nat i))) = Some (Vint v) /\ is_digit v = true.
Proof.
  induction n.
  - intros. nia.
  - intros until value; intro H.
    pose (strtoimax_loop_inv _ _ _ _ _ _ H) as S.
    destruct S as [j S].
    pose (IHn (str++) fin  outp _ (value * Int.repr 10 + (j - zero_char))  S) as N.
    Admitted.

Ltac exec_until_seq := 
     repeat  match goal with
            | [ |- exec_stmt _ _ _ _ (Ssequence _ _)  _ _ _ _ ] => idtac
            | _ => econstructor ; exec_until_seq

             end.

Lemma loop_result : forall  (dist : nat) (str : addr) (fin : addr) (value : int) (s: signedness) (last_digit : int),
    asn_strtoimax_lim_loop str fin value s last_digit dist m <> Some (ASN_STRTOX_ERROR_INVAL, None, None).
Proof.
  induction dist.
  intros.
  simpl.
  congruence.
  intros.
  simpl.
  repeat break_match.
  repeat break_if.
  all: try congruence.
Qed.

Lemma asn_strtoimax_lim_ASN_STRTOX_ERROR_INVAL_correct : forall le str fin,
    
    asn_strtoimax_lim str fin = Some (ASN_STRTOX_ERROR_INVAL, None, None) ->
    
     exists t le', le!_str = Some (vptr str)  ->
              le!_end = Some (vptr fin) ->
              
             exec_stmt ge e le m f_asn_strtoimax_lim.(fn_body) t le' m (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_INVAL), tint))).
Proof.
  intros.
  unfold asn_strtoimax_lim in H.
  
  break_match.
  break_match.
  all: try congruence.
  break_match.
  unfold addr_ge in Heqo0.
  destruct b0.
  unfold vptr in *.
  repeat break_let.
   unfold addr_ge in Heqo0.
   replace (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_INVAL) with  (Int.repr (-2)).
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
  simpl.
  unfold sem_cmp.
  simpl.
  unfold cmp_ptr.
  assert (option_map Val.of_bool
    (if Archi.ptr64
     then Val.cmplu_bool (Mem.valid_pointer m) Cge (Vptr b0 i0) (Vptr b i)
     else Val.cmpu_bool (Mem.valid_pointer m) Cge (Vptr b0 i0) (Vptr b i)) = (option_map Val.of_bool (Some true))).
  f_equal.
  unfold ptr_ge in Heqo0.
  assumption.
    eapply H0.
    simpl.
    econstructor.
    repeat econstructor.
    cbv; congruence.
    cbv. auto.
    repeat break_match.
    all: try congruence.
    all: pose (loop_result _ _ _ _ _ _ H).
    all: contradiction.
Qed.

Lemma asn_strtoimax_lim_loop_ASN_STRTOX_EXTRA_DATA_correct : forall dist le str fin value s last_digit,
    
    asn_strtoimax_lim_loop str fin value s last_digit dist m = Some (ASN_STRTOX_EXTRA_DATA, None, None) ->
    
     exists t le', le!_str = Some (vptr str)  ->
                   le!_end = Some (vptr fin) ->
                   le!_value = Some (Vlong (Int64.repr (Int.unsigned value))) ->
              
             exec_stmt ge e le m f_asn_strtoimax_lim_loop t le' m (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_EXTRA_DATA), tint))).
Proof.
  induction dist.
  intros.
  simpl in H. congruence.
  intros.
  simpl in H.
  repeat break_match.
  all: try congruence.
  pose (IHdist le (str ++) fin (value * Int.repr 10 + (i - zero_char)) s
               last_digit H). (* TODO: change le *)
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
  assert (Mem.loadv Mptr m (Vptr b0 i1) = Some (Vptr b0 i1)) as M by admit. (* derefencing a pointer *)
  apply M.
  rewrite PTree.gso.
  apply H1.
  cbv; congruence.
  apply PTree.gss.
  simpl.
  assert (sem_cmp Clt (Vptr b i2) (tptr tschar) (Vptr b0 i1) (tptr tschar) m = Some Vtrue) as T by admit.
  apply T.
  repeat econstructor.
  econstructor.
  rewrite PTree.gso.
  apply H1.
  cbv; congruence.
  simpl in Heqo.
  apply Heqo.
  repeat  rewrite PTree.gso.
  apply H1.
  1-2: cbv; congruence.
  repeat  rewrite PTree.gso.
  simpl in Heqo.
  apply Heqo.
  simpl.
  econstructor.
  Print exec_stmt.
  Print seq_of_labeled_statement.
  Print select_switch.
  replace i with (Int.repr 48) by admit.
  repeat econstructor.
    repeat  rewrite PTree.gso.
    apply H1.
    1-2:  cbv; congruence.
     simpl in Heqo.
     apply Heqo.
     apply PTree.gss.
     econstructor.
     repeat  rewrite PTree.gso.
  apply H5.
  1-4: cbv; congruence.
  assert (le! _upper_boundary = Some (Vlong (Int64.repr (Int.unsigned upper_boundary)))) by admit.
  repeat  rewrite PTree.gso.
  apply H6.
  1-4: cbv; congruence.
  simpl.
  econstructor.
  unfold tlong.
  simpl.
  replace (Int64.lt (Int64.repr (Int.unsigned value))
          (Int64.repr (Int.unsigned upper_boundary))) with true.
    
  econstructor.
  (* follows from an assumption *)
  admit.
  break_if.
  repeat econstructor.
  repeat  rewrite PTree.gso.
  apply H5.
  1-4: cbv; congruence.
  repeat econstructor.
  apply PTree.gss.
  repeat econstructor.

  repeat econstructor.
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



Lemma asn_strtoimax_lim_loop_correct' : forall le str fin value m', 
    asn_strtoimax_lim str fin = Some (ASN_STRTOX_OK, Some (value, Unsigned), Some m') ->
    exists t le', le!_str = Some (vptr str)  ->
             le!_end = Some (vptr fin) ->
      
             exec_stmt ge e le m f_asn_strtoimax_lim.(fn_body) t le' m (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_OK), tint)))
             /\ le'!_intp = Some (Vint value)
             /\ le'!_end = Some (vptr str).
Proof.
  intros until value; intros m' Spec.
  unfold vptr.
  repeat break_let.
  unfold asn_strtoimax_lim in Spec.
  repeat break_match.
  all: try congruence.
  repeat eexists.
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
  assert (sem_cmp Cge (Vptr b i) (tptr tschar)  (Vptr b1 i1) (tptr tschar) m = Some Vfalse) by admit. (* follows from spec: TODO*)
  apply H1.
  repeat econstructor.
  repeat econstructor. 
  repeat rewrite PTree.gso.
  apply H.
  1-4: cbv; congruence.
  apply Heqo1.
  replace Out_normal with (outcome_switch  Out_normal).
  repeat econstructor.
  repeat rewrite PTree.gso.
  eapply H.
  1-5: cbv; congruence.
  simpl in Heqo1.
  simpl.
  apply Heqo1.
  repeat econstructor.
  replace i2 with minus_char.
  repeat econstructor.
  assert ((le! _last_digit_max) = Some (Vint last_digit_max_minus)) by admit. (* change to int64 *)
  repeat rewrite PTree.gso.
  eapply H1.
  1-5: cbv; admit. (* TODO: fix ident *)
  repeat econstructor.
  simpl.
  unfold tlong.
  unfold tint.
   Admitted.
    
    
