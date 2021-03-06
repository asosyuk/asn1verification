(** This is a toy example to demonstrate how to specify and prove correct a C function using C light *)

From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.

(* Specification of the strlen function *)
Inductive strlen (m : mem) (b : block) (ofs : ptrofs) : nat -> Prop :=
| LengthZero: Mem.loadv Mint8signed m (Vptr b ofs) = Some (Vint Int.zero) -> strlen m b ofs 0
| LengthSucc: forall n c,
    Z.of_nat (S n) < Int.modulus -> (* no int overflow *)
    Ptrofs.unsigned ofs + 1 < Ptrofs.modulus -> (* no ofs overflow *)
    strlen m b (Ptrofs.add ofs Ptrofs.one) n ->
    Mem.loadv Mint8signed m (Vptr b ofs)  = Some (Vint c) ->
    c <> Int.zero ->
    strlen m b ofs (S n).

(* strlen C light AST *)
Definition _output : ident := 4%positive.
Definition _input : ident := 3%positive.
Definition _t'1 : ident := 7%positive.
Definition _t'2 : ident := 8%positive.

Definition f_strlen := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_input, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_output, tuint) :: (_t'1, (tptr tschar)) :: (_t'2, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _output (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'1 (Etempvar _input (tptr tschar)))
            (Sset _input
              (Ebinop Oadd (Etempvar _t'1 (tptr tschar))
                (Econst_int (Int.repr 1) tint) (tptr tschar))))
          (Ssequence
            (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tschar)) tschar))
            (Sifthenelse (Etempvar _t'2 tschar) Sskip Sbreak)))
        (Sset _output
          (Ebinop Oadd (Etempvar _output tuint) (Econst_int (Int.repr 1) tint)
            tuint)))
      Sskip)
    (Sreturn (Some (Etempvar _output tuint)))))
                          |}.

Definition f_strlen_loop :=
  (Sloop
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'1 (Etempvar _input (tptr tschar)))
            (Sset _input
              (Ebinop Oadd (Etempvar _t'1 (tptr tschar))
                (Econst_int (Int.repr 1) tint) (tptr tschar))))
          (Ssequence
            (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tschar)) tschar))
            (Sifthenelse (Etempvar _t'2 tschar) Sskip Sbreak)))
        (Sset _output
          (Ebinop Oadd (Etempvar _output tuint) (Econst_int (Int.repr 1) tint)
            tuint)))
      Sskip).


Definition f_strlen_loop_body := (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'1 (Etempvar _input (tptr tschar)))
            (Sset _input
              (Ebinop Oadd (Etempvar _t'1 (tptr tschar))
                (Econst_int (Int.repr 1) tint) (tptr tschar))))
          (Ssequence
            (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tschar)) tschar))
            (Sifthenelse (Etempvar _t'2 tschar) Sskip Sbreak)))
        (Sset _output
          (Ebinop Oadd (Etempvar _output tuint) (Econst_int (Int.repr 1) tint)
                  tuint))).



(* Our goal is to prove that the C light AST is equivalent satisfies the spec: in this context it means that the C light AST evaluates to the correct value wrt to big step operational semantics *)

(* Some useful notation and tactics *)

Definition chunk : memory_chunk := Mint8signed.
Definition VintZ := fun (z : Z) => Vint (Int.repr z).
Definition VintN:= fun n => Vint (Int.repr(Z_of_nat n)).

Notation gso := PTree.gso.
Notation gss := PTree.gss.

(* Tactics for arithmetic on ptrofs, now they are ad hoc, TODO: automatize translation from ptrofs to Z *)

Ltac ints_to_Z :=
  repeat rewrite Int.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac ptrofs_to_Z :=
  repeat rewrite Ptrofs.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac ptrofs_compute_add_mul :=
      simpl; unfold Ptrofs.add; unfold Ptrofs.mul; unfold Ptrofs.of_intu; unfold Ptrofs.of_int;
      repeat rewrite Ptrofs.unsigned_repr_eq;  repeat rewrite Int.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac ints_compute_add_mul :=
      simpl; unfold Int.add; unfold Int.mul;
      repeat rewrite Int.unsigned_repr_eq;  repeat rewrite Int.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac seq1 := eapply exec_Sseq_1.
Ltac seq2 := eapply exec_Sseq_2.
Ltac sset := eapply exec_Sset.
Ltac loop := eapply exec_Sloop_loop.

(* can make more generic to repeatedly apply gso *)
Ltac gso_assumption :=
  match goal with
  | [ H : ?P ! ?I = Some ?W |- (PTree.set _ _ ?P) ! ?I = Some ?Z ] => rewrite gso  
  | [ H : ?P ! ?Q = Some ?W |-  ?P ! ?Q = Some ?Z ] => apply H
  | [ |- _ <> _ ] => cbv ; congruence
  end.

Proposition char_not_zero : forall c, c <> Int.zero -> true = (negb (Int.eq c Int.zero)).
Proof.
  intros.
  replace (Int.eq c Int.zero) with false.
  auto.
  rewrite Int.eq_false; intuition.
Qed.  

Parameter ge : genv.
Parameter e : env.
(* Test *)
Lemma strlen_correct_test: forall m b ofs le,
    strlen m b ofs 2%nat ->
    le!_input = Some (Vptr b ofs) ->
    (* C light expression f_strlen returns O and assigns O to output variable *)
    exists t le', exec_stmt ge e le m f_strlen.(fn_body) t le' m (Out_return (Some ((VintZ 2),tuint))) /\ (le'!_output) = Some (VintZ 2).
Proof.
  intros until le. intro Spec.
  inversion_clear Spec. inversion_clear H1. inversion_clear H6.
  repeat eexists.
  - seq1.
    -- sset. (* evaluate expression *) repeat econstructor.
    -- seq1.   
      * (* loop 1 *)
        loop. repeat econstructor. repeat gso_assumption. eapply gss. repeat econstructor.
        rewrite gso. apply gss. cbv. congruence. apply H2.
        apply gss.
        econstructor.
        replace (negb (Int.eq c Int.zero)) with true by (apply (char_not_zero c); assumption).
        econstructor.
         rewrite gso. rewrite gso. rewrite gso. apply gss. 1-3: cbv; congruence.
        repeat econstructor. econstructor. econstructor.

        (* loop 2 *)
        loop. repeat econstructor. 
        rewrite gso. rewrite gso. apply gss. 1-2: cbv; congruence. apply gss.
        repeat econstructor.
        rewrite gso. apply gss. cbv; congruence.
        replace (Ptrofs.add ofs
          (Ptrofs.mul (Ptrofs.repr (sizeof ge tschar))
             (ptrofs_of_int Signed (Int.repr 1)))) with (Ptrofs.add ofs Ptrofs.one) by (auto with ptrofs).
        apply H7.
        apply gss.
        econstructor.
        replace (negb (Int.eq c0 Int.zero)) with true by (apply (char_not_zero c0); assumption).      
        econstructor. 
        rewrite gso. rewrite gso. rewrite gso. apply gss. 1-3: cbv; congruence.
        repeat econstructor. econstructor. econstructor.
            
         (* exit loop *)
        eapply exec_Sloop_stop1.
        seq2. seq1. seq1. econstructor. econstructor. rewrite gso. rewrite gso. apply gss. 1-2: cbv; congruence.
        repeat econstructor.
        apply gss.
        repeat econstructor.
        seq1. repeat econstructor.
        rewrite gso. apply gss. cbv ; congruence.
        replace (Ptrofs.add
          (Ptrofs.add ofs
             (Ptrofs.mul (Ptrofs.repr (sizeof ge tschar))
                (ptrofs_of_int Signed (Int.repr 1))))
          (Ptrofs.mul (Ptrofs.repr (sizeof ge tschar))
             (ptrofs_of_int Signed (Int.repr 1))))  with (Ptrofs.add (Ptrofs.add ofs Ptrofs.one) Ptrofs.one) by (auto with ptrofs).
        apply H1.
        repeat econstructor.
        apply gss.
        econstructor. 
        replace (negb (Int.eq Int.zero Int.zero)) with false by (auto with ints).
        econstructor.
        cbv; congruence.
        econstructor.
      * (* return statement *)
        repeat econstructor.  rewrite gso.  rewrite gso. rewrite gso.  eapply gss. all: cbv; congruence.
  - rewrite gso.  rewrite gso.  rewrite gso. eapply gss. all: cbv; congruence.
Qed.
(* Helper lemmas about the specification *)

 (* add more lemmas from Compcert to ptrofs hints *)
Lemma int_ptrofs_mod_eq : (Int.modulus = Ptrofs.modulus).
Proof.
  cbv; split; congruence.
Qed.

Hint Resolve Ptrofs.mul_one Ptrofs.add_zero int_ptrofs_mod_eq : ptrofs.

Lemma strlen_to_len_0 : forall len m b ofs, strlen m b ofs len -> strlen m b (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat len))) O.
Proof.
  induction len; intros.
  - simpl.  replace (Ptrofs.repr 0) with Ptrofs.zero by (auto with ptrofs).
    replace (Ptrofs.add ofs Ptrofs.zero) with ofs by (auto with ptrofs).
    assumption.
  - inversion_clear H.
    replace (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat (S len)))) with
    (Ptrofs.add (Ptrofs.add ofs Ptrofs.one) (Ptrofs.repr (Z.of_nat len))).
    apply (IHlen m b (Ptrofs.add ofs Ptrofs.one) H2).
    { rewrite Nat2Z.inj_succ.
      replace  (Z.succ (Z.of_nat len)) with ((Z.of_nat len) + 1) by (auto with zarith).
      unfold Ptrofs.one.
      symmetry.
      rewrite Ptrofs.add_assoc.
      f_equal.
      ptrofs_compute_add_mul.
      all: pose  int_ptrofs_mod_eq; try nia.
      f_equal. auto with zarith. }
Qed.


Lemma strlen_to_mem : forall len m b ofs, strlen m b ofs len ->
                                     forall i, (i < len)%nat -> exists c, Mem.loadv chunk m (Vptr b (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i)))) = Some (Vint c) /\ c <> Int.zero.
Proof.
  induction len.
  - intros. omega.
  -  induction i; intro; inversion_clear H.
     +  replace (Ptrofs.repr (Z.of_nat 0)) with Ptrofs.zero by (simpl; auto with ptrofs).
        replace (Ptrofs.add ofs Ptrofs.zero) with ofs by (auto with ptrofs).
       exists c. exact (conj H4 H5).
    +  assert (i < len)%nat by omega. pose (IHlen m b (Ptrofs.add ofs Ptrofs.one) H3 i H).
       replace (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat (S i)))) with  (Ptrofs.add (Ptrofs.add ofs Ptrofs.one) (Ptrofs.repr (Z.of_nat i))).
       assumption.
       {
         rewrite Nat2Z.inj_succ.
         replace  (Z.succ (Z.of_nat i)) with ((Z.of_nat i) + 1) by (auto with zarith).
         unfold Ptrofs.one.
         ptrofs_compute_add_mul.
         f_equal.
         nia.
         all: pose int_ptrofs_mod_eq; try nia.
         destruct ofs; simpl in *.
         nia.
       }
Qed. 

(* Correctness statements *)


Lemma strlen_loop_correct_gen :
  forall len i m b ofs le,
    (* we read a C string of length len + i from memory and len + i is a valid integer *)
    strlen m b ofs (len + i) ->   
    (* THEN there is a trace t and local environment le' such that: *)
    forall t le',
      (* if output equals i in the starting local environment le *)
      le!_output = Some (VintN i) ->
      (* if input is an address [b,ofs + i] in the starting local environment *)
      le!_input = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i)))) ->     (* then loop of strlen function executes to le' with output assigned len + i *)
      exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (VintN (len + i)).
Proof.

(* A generalization of loop correctness *)
Lemma strlen_loop_correct_gen :
  forall len i m b ofs le,
    (* we read a C string of length len + i from memory and len + i is a valid integer *)
    strlen m b ofs (len + i) ->   
    (* THEN there is a trace t and local environment le' such that: *)
    exists t le',
      (* if output equals i in the starting local environment le *)
      le!_output = Some (VintN i) ->
      (* if input is an address [b,ofs + i] in the starting local environment *)
      le!_input = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i)))) ->     (* then loop of strlen function executes to le' with output assigned len + i *)
      exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (VintN (len + i)).
Proof.
  assert (Int.modulus <= Ptrofs.modulus) as B.
  { cbv. destruct Archi.ptr64. 1-2: congruence. }
  induction len; intros until le; intro Spec. 
  - (* Base case *)    
    simpl in Spec.
    repeat eexists.
    (* Exit the loop *)
    eapply exec_Sloop_stop1. seq2. repeat econstructor.
    apply H0.
    eapply gss.
    repeat econstructor.
    rewrite gso. apply gss. cbv. congruence.
    (* Derive memory assumptions from the specification *)
    pose (Spec_mem := strlen_to_len_0 i m b ofs Spec).
    inversion_clear Spec_mem.
    apply H1.
    apply gss.
    econstructor.
    replace (negb (Int.eq Int.zero Int.zero)) with false by (auto with ints).      
    econstructor.
    cbv; congruence. econstructor.
    repeat (rewrite gso).
    replace (0 + i)%nat with i by lia.
    assumption.
    1-3: cbv; congruence.
  - (* Ind. Step *)
    assert (exists char, Mem.loadv Mint8signed m (Vptr b  (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i)))) = Some (Vint char) /\ char <> Int.zero) as Mem. 
    { refine (strlen_to_mem (S len + i) m b ofs Spec i _). omega. }
    destruct Mem as [char Mem].
    (* apply I.H. to le' after one step when starting with i and [b,ofs + i]  *)
    pose (le'' :=  (PTree.set _output (VintN (S i))
       (PTree.set _t'2 (Vint char) (PTree.set _input
               (Vptr b  (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat (S i)))))
          (PTree.set _t'1
               (Vptr b  (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i))))
                      le))))).
    pose (IH := IHlen (S i)  m b ofs le'').
    assert ( exists (t : trace) (le' : temp_env),
       le'' ! _output = Some (VintN (S i)) -> 
       le''! _input = Some (Vptr b  (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat (S i))))) ->               
       exec_stmt ge e le'' m f_strlen_loop t le' m
         Out_normal /\
       le' ! _output = Some (VintN (len + S i))) as Step.
    { eapply IH.
      replace (len + S i)%nat with (S len + i)%nat by omega.
      assumption. }
    destruct Step as [s Step]. destruct Step as [t Step].
    (* Do one loop on the goal: then apply IH *)
    repeat eexists.
    loop. repeat econstructor.
    apply H0.
    eapply gss. 
    repeat econstructor.
    rewrite gso. apply gss. cbv; congruence.
    simpl. ptrofs_to_Z.
    apply Mem.
    apply gss.
    econstructor.
    replace (negb (Int.eq char Int.zero)) with true by (apply (char_not_zero char); apply Mem).
    econstructor. 
    repeat (rewrite gso). apply H. 1-3: cbv; congruence.
    repeat econstructor. econstructor. econstructor.
    fold f_strlen_loop.
    replace (PTree.set _output
       (Vint (Int.add (Int.repr (Z.of_nat i)) (Int.repr 1)))
       (PTree.set _t'2 (Vint char)
          (PTree.set _input
             (Vptr b
                (Ptrofs.add
                   (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i)))
                   (Ptrofs.mul
                      (Ptrofs.repr (sizeof ge tschar))
                      (ptrofs_of_int Signed (Int.repr 1)))))
             (PTree.set _t'1
                (Vptr b
                   (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i))))
                le)))) with le''.
  eapply Step.
  apply gss.
  unfold le''. rewrite gso. rewrite gso. apply gss.
  1-2: cbv; congruence.

  { inversion Spec.
    unfold le''.
    replace (Vint (Int.add (Int.repr (Z.of_nat i)) (Int.repr 1))) with (VintN (S i)).
    replace (Ptrofs.add
                (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i)))
                (Ptrofs.mul (Ptrofs.repr (sizeof ge tschar))
                            (ptrofs_of_int Signed (Int.repr 1)))) with (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat (S i)))).
    reflexivity.
    + rewrite Nat2Z.inj_succ.
      replace  (Z.succ (Z.of_nat i)) with ((Z.of_nat i) + 1) by (auto with zarith).
      simpl.
      replace  (Ptrofs.repr 1) with Ptrofs.one by (auto with ptrofs).
      replace  (Ptrofs.of_ints (Int.repr 1)) with Ptrofs.one by (auto with ptrofs).
      replace  (Ptrofs.mul Ptrofs.one Ptrofs.one) with (Ptrofs.one) by (auto with ptrofs).
      unfold Ptrofs.one.
      symmetry.
      rewrite Ptrofs.add_assoc.
      f_equal.
      ptrofs_compute_add_mul.
      auto.
      all: pose int_ptrofs_mod_eq; try nia.
    + unfold VintN.
      f_equal.
      ints_compute_add_mul.
      f_equal.
      lia.
      cbv. econstructor. 1-2: congruence.
      nia.
      }
  destruct Step.
  apply gss.
  unfold le''. rewrite gso. rewrite gso. apply gss.
  1-2: cbv; congruence.
  replace (S len + i)%nat with (len + S i)%nat by omega.
  assumption.
Qed.      

(* Correctness of the loop execution *)
Lemma strlen_loop_correct: forall len m b ofs le, strlen m b ofs len -> exists t le', le!_output = Some (VintN O) ->
                                                                                    le!_input = Some (Vptr b ofs) ->
      
      exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (VintN len).
Proof.
  intros.
  replace ofs with (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat O))) by (auto with ptrofs).
  replace len with (len + O)%nat by lia.
  eapply strlen_loop_correct_gen.
  replace (len + O)%nat with len by omega.
  assumption.
Qed.
  
(* Full correctness statement *)
Lemma strlen_correct: forall len m b ofs le, strlen m b ofs len -> exists t le', le!_input = Some (Vptr b ofs) ->
                                                                               exec_stmt ge e le  m f_strlen.(fn_body) t le' m (Out_return (Some ((VintN len),tuint))).
Proof.
  intros.
  pose (Loop := strlen_loop_correct len  _ _ _ (PTree.set _output (Vint Int.zero) le) H). destruct Loop as [t Loop]. destruct Loop as [le' Loop].
  repeat eexists.
  intro input.
  assert ((PTree.set _output (Vint Int.zero) le) ! _output =
          Some (VintN 0)) as O by (apply gss).
  assert ((PTree.set _output (Vint Int.zero) le) ! _input =
          Some (Vptr b ofs)) as I.
  { rewrite gso. assumption. cbv; congruence. }
  destruct (Loop O I) as [Exec Out].
  seq1. 
  repeat econstructor.
  seq1. fold f_strlen_loop.
  eapply Exec.
  repeat econstructor.
  eapply Out.
Qed.


(* Specification of the strlen function on integers *)

Definition no_int_overflow (i : int) := 0 < Int.unsigned i + 1 < Int.modulus.
Definition no_pointer_overflow (i : ptrofs) := 0 < Ptrofs.unsigned i + 1 < Int.modulus.

Definition Int_succ := fun i : int => Int.add i Int.one.

Inductive strlen_int (m : mem) (b : block) (ofs : ptrofs) : int -> Prop :=
| LengthZeroInt: Mem.loadv Mint8signed m (Vptr b ofs) = Some (Vint Int.zero) -> strlen_int m b ofs Int.zero
| LengthSuccInt: forall n c,
    no_pointer_overflow ofs -> (* this condition is superflous *)
    no_int_overflow n ->
    Mem.loadv Mint8signed m (Vptr b ofs)  = Some (Vint c) ->
    c <> Int.zero ->
    strlen_int m b (Ptrofs.add ofs Ptrofs.one) n ->
    strlen_int m b ofs (Int_succ n).

Lemma strlen_refine : forall m b ofs i, strlen_int m b ofs i -> strlen m b ofs (Z.to_nat (Int.unsigned i)).
Proof.
  intros.
  induction H.
  replace (Z.to_nat (Int.unsigned Int.zero)) with O by (auto with ints; nia).
  econstructor.
  assumption.
  replace (Z.to_nat (Int.unsigned (Int_succ n))) with (S (Z.to_nat (Int.unsigned n))).
  econstructor.
  unfold no_int_overflow in H0.
  replace  (S (Z.to_nat (Int.unsigned n))) with  ((Z.to_nat (Int.unsigned n)) + 1)%nat by omega.
  destruct n; simpl in *; try nia.
  Search Z.of_nat.
  rewrite Nat2Z.inj_add.
  Search Z.of_nat (Z.to_nat _).
  
  replace (Z.of_nat (Z.to_nat intval)) with intval.
  replace (Z.of_nat 1) with 1 by nia.
  nia.
  symmetry.
  (eapply Z2Nat.id).
  nia.
  unfold no_pointer_overflow in H.
  pose int_ptrofs_mod_eq;   nia.
  (* true *)
  assumption.
  apply H1.
  assumption.

  unfold no_int_overflow in H.
  unfold Int_succ.
  replace  (Int.unsigned (Int.add n Int.one)) with (Int.unsigned n + 1).
  replace  (S (Z.to_nat (Int.unsigned n))) with  ((Z.to_nat (Int.unsigned n)) + 1)%nat by omega.
  Search Z.to_nat.
  rewrite Z2Nat.inj_add.
  replace  (Z.to_nat 1) with 1%nat.
  auto.
  symmetry.
  unfold Z.to_nat.
  nia.
  destruct n; simpl in *; nia.
  nia.
  ints_compute_add_mul.
  all: replace (Int.unsigned Int.one) with 1 by (auto with ints).
  auto. unfold no_int_overflow in H0. nia.
  Qed.

(* Full correctness statement *)
Lemma strlen_correct_int: forall len m b ofs le,
      strlen_int m b ofs len -> exists t le',
      le!_input = Some (Vptr b ofs) ->
      exec_stmt ge e le  m f_strlen.(fn_body) t le' m (Out_return (Some ((Vint len),tuint))).
Proof.
  intros until le; intro Spec.
  pose (strlen_refine _ _ _ _  Spec) as S.
  pose (strlen_correct _ _ _  _  le   S).
  replace (VintN (Z.to_nat (Int.unsigned len))) with (Vint len) in e0.
  assumption.
  unfold VintN.
  f_equal.
  replace (Z.of_nat (Z.to_nat (Int.unsigned len))) with (Int.unsigned len).
  auto with ints.
  rewrite Z2Nat.id.
  auto.
  destruct len; simpl in *. nia.
Qed.

(* Functional spec *)
(* true if the integer value read is zero - end of string *)

Definition is_null (v : Values.val) :=
  match v with
  | Vint zero => true
  | _ => false
  end.

Definition INTSIZE := (nat_of_Z Int.modulus).

Fixpoint strlen_fun_spec (m : mem) (b : block) (ofs : ptrofs) (l: Z) (intrange : nat) {struct intrange} : option int := 
      match intrange with
      | O => None (* out of intrange *)
      | S n => match Mem.loadv chunk m (Vptr b ofs) with 
              | Some v =>
                if is_null v
                then Some (Int.repr l) else strlen_fun_spec m b (Ptrofs.add ofs Ptrofs.one) (l + 1) n  
              | None => None 
              end
      end.

Definition strlen_fun (m : mem) (b: block) (ofs : ptrofs) :=  strlen_fun_spec m b ofs 0 INTSIZE.

(* Full correctness statement *)
Lemma strlen_correct_fun: forall len m b ofs le, strlen_fun m b ofs = Some len ->
                                            exists t le', le!_input = Some (Vptr b ofs) ->
      exec_stmt ge e le  m f_strlen.(fn_body) t le' m (Out_return (Some ((Vint len),tuint))).
Admitted.

(* Conditions about the f_strlen loop: an illustration *)

(* On empty string C light function evaluates to 0 *)
Lemma strlen_correct_loop_empty_string :
  forall ge e m b ofs le,                                           
    strlen m b ofs O ->

    exists t le',
      le!_output = Some (VintN O) ->
      le!_input = Some (Vptr b ofs) ->
      exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (VintN O).
Proof.
  intros.
  replace O with (0 + 0)%nat by lia.
  replace ofs with (Ptrofs.add ofs Ptrofs.zero) by (auto with ptrofs).
  eapply strlen_loop_correct_gen.
  simpl.
  assumption.
Qed.   

(* If 0 is read from memory at [b,ofs + len] the output is set to len *)
Lemma strlen_loop_break_correct:  forall ge e m b ofs outp le,      
      ofs + Z.of_nat outp < Ptrofs.modulus ->
      0 <= ofs < Ptrofs.modulus ->
      0 <= Z.of_nat outp < Ptrofs.modulus ->

      (* IF before the loop *s = [b,ofs + outp] and i = outp *)
      le!_input = Some (Vptr b (Ptrofs.repr (ofs + Z.of_nat outp))) ->
      le!_output = Some (VintN outp) ->
      
      (* and the guard condition is false *)
      Mem.load Mint8signed m b (ofs + (Z_of_nat outp)) = Some (Vint (Int.repr 0)) ->

      (* THEN loop executes to an environment with i = outp [i.e., i stays unchanged] + memory is unchanged *)
      exists t le', exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ (le'!_output) = Some (VintN outp).
Proof.
  intros.
  repeat eexists.
  eapply exec_Sloop_stop1.
  seq2. seq1. seq1.
  repeat econstructor.
  apply H2.
  repeat econstructor.
  apply gss.
  repeat econstructor.
  seq1.
  repeat econstructor.
  rewrite gso. apply gss. cbv ; congruence.
  simpl.
  replace (Ptrofs.unsigned (Ptrofs.repr (ofs + Z.of_nat outp))) with (ofs + Z.of_nat outp).
  apply H4.
  { ptrofs_compute_add_mul. all: lia. }
  repeat econstructor.
  apply gss.
  econstructor.
  replace (negb (Int.eq Int.zero Int.zero)) with false by (auto with ints).
  econstructor.
  cbv; congruence.
  econstructor.
  repeat (rewrite gso). assumption.
  all: cbv; congruence.
Qed.

   
Lemma strlen_loop_body_correct: Archi.ptr64 = false -> forall len ge e m b ofs le,
      0 <= ofs < Ptrofs.modulus ->
      Z_of_nat len < Int.modulus ->
      ofs + Z_of_nat len < Ptrofs.modulus ->
                       
      le!_input = Some (Vptr b (Ptrofs.repr (ofs + Z.of_nat len))) ->
      le!_output = Some (VintN len) ->
    
      (exists c, Mem.load chunk m b (ofs + Z.of_nat len) = Some (Vint c) /\c <> Int.zero) ->
                                         
      exists t le', exec_stmt ge e le m f_strlen_loop_body t le' m Out_normal /\ le'!_output = Some (VintN (S len)).
Proof.
  intros.
  destruct H5 as [p].
  repeat eexists.
  repeat seq1.
  repeat econstructor. apply H3. repeat econstructor.
  apply gss.
  repeat econstructor.
  repeat econstructor.
  rewrite gso. apply gss. cbv; congruence.
  simpl.
  replace (Ptrofs.unsigned (Ptrofs.repr (ofs + Z.of_nat len))) with (ofs + Z.of_nat len). 
  apply H5.
  { ptrofs_compute_add_mul. all: lia. }
  repeat econstructor.
  apply gss.
  econstructor.
  replace (negb (Int.eq p Int.zero)) with true.
  repeat econstructor.
  { replace (Int.eq p Int.zero) with false.
          auto.
          rewrite Int.eq_false.
          reflexivity.
          apply H5. }
  repeat econstructor.
  repeat (rewrite gso).
  apply H4. 1-3: cbv; congruence.
  repeat econstructor.
  unfold VintN.
  replace (Int.add (Int.repr (Z.of_nat len)) (Int.repr 1)) with (Int.repr (Z.of_nat (S len))). 
  apply gss.
  { ints_compute_add_mul.
    f_equal.
    lia.
    split; try lia. cbv; auto.
    lia. }
Qed.
               

