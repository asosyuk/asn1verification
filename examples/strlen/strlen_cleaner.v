From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events Memory.

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

Definition chunk : memory_chunk := Mint8signed.
Definition VintZ := fun (z : Z) => Vint (Int.repr z).
Definition VintN:= fun n => Vint (Int.repr (Z_of_nat n)).

Inductive strlen_rspec (m : mem) (b : block) (ofs : ptrofs) : nat -> Prop :=
| LengthZero:
    Mem.loadv chunk m (Vptr b ofs) = Some (Vint Int.zero) ->
    strlen_rspec m b ofs 0
| LengthSucc:
    forall n c,
    Z.of_nat (S n) < Int.modulus ->
    Ptrofs.unsigned ofs + 1 < Ptrofs.modulus ->
    Mem.loadv chunk m (Vptr b ofs)  = Some (Vint c) ->
    c <> Int.zero ->
    strlen_rspec m b (Ptrofs.add ofs Ptrofs.one) n ->
    strlen_rspec m b ofs (S n).

Ltac gso := rewrite PTree.gso by discriminate.
Ltac gss := apply PTree.gss.

(* 
 * Tactics for arithmetic on ptrofs, now they are ad hoc.
 * TODO: automatize translation from ptrofs to Z
 *)

Ltac ints_to_Z :=
  repeat rewrite Int.unsigned_repr_eq;
  repeat rewrite Zmod_small.

Ltac ptrofs_to_Z :=
  repeat rewrite Ptrofs.unsigned_repr_eq;
  repeat rewrite Zmod_small.

Ltac ptrofs_compute_add_mul :=
  simpl; unfold Ptrofs.add, Ptrofs.mul, Ptrofs.of_intu, Ptrofs.of_int;
  repeat rewrite Ptrofs.unsigned_repr_eq;
  repeat rewrite Int.unsigned_repr_eq;
  repeat rewrite Zmod_small.

Ltac ints_compute_add_mul :=
  simpl; unfold Int.add, Int.mul;
  repeat rewrite Int.unsigned_repr_eq;
  repeat rewrite Int.unsigned_repr_eq;
  repeat rewrite Zmod_small.

(* can make more generic to repeatedly apply gso *)
(*
Ltac gso_assumption :=
  match goal with
  | [ H : ?P ! ?I = Some ?W |- (PTree.set _ _ ?P) ! ?I = Some ?Z ] => rewrite gso  
  | [ H : ?P ! ?Q = Some ?W |-  ?P ! ?Q = Some ?Z ] => apply H
  | [ |- _ <> _ ] => cbv ; congruence
  end.
*)

Fact char_not_zero (c : int) :
  c <> Int.zero ->
  negb (Int.eq c Int.zero) = true.
Proof.
  intro.
  rewrite Int.eq_false by assumption.
  reflexivity.
Qed.  

Fact int_ptrofs_mod_eq : Int.modulus = Ptrofs.modulus.
Proof. reflexivity. Qed.

(* add more lemmas to ptrofs hints *)
Hint Resolve Ptrofs.mul_one Ptrofs.add_zero int_ptrofs_mod_eq : ptrofs.

Parameter ge : genv.
Parameter e : env.

(** * Helper lemmas about the specification *)

(*
 * if strlen on [b + ofs] is [len],
 * then strlen on [b + ofs + len] is 0
 *)
Lemma strlen_to_len_0 :
  forall len m b ofs,
    strlen_rspec m b ofs len ->
    strlen_rspec m b (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat len))) 0.
Proof.
  induction len; intros.
  - simpl.
    replace (Ptrofs.repr 0) with Ptrofs.zero by (auto with ptrofs).
    replace (Ptrofs.add ofs Ptrofs.zero) with ofs by (auto with ptrofs).
    assumption.
  - inversion_clear H.
    replace
      (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat (S len))))
      with
      (Ptrofs.add (Ptrofs.add ofs Ptrofs.one) (Ptrofs.repr (Z.of_nat len))).
    apply IHlen; assumption.
    {
      rewrite Nat2Z.inj_succ, Ptrofs.add_assoc.
      replace  (Z.succ (Z.of_nat len)) with ((Z.of_nat len) + 1) by (auto with zarith).
      unfold Ptrofs.one.
      f_equal.
      ptrofs_compute_add_mul.
      all: pose proof int_ptrofs_mod_eq; try nia.
      f_equal.
      auto with zarith.
    }
Qed.

Fact Ptrofs_zero_nat_O :
  Ptrofs.repr (Z.of_nat 0) = Ptrofs.zero.
Proof. reflexivity. Qed.

(*
 * if strlen on [b + ofs] is [len],
 * then all chars on [b + ofs + i], [i < len] are non-nil
 *)
Lemma strlen_to_mem :
  forall len m b ofs,
    strlen_rspec m b ofs len ->
    forall i, (i < len)%nat ->
         exists c, c <> Int.zero /\
              Mem.loadv chunk m (Vptr b (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i)))) = Some (Vint c).
Proof.
  induction len; intros.
  - lia.
  - intros.
    destruct i; inversion_clear H.
    + exists c.
      split; [try assumption |].
      rewrite Ptrofs.add_zero.
      assumption.
    + specialize IHlen with (ofs := (Ptrofs.add ofs Ptrofs.one)).
      replace (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat (S i))))
        with (Ptrofs.add (Ptrofs.add ofs Ptrofs.one) (Ptrofs.repr (Z.of_nat i))).
      apply IHlen; [assumption | lia].
      {
        pose proof int_ptrofs_mod_eq.
        unfold Ptrofs.one.
        ptrofs_compute_add_mul.
        f_equal.
        all: try lia.
        destruct ofs; simpl in *; nia.
      }
Qed.

(* Correctness statements *)

(* A generalization of loop correctness *)
Lemma strlen_loop_correct_gen :
  forall len i m b ofs le,
    strlen_rspec m b ofs (len + i) ->   
    exists t le',
      le!_output = Some (VintN i) ->
      le!_input = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i)))) ->
      exec_stmt ge e le m f_strlen_loop t le' m Out_normal
      /\
      le'!_output = Some (VintN (len + i)).
Proof.
  induction len; intros.
  - (* Base case *)    
    simpl in H.
    repeat eexists.
    (* Exit the loop *)
    eapply exec_Sloop_stop1.
    eapply exec_Sseq_2.
    repeat econstructor.
    eassumption.
    gss.
    repeat econstructor.
    gso. gss.
    (* Derive memory assumptions from the specification *)
    pose (Spec_mem := strlen_to_len_0 i m b ofs H).
    inversion_clear Spec_mem.
    apply H2.
    gss.
    econstructor.
    replace (negb (Int.eq Int.zero Int.zero)) with false by (auto with ints).      
    econstructor.
    cbv; congruence. econstructor.
    repeat (rewrite gso).
    replace (0 + i)%nat with i by lia.
    repeat gso; assumption.
  - (* Ind. Step *)
    pose proof H as M.
    apply strlen_to_mem with (i := i) in M; [| lia].
    destruct M as [c M].
    (* apply I.H. to le' after one step when starting with i and [b,ofs + i]  *)
    pose (le'' :=
            (PTree.set _output (VintN (S i))
              (PTree.set _t'2 (Vint c)
                (PTree.set _input (Vptr b  (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat (S i)))))
                  (PTree.set _t'1 (Vptr b  (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i))))
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
Lemma strlen_loop_correct :
  forall len m b ofs le,
    strlen m b ofs len ->
    exists t le',
      le!_output = Some (VintN O) ->
      le!_input = Some (Vptr b ofs) ->
      exec_stmt ge e le m f_strlen_loop t le' m Out_normal
      /\
      le'!_output = Some (VintN len).
Proof.
  intros.
  replace ofs with (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat O))) by (auto with ptrofs).
  replace len with (len + O)%nat by lia.
  eapply strlen_loop_correct_gen.
  replace (len + O)%nat with len by omega.
  assumption.
Qed.
  
(* Full correctness statement *)
Lemma strlen_correct: forall len m b ofs le,
    strlen m b ofs len ->
    exists t le',
      le!_input = Some (Vptr b ofs) ->
      exec_stmt ge e le m f_strlen.(fn_body) t le' m (Out_return (Some ((VintN len),tuint))).
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
