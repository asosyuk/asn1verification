From Coq Require Import String List ZArith Lia.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events Memory.
Open Scope Z_scope.

Definition _s : ident := 54%positive.
Definition _str : ident := 53%positive.
Definition _strlen : ident := 55%positive.
(* Definition _t : ident := 57%positive. *)

Definition f_strlen := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_s, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _s (Etempvar _str (tptr tschar)))
    (Sloop
    (* we don't need temporary variable _t *)
    (Sifthenelse (Ederef (Etempvar _s (tptr tschar)) tschar) Sskip Sbreak)
      (Sset _s
        (* add 1 to pointer _s *)
        (Ebinop Oadd (Etempvar _s (tptr tschar))
          (Econst_int (Int.repr 1) tint) (tptr tschar)))))
  (* return result of substraction of _s with original pointer _str, 
     with equals to 'len' *)
  (Sreturn (Some (Ebinop Osub (Etempvar _s (tptr tschar))
                   (Etempvar _str (tptr tschar)) tint))))
|}.

Definition f_strlen_loop := 
    (Sloop
    (* we don't need temporary variable _t *)
    (Sifthenelse (Ederef (Etempvar _s (tptr tschar)) tschar) Sskip Sbreak)
      (Sset _s
        (* add 1 to pointer _s *)
        (Ebinop Oadd (Etempvar _s (tptr tschar))
          (Econst_int (Int.repr 1) tint) (tptr tschar)))).


Inductive strlen_spec (m : mem) (b : block) (ofs : ptrofs) : nat -> Prop :=
| LengthZero:
    Mem.loadv Mint8signed m (Vptr b ofs) = Some (Vint Int.zero) ->
    strlen_spec m b ofs 0
| LengthSucc:
    forall n c,
    Z.of_nat (S n) < Int.modulus ->
    Ptrofs.unsigned ofs + 1 < Ptrofs.modulus ->
    Mem.loadv Mint8signed m (Vptr b ofs)  = Some (Vint c) ->
    Int.eq c Int.zero = false ->
    strlen_spec m b (Ptrofs.add ofs Ptrofs.one) n ->
    strlen_spec m b ofs (S n).

Definition nat_to_ofs (n : nat) := Ptrofs.repr (Z.of_nat n).

Hint Resolve Ptrofs.mul_one Ptrofs.add_zero : ptrofs.

Notation "x +* y" := (Ptrofs.add x y) (at level 80, right associativity).

Lemma ofs_succ_l : forall ofs i,
  Z.of_nat i < Int.modulus ->
  ((ofs +* (nat_to_ofs i)) +* Ptrofs.one) =
  (ofs +* (nat_to_ofs (S i))).
Proof.
  intros.
  rewrite Ptrofs.add_assoc.
  f_equal.
  unfold nat_to_ofs, Ptrofs.add, Ptrofs.one, Ptrofs.mul.
  rewrite Nat2Z.inj_succ.
  rewrite Ptrofs.unsigned_repr_eq.
  rewrite Zmod_small.
  reflexivity.
  replace Ptrofs.modulus with Int.modulus by reflexivity.
  lia.
Qed.

Lemma ofs_succ_r : forall ofs i,
  Z.of_nat i < Int.modulus ->
  ((ofs +* Ptrofs.one) +* (nat_to_ofs i)) =
  (ofs +* (nat_to_ofs (S i))).
Proof.
  intros.
  rewrite <-ofs_succ_l by assumption.
  rewrite Ptrofs.add_assoc, Ptrofs.add_assoc.
  f_equal.
  apply Ptrofs.add_commut.
Qed.

Lemma strlen_to_mem_0 :
  forall len m b ofs,
    strlen_spec m b ofs len ->
    strlen_spec m b (ofs +* (nat_to_ofs len)) 0.
Proof.
  induction len.
  all: intros.
  - 
    replace (nat_to_ofs 0) with Ptrofs.zero by reflexivity.
    rewrite Ptrofs.add_zero.
    assumption.
  - 
    inversion H.
    rewrite <-ofs_succ_r by lia.
    apply IHlen.
    assumption.
Qed.

Lemma strlen_to_mem :
  forall len m b ofs,
    strlen_spec m b ofs len ->
    forall i, (i < len)%nat ->
         exists c, Int.eq c Int.zero = false /\
           Mem.loadv Mint8signed m (Vptr b 
             (ofs +* (nat_to_ofs i))) = Some (Vint c).
Proof .
  induction len. 
  all: intros.
  - lia.
  - 
    destruct i. 
    all: inversion H.
    * 
      exists c.
      split.
      assumption.
      rewrite Ptrofs.add_zero.
      assumption.
    * 
      replace (ofs +* (nat_to_ofs (S i)))
        with ((ofs +* Ptrofs.one) +* (nat_to_ofs i)).
      apply IHlen.
      assumption.
      apply lt_S_n.
      assumption.
      rewrite ofs_succ_r by lia.
      reflexivity.
Qed.

Lemma strlen_loop_correct_gen :
  forall len i m b ofs ge e te,
    strlen_spec m b ofs (len + i) ->   
    exists t te',
      te ! _str = Some (Vptr b ofs) ->
      te ! _s = Some (Vptr b (ofs +* (nat_to_ofs i))) ->
      exec_stmt ge e te m f_strlen_loop t te' m Out_normal
      /\ te' ! _s = Some (Vptr b (ofs +* (nat_to_ofs (len + i))))
      /\ te' ! _str = Some (Vptr b ofs) .
Proof.
  induction len; intros.
  - 
    repeat eexists.
    eapply exec_Sloop_stop1.
    repeat econstructor.
    all: try eassumption.
    apply strlen_to_mem_0 in H.
    inversion_clear H.
    eassumption.
    econstructor.
    repeat econstructor.
    constructor.
  - 
    assert (T : (i < S len + i)%nat) by lia.
    pose proof strlen_to_mem _ _ _ _ H _ T as HM; clear T.
    destruct HM as [c HM]; destruct HM as [HM1 HM2].
    pose proof strlen_to_mem_0 _ _ _ _ H as HO.
    replace (S len + i)%nat with (len + S i)%nat in * by lia.
    (* starting env *)
    remember (PTree.set _s 
               (Vptr b (Ptrofs.add 
               (Ptrofs.add ofs (nat_to_ofs i)) Ptrofs.one)) te)
      as Ite.
    inversion H; try lia.
    assert (Z.of_nat (S i) < Int.modulus) by lia.
    pose proof IHlen (S i) m b ofs ge e Ite H as IH.
    clear IHlen.
    destruct IH as [t' IH]. 
    destruct IH as [te' IH].
    eexists.
    eexists.
    intros.
    destruct IH.
    subst; rewrite PTree.gso by discriminate.
    eassumption.
    subst; rewrite PTree.gss; rewrite ofs_succ_l by lia; reflexivity.
    destruct H10; split;[| split].
    eapply exec_Sloop_loop.
    repeat econstructor.
    eassumption.
    eassumption.
    econstructor.
    rewrite HM1.
    simpl.
    econstructor.
    constructor.
    repeat econstructor.
    eassumption.
    econstructor.
    fold f_strlen_loop.
    replace (Ptrofs.mul (Ptrofs.repr (sizeof ge tschar)) 
                        (ptrofs_of_int Signed (Int.repr 1))) with (Ptrofs.one) by (auto with ptrofs).
    rewrite <-HeqIte.
    eapply H9.
    rewrite H0.
    assumption.
    assumption.
Qed.

Theorem strlen_correct : forall len m b ofs ge e te,
  strlen_spec m b ofs len ->
  te ! _str = Some (Vptr b ofs) ->
  exists t te',
    exec_stmt ge e te m (fn_body f_strlen) t te' m 
              (Out_return (Some (Vptrofs (nat_to_ofs len), tint))).
Proof.
  intros.
  replace (len) with (len + 0)%nat in H by lia.
  pose proof strlen_loop_correct_gen len 0%nat m b ofs ge e (PTree.set _s (Vptr b ofs) te) H.
  destruct H1 as [t' HM].
  destruct HM as [te' HM].
  repeat eexists.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  eassumption.
  fold f_strlen_loop.
  destruct HM.
  rewrite PTree.gso by discriminate.
  eassumption.
  rewrite PTree.gss.
  replace (ofs +* nat_to_ofs 0) with (ofs) by (auto with ptrofs).
  reflexivity.
  eassumption.
  econstructor.
  econstructor.
  econstructor.
  all: destruct HM.
  1,4,7: rewrite PTree.gso by discriminate.
  all: try eassumption.
  1,3,5: rewrite PTree.gss.
  all: try replace (ofs +* nat_to_ofs 0) with (ofs) by (auto with ptrofs).
  all: try reflexivity.
  all: destruct H2.
  eassumption.
  econstructor.
  eassumption.
  replace (len + 0)%nat with len by lia.
  cbn.
  unfold proj_sumbool.
  destruct Archi.ptr64 eqn:kek.
  all: destruct zle.
  1,3: destruct eq_block.
  rewrite Ptrofs.sub_add_l.
  rewrite Ptrofs.sub_idem.
  rewrite Ptrofs.add_zero_l.
  rewrite Ptrofs.divs_one.
  reflexivity.
  unfold Ptrofs.zwordsize, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
  rewrite kek.
  lia.
  contradict n; reflexivity.
  rewrite Ptrofs.sub_add_l.
  rewrite Ptrofs.sub_idem.
  rewrite Ptrofs.add_zero_l.
  rewrite Ptrofs.divs_one.
  reflexivity.
  unfold Ptrofs.zwordsize, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
  rewrite kek.
  lia.
  contradict n; reflexivity.

  contradict g.
  unfold Ptrofs.max_signed, Ptrofs.half_modulus, Ptrofs.modulus.
  unfold Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
  rewrite kek.
  simpl.
  lia.
  contradict g.
  unfold Ptrofs.max_signed, Ptrofs.half_modulus, Ptrofs.modulus.
  unfold Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
  rewrite kek.
  simpl.
  lia.
Qed.

Close Scope Z.
