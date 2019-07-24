From Coq Require Import String List ZArith Lia.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events Memory.

Local Open Scope Z_scope.

Definition _s : ident := 54%positive.
Definition _str : ident := 53%positive.

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
      (Sifthenelse (Ederef (Etempvar _s (tptr tschar)) tschar) Sskip Sbreak)
      (Sset _s
        (Ebinop Oadd (Etempvar _s (tptr tschar))
          (Econst_int (Int.repr 1) tint) (tptr tschar)))))
  (Sreturn (Some (Ebinop Osub (Etempvar _s (tptr tschar))
                   (Etempvar _str (tptr tschar)) tint))))
|}.

Definition f_strlen_loop :=
  (Sloop
    (Sifthenelse (Ederef (Etempvar _s (tptr tschar)) tschar) Sskip Sbreak)
    (Sset _s
      (Ebinop Oadd (Etempvar _s (tptr tschar))
        (Econst_int (Int.repr 1) tint) (tptr tschar)))).

Definition VintZ (z : Z) := Vint (Int.repr z).
Definition VintN (n : nat) := Vint (Int.repr (Z_of_nat n)).

(* relational specification of strlen *)
Inductive strlen_rspec (m : mem) (b : block) (ofs : ptrofs) : nat -> Prop :=
| LengthZero:
    Mem.loadv Mint8signed m (Vptr b ofs) = Some (Vint Int.zero) ->
    strlen_rspec m b ofs 0
| LengthSucc:
    forall n c,
    Z.of_nat (S n) < Int.modulus ->
    Ptrofs.unsigned ofs + 1 < Ptrofs.modulus ->
    Mem.loadv Mint8signed m (Vptr b ofs)  = Some (Vint c) ->
    Int.eq c Int.zero = false ->
    strlen_rspec m b (Ptrofs.add ofs Ptrofs.one) n ->
    strlen_rspec m b ofs (S n).

Ltac gso := rewrite PTree.gso by discriminate.
Ltac gss := rewrite PTree.gss.

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

Fact char_not_zero (c : int) :
  c <> Int.zero ->
  negb (Int.eq c Int.zero) = true.
Proof.
  intro.
  rewrite Int.eq_false by assumption.
  reflexivity.
Qed.  

(* add more lemmas to ptrofs hints *)
Hint Resolve Ptrofs.mul_one Ptrofs.add_zero : ptrofs.

Parameter ge : genv.
Parameter e : env.

(** * Helper lemmas *)

Definition ofs_of_nat (n : nat) := Ptrofs.repr (Z.of_nat n).

  

Lemma x : forall ofs i,
  Z.of_nat i < Int.modulus ->
  Ptrofs.add (Ptrofs.add ofs (ofs_of_nat i)) Ptrofs.one =
  Ptrofs.add ofs (ofs_of_nat (S i)).
Proof.
  replace Int.modulus
    with Ptrofs.modulus
    by reflexivity.
  intros.
  unfold ofs_of_nat.
  rewrite Nat2Z.inj_succ, Ptrofs.add_assoc.
  replace  (Z.succ (Z.of_nat i)) with ((Z.of_nat i) + 1) by (auto with zarith).
  unfold Ptrofs.one.
  f_equal.
  ptrofs_compute_add_mul; try nia.
  reflexivity.
Admitted.

Lemma x1 : forall ofs i,
  Z.of_nat i < Int.modulus ->
  Ptrofs.add (Ptrofs.add ofs Ptrofs.one) (ofs_of_nat i) =
  Ptrofs.add ofs (ofs_of_nat (S i)).
Proof.
  replace Int.modulus
    with Ptrofs.modulus
    by reflexivity.
  intros.
  unfold ofs_of_nat.
  rewrite Nat2Z.inj_succ, Ptrofs.add_assoc.
  replace  (Z.succ (Z.of_nat i)) with ((Z.of_nat i) + 1) by (auto with zarith).
  unfold Ptrofs.one.
  f_equal.
  ptrofs_compute_add_mul; try nia.
  rewrite Z.add_comm.
  reflexivity.
Admitted.

  

(*
 * if strlen on [b + ofs] is [len],
 * then strlen on [b + ofs + len] is 0
 *)
Lemma strlen_to_len_0 :
  forall len m b ofs,
    strlen_rspec m b ofs len ->
    strlen_rspec m b (Ptrofs.add ofs (ofs_of_nat len)) 0.
Proof.
  induction len; intros.
  - replace (ofs_of_nat 0) with Ptrofs.zero by reflexivity.
    replace (Ptrofs.add ofs Ptrofs.zero) with ofs by (auto with ptrofs).
    assumption.
  - inversion_clear H.
    rewrite <-x1 by lia.
    apply IHlen.
    assumption.
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
         exists c,
           Int.eq c Int.zero = false /\
           Mem.loadv Mint8signed m (Vptr b (Ptrofs.add ofs (ofs_of_nat i))) = Some (Vint c).
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
      replace (Ptrofs.add ofs (ofs_of_nat (S i)))
        with (Ptrofs.add (Ptrofs.add ofs Ptrofs.one) (ofs_of_nat i)).
      apply IHlen; [assumption | lia].
      rewrite x1 by lia.
      reflexivity.
Qed.

(** * correctness *)

Lemma strlen_loop_correct :
  forall len m b ofs le i,
    strlen_rspec m b ofs (len + i) ->   
    exists t le',
      le!_str = Some (Vptr b ofs) ->
      le!_s = Some (Vptr b (Ptrofs.add ofs (ofs_of_nat i))) ->
      exec_stmt ge e le m f_strlen_loop t le' m Out_normal
      /\
      le'!_s = Some (Vptr b (Ptrofs.add ofs (ofs_of_nat (len + i)))).
Proof.
  induction len; intros.
  - (* iBase *)
    repeat eexists.
    eapply exec_Sloop_stop1.
    repeat econstructor.
    2: apply strlen_to_len_0 in H; inversion_clear H.
    all: try eassumption.
    all: try econstructor.
  - (* iStep *)
    assert (i < S len + i)%nat by lia.
    pose proof strlen_to_mem _ _ _ _ H _ H0 as HM; clear H0.
    destruct HM as [c HM]; destruct HM as [HM1 HM2].
    pose proof strlen_to_len_0 _ _ _ _ H as HO.
    inversion H; subst.
    

    remember (PTree.set _s (Vptr b (Ptrofs.add (Ptrofs.add ofs (ofs_of_nat i)) Ptrofs.one)) le)
      as X.
    replace (S len + i)%nat with (len + S i)%nat in * by lia.
    pose proof IHlen m b ofs X (S i) H as IH.
    destruct IH as [t' IH]; destruct IH as [le'' IH].


    
    repeat eexists.
    + (* stmt *)
      eapply exec_Sloop_loop.
      repeat econstructor.
      eassumption.
      eassumption.
      econstructor.
      rewrite HM1.
      econstructor.
      constructor.
      repeat econstructor.
      eassumption.
      econstructor.
 
      fold f_strlen_loop.
      replace (Ptrofs.mul (Ptrofs.repr (sizeof ge tschar)) (ptrofs_of_int Signed (Int.repr 1)))
        with Ptrofs.one
        by (auto with ptrofs).
      rewrite <-HeqX.
 
 
 
 
      destruct IH.
      subst; gso; assumption.
      subst; gss. rewrite x by lia; reflexivity.
      eassumption.
 
    + destruct IH.
      subst; gso; assumption.
      subst; gss; rewrite x by lia; reflexivity.
      assumption.
Qed.

