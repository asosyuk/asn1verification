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



(** * relational specification of strlen *)

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



(** * Helper lemmas and definitions *)

Parameter ge : genv.
Parameter e : env.

Definition ofs_of_nat (n : nat) := Ptrofs.repr (Z.of_nat n).

(* add more lemmas to ptrofs hints *)
Hint Resolve Ptrofs.mul_one Ptrofs.add_zero : ptrofs.

Ltac gso_simpl := rewrite PTree.gso by discriminate.
Ltac gss_simpl := rewrite PTree.gss.

(*
 * helper for pointer arithmetic
 * the first two requirements are technical:
 * true in all but corner cases
*)
Fact ofs_succ_l : forall ofs i,
  1 < Int.modulus ->
  Z.of_nat i < Int.modulus ->
  Ptrofs.add (Ptrofs.add ofs (ofs_of_nat i)) Ptrofs.one =
  Ptrofs.add ofs (ofs_of_nat (S i)).
Proof.
  intros.
  rewrite Ptrofs.add_assoc.
  f_equal.
  unfold ofs_of_nat, Ptrofs.one, Ptrofs.add, Ptrofs.mul.
  rewrite Nat2Z.inj_succ, Ptrofs.unsigned_repr_eq, Zmod_small.
  reflexivity.
  replace Ptrofs.modulus with Int.modulus by reflexivity.
  nia.
Qed.

Fact ofs_succ_r : forall ofs i,
  1 < Int.modulus ->
  Z.of_nat i < Int.modulus ->
  Ptrofs.add (Ptrofs.add ofs Ptrofs.one) (ofs_of_nat i) =
  Ptrofs.add ofs (ofs_of_nat (S i)).
Proof.
  intros.
  rewrite <-ofs_succ_l by assumption.
  rewrite Ptrofs.add_assoc, Ptrofs.add_assoc.
  f_equal.
  apply Ptrofs.add_commut.
Qed.

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
    rewrite <-ofs_succ_r by lia.
    apply IHlen.
    assumption.
Qed.

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
      rewrite ofs_succ_r by lia.
      reflexivity.
Qed.



(** * correctness *)

Lemma strlen_loop_correct_gen :
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
  - (** iBase *)
    repeat eexists.
    eapply exec_Sloop_stop1.
    repeat econstructor.
    2: apply strlen_to_len_0 in H; inversion_clear H.
    all: try eassumption.
    all: try econstructor.
  - (** iStep *)
    (** introduce properties of [strlen_rspec] *)
    assert (T : (i < S len + i)%nat) by lia;
      pose proof strlen_to_mem _ _ _ _ H _ T as HM;
      clear T;
      destruct HM as [c HM]; destruct HM as [HM1 HM2].
    pose proof strlen_to_len_0 _ _ _ _ H as HO.

    (** prepare the induction hypothesis for use *)
    (* cannot work with [S len] but can with [S i] *)
    replace (S len + i)%nat with (len + S i)%nat in * by lia.
    (* this is the starting state of the iteration on the induction step *)
    remember (PTree.set _s (Vptr b (Ptrofs.add (Ptrofs.add ofs (ofs_of_nat i)) Ptrofs.one)) le)
      as Ile.
    pose proof IHlen m b ofs Ile (S i) H as IH;
      clear IHlen;
      destruct IH as [t' IH]; destruct IH as [le'' IH].

    repeat eexists.

    (* make induction hypothesis useful *)
    all: destruct IH;
      [ subst; gso_simpl; assumption
      | subst; gss_simpl; inversion H; rewrite ofs_succ_l by lia; reflexivity
      |].
    + (* statment execution *)
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
      subst; eassumption.
    + (* execution result *)
      assumption.
Qed.
