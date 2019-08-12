From Coq Require Import String List ZArith Lia.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events Memory.

Require Import Clight.strlen.

Open Scope Z_scope.


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
  forall len m b ofs, strlen_rspec m b ofs len -> forall i, (i < len)%nat ->
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

Fact ptr_max_signed_lower_bound :
  2147483647 <= Ptrofs.max_signed.
Proof.
  unfold Ptrofs.max_signed, Ptrofs.half_modulus, Ptrofs.modulus,
    Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
  destruct Archi.ptr64; simpl; lia.
Qed.

Fact ptr_zwordsize_lower_bound :
 32 <= Ptrofs.zwordsize.
Proof.
  unfold Ptrofs.zwordsize, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
  destruct Archi.ptr64; simpl; lia.
Qed.


(** * correctness *)

(* loop isolated *)
Definition f_strlen_loop :=
  (Sloop
    (Sifthenelse (Ederef (Etempvar _s (tptr tschar)) tschar) Sskip Sbreak)
    (Sset _s
      (Ebinop Oadd (Etempvar _s (tptr tschar))
        (Econst_int (Int.repr 1) tint) (tptr tschar)))).

(*
 * correctness of the loop in isolation.
 * in addition to proving correctness of result
 * we also prove preservation of [str]:
 * that is required because [str] is used again in the return statement
 *)
Lemma f_strlen_loop_correct :
  forall len ge e m b ofs ste i,
    strlen_rspec m b ofs (len + i) ->   
    exists t rte,
      ste ! _str = Some (Vptr b ofs) ->
      ste ! _s = Some (Vptr b (Ptrofs.add ofs (ofs_of_nat i))) ->

      exec_stmt ge e ste m f_strlen_loop t rte m Out_normal
      /\
      rte ! _s = Some (Vptr b (Ptrofs.add ofs (ofs_of_nat (len + i))))
      /\
      rte ! _str = ste ! _str.
Proof.
  induction len; intros.
  - (** iBase *)
    apply strlen_to_len_0 in H; inversion_clear H.
    repeat eexists.
    eapply exec_Sloop_stop1.
    repeat econstructor.
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
    remember (PTree.set _s (Vptr b (Ptrofs.add (Ptrofs.add ofs (ofs_of_nat i)) Ptrofs.one)) ste)
      as sIte.
    pose proof IHlen ge e m b ofs sIte (S i) H as IH;
      clear IHlen;
      destruct IH as [t IH]; destruct IH as [rIte IH].

    eexists; eexists; intros.

    (* split induction hypothesis *)
    destruct IH as [IH1 IH];
      [subst; gso_simpl; assumption
      | subst; gss_simpl; inversion H; rewrite ofs_succ_l by lia; reflexivity
      |].
    destruct IH as [IH2 IH3].

    split.
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
      subst.
      eassumption.
    + (* execution result *)
      split.
      assumption.
      rewrite IH3; subst; gso_simpl; reflexivity.
Qed.

(* full correctness *)
Lemma f_strlen_correct :
  forall len ge e m b ofs ste,
    strlen_rspec m b ofs len ->   
    ste ! _str = Some (Vptr b ofs) ->
    exists t rte,
      exec_stmt ge e ste m (fn_body f_strlen) t rte m
                (Out_return (Some (Vptrofs (ofs_of_nat len), tint))).
Proof.
  intros.

  (* introduce the gneralized correctness lemma *)
  pose proof f_strlen_loop_correct len ge e m b ofs (PTree.set _s (Vptr b ofs) ste) 0 as GC.
  replace (len + 0)%nat with len in * by lia.
  specialize (GC H).
  destruct GC as [t GC]; destruct GC as [le' GC].

  repeat eexists.

  (* make loop correctness lemma usable *)
  destruct GC as [GC1 GC];
    [gso_simpl; assumption
    |gss_simpl; rewrite Ptrofs.add_zero; reflexivity
    |].
  destruct GC as [GC2 GC3].
  
  (* split body into three parts *)
  econstructor. econstructor.
  - (* set *)
    repeat econstructor.
    eassumption.
  - (* loop *)
    eassumption.
  - (* return *)
    repeat econstructor.
    eassumption.
    rewrite GC3; gso_simpl; eassumption.
    cbn.
    destruct eq_block; [| contradiction].
    unfold proj_sumbool.
    destruct zle;
      [| pose proof ptr_max_signed_lower_bound; lia].
    rewrite Ptrofs.divs_one;
      [| pose proof ptr_zwordsize_lower_bound; lia].
    rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
    reflexivity.
Qed.
