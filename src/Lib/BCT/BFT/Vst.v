Require Import Core.Core Core.StructNormalizer VstLib.
Require Import VST.floyd.proofauto.
(* Require Import BFT.Exec. *)
Require Import Clight.ber_tlv_tag.
Require Import Core.Notations Core.SepLemmas Core.Tactics Core.VstTactics.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
 
Open Scope int.

Fixpoint range n :=
  match n with 
  | O => []
  | S m => range m ++ [m]
  end.

Fixpoint index {A} (f : A -> bool) ls l :=
  match ls with
  | [] => None
  | x :: tl => if f x then Some (l - len tl)%Z else index f tl l
  end.

Definition append_val ls 
  := (fun x y => (x << Int.repr 7) or (Znth (Z.of_nat y) ls & Int.repr 127)). 
  
Definition bft_loop ls size tclass := 
  let n := index (fun h => (h & Int.repr 128) == 0) 
              ls (len ls - 1) in
  let v := fold_left (append_val ls)
                     (range (Z.to_nat size)) 0 in
  match n with
    | None => (0%Z, v)
    | Some n => if (n + 2) <=? size
                then               
                ((n + 2)%Z, v << Int.repr 2 or tclass)
                else (0%Z, v)
  end.

(*
Definition append_val ls size sizeofval 
  := (fun x y => 
        if ((Z.of_nat y <=? size) ||
             ((x >> Int.repr (8 * sizeofval - 9))%int == 0))%bool
        then
          (x << Int.repr 7)
            or (nth y ls 0 & Int.repr 127)
        else x). 

Eval cbn in (let ls := [0; 1; Int.repr 2; Int.repr 3] in
             fold_left (append_val ls 4 (sizeof tuint)) 
                       (range (length ls - 1)%nat) 0).

Definition bft_loop ls size tclass := 
  let n := index (fun h => (h & Int.repr 128) == 0) 
              ls (size - 1)%Z in
  let v := fold_left (append_val ls size (sizeof tuint))
                             (range (Z.to_nat size - 1)%nat) 0 in
  if eq_dec (v >> Int.repr (8 * sizeof tuint - 9)) 0%int 
  then 
  match n with
    | None => (0%Z, v)
    | Some n => if n <=? size
                then               
                (n, v << Int.repr 2 or tclass)
                else (0%Z, v)
  end
  else (-1, v).


Fixpoint bft_loop' v (ptr : list int) skip (size : Z) tclass (sizeofval : Z)  := 
  match ptr with
    | [] => (0%Z, v)
    | h :: tl => 
      if skip <=? size then
      if eq_dec (h & Int.repr 128) 0 
      then (skip, (v << Int.repr 7) or h)
      else 
        let v := (v << Int.repr 7) or (h & Int.repr 127) in 
        if eq_dec (v >> Int.repr (8 * sizeofval - 9)) 0
        then let (r, v) := bft_loop' v tl (skip + 1)%Z size tclass sizeofval in
             (r, v << Int.repr 2 or tclass)
        else (-1, v)
      else (0%Z, v)
  end. 

Lemma fold_left_zero : forall n size,
    fold_left (append_val [] size 4) (range n) 0 = 0.
Proof.
  induction n; intros.
  - auto.
  - simpl.
    erewrite fold_left_app.
    erewrite IHn.
    cbn.
    unfold append_val.
    break_if; auto.
Qed.
*) 

Definition ber_fetch_tags (ptr : list int) size   :=
  if eq_dec size 0%Z
  then (0%Z, 0)
  else let val := Znth 0 ptr in 
       let tclass := val >> Int.repr 6 in 
       if eq_dec (val & Int.repr 31) (Int.repr 31)
       then bft_loop (sublist 1 (len ptr) ptr) size tclass     
       else (1%Z, ((val & Int.repr 31) << Int.repr 2) or tclass).

Open Scope Z.

Section Ber_fetch_tag.

Definition ber_fetch_tag_spec : ident * funspec :=
  DECLARE _ber_fetch_tag
    WITH b : block, i : ptrofs, 
         data : list int, size : Z, 
         tag_p : val
    PRE [tptr tvoid, tuint, tptr tuint]
      PROP (0 <= size <= Int.max_unsigned;
            Forall (fun x => 0 <= Int.unsigned x <= Byte.max_unsigned) data;
            Ptrofs.unsigned i + (Zlength data) < Ptrofs.modulus;
            0 < len data <= Int.max_unsigned;
            size < len data)
      PARAMS ((Vptr b i); Vint (Int.repr size); tag_p)
      GLOBALS ()
      SEP (data_at Tsh (tarray tuchar (Zlength data)) 
                   (map Vint data) (Vptr b i);
           data_at_ Tsh tuint tag_p)
    POST [tint]
      let r := ber_fetch_tags data size in
      PROP ()
      LOCAL (temp ret_temp (Vint (Int.repr (fst r))))
      SEP (data_at Tsh (tarray tuchar (Zlength data)) 
                   (map Vint data) (Vptr b i);
           if eq_dec (fst r) 1 
           then data_at Tsh tuint (Vint ((snd r))) tag_p
           else data_at_ Tsh tuint tag_p).

Definition Gprog := ltac:(with_library prog [ber_fetch_tag_spec]).

Lemma Znth_0_cons_sublist :  forall (ls : list int) i, 
             0 <= i < len ls ->
             Znth i ls :: sublist (i + 1) (len ls) ls = sublist i (len ls) ls.
  { intros.
    erewrite Znth_cons_sublist.
    autorewrite with sublist.
    auto. lia. }
Qed.

Theorem ber_fetch_tag : semax_body Vprog Gprog 
                                   (normalize_function f_ber_fetch_tag composites) 
                                   ber_fetch_tag_spec.
Proof.
  start_function.
  forward_if.
  forward.
  assert (data_at Tsh (tarray tuchar (len data)) (map Vint data) (Vptr b i) =
          (data_at Tsh tuchar (Vint (Znth 0 data)) (Vptr b i) *
          data_at Tsh (tarray tuchar (len data - 1)) 
                  (sublist 1 (len data) (map Vint data))
                  (Vptr b (i + 1)%ptrofs))%logic) as D.
  { erewrite split_non_empty_list 
      with (i := Vint (Znth 0 data)) 
           (j2 := len data - 1) 
           (ls' := sublist 1 (len data) (map Vint data)).
    auto. erewrite <- map_sublist;
            erewrite <- map_cons;
            f_equal; erewrite Znth_0_cons_sublist; try lia; auto.
    all: autorewrite with sublist; strip_repr. }
  erewrite D.
  Intros.
  forward.
  entailer!.
  eapply Forall_Znth with (i0 := 0) in H0; try lia.
  repeat forward.
  forward_if.
  repeat forward.
  erewrite <- D.
  unfold ber_fetch_tags.
  repeat rewrite_if_b.
  entailer!.
  repeat forward.
  (* Loop *)
  Open Scope int.
  remember ((Znth 0 data) >> Int.repr 6) as tclass.
  remember (sublist 1 (len data) data) as data'.
  match goal with
  | [ _ : _ |-  semax _ ?P ?C ?Post ] =>
    forward_loop (
               EX j : Z, EX v : int, 
                 let v := fold_left (append_val data') (range (Z.to_nat j)) 0 in
                 PROP (v >> Int.repr 23 = 0;
                       forall i, (0 <= i < j)%Z -> (Znth i data' & Int.repr 128) <> 0;
                       0 <= j + 2 <= Int.max_unsigned;
                       (0 <= j)%Z)
                 LOCAL (temp _skipped (Vint (Int.repr (2 + j)));
                        temp _ptr (Vptr b (i + Ptrofs.repr j + 1)%ptrofs);
                        temp _val (Vint v);
                        temp _t'1 (Vint (Znth 0 data & Int.repr 31)%int);
                        temp _tclass (Vint (Znth 0 data >> Int.repr 6)%int);
                        temp _size (Vint (Int.repr size));
                        temp _tag_r tag_p)
                 SEP (data_at Tsh tuchar (Vint (Znth 0 data)) (Vptr b i);
                      data_at Tsh (tarray tuchar j)
                              (map Vint (sublist 1 (j + 1) data))
                              (Vptr b (i + 1)%ptrofs);
                      data_at Tsh (tarray tuchar (len data - j - 1)) 
                              (map Vint (sublist (j + 1) (len data) data))
                              (Vptr b (i + Ptrofs.repr j + Ptrofs.repr 1)%ptrofs);
                      data_at_ Tsh tuint tag_p))
            break:
             (EX j : Z,
             let val := fold_left 
                        (append_val data)
                              (range (Z.to_nat size - 1)) 0 in
               PROP (j + 2 > size;
                    (fold_left (append_val data)
                                 (range (Z.to_nat size - 1)) 0
                                 >> Int.repr (8 * sizeof tuint - 9)) = 0;
                    (index (fun h : int => (h & Int.repr 128) == 0) 
                           (data) (len data - 1) = None)) 
               LOCAL (temp _skipped (Vint (Int.repr (2 + j)));
                      temp _ptr (Vptr b (i + Ptrofs.repr j + 1)%ptrofs);
                      temp _val (Vint val);
                      temp _t'1 (Vint (Znth 0 data & Int.repr 31)%int);
                      temp _tclass (Vint (Znth 0 data >> Int.repr 6)%int);
                      temp _size (Vint (Int.repr size));
                      temp _tag_r tag_p)
                 SEP (data_at Tsh tuchar (Vint (Znth 0 data)) (Vptr b i);
                      data_at Tsh (tarray tuchar (len data - 1)) 
                              (sublist 1 (len data) (map Vint data))
                              (Vptr b (i + 1)%ptrofs);
                      data_at Tsh tuint
                              (Vint ((val << Int.repr 2) or
                                 (Znth 0 data >> Int.repr 6)%int)) tag_p))
  end.
  -- (* PRE to LI *) 
    Arguments eq_dec : simpl never.
    Exists 0%Z 0.
    autorewrite with sublist.
    entailer!.
    intros. 
    lia.
    erewrite data_at_zero_array_eq; auto.
    repeat erewrite sublist_map.
    entailer!.
  -- (* LI C LI *)
    Intros j v.
    forward_if.
    erewrite  Heqdata'.
    ++ 
      assert (data_at Tsh (tarray tuchar (len data - j - 1))
                      (sublist (j + 1) (len data) (map Vint data))
                      (Vptr b (i + Ptrofs.repr j + 1)%ptrofs) =
              (data_at Tsh tuchar
                   (Vint (Znth j (sublist 1 (len data) data))) 
                   (Vptr b (i + Ptrofs.repr j + 1)%ptrofs) *
               data_at Tsh (tarray tuchar (len data - j - 2)) 
                       (sublist (j + 1 + 1) (len data) (map Vint data))
                       (Vptr b (i + Ptrofs.repr j + 1 + 1)%ptrofs))%logic) as D2.
  { erewrite split_non_empty_list 
      with (i := Vint ((Znth j (sublist 1 (len data) data)))) 
           (j2 := (len data - j - 2)%Z) 
           (ls' := sublist (j + 1 + 1) (len data) (map Vint data)).
    auto. repeat erewrite <- map_sublist.
    erewrite <- map_cons.
    f_equal. 
    replace (Znth j (sublist 1 (len data) data)) with
                 (Znth (j + 1) data).
    erewrite Znth_0_cons_sublist; try lia; auto.
    autorewrite with sublist.
    auto.
    all: autorewrite with sublist; strip_repr.

     }
  replace (Ptrofs.repr 1) with 1%ptrofs by auto with ptrofs.
  repeat erewrite map_sublist.
  erewrite D2.
  Intros.
  forward.
  entailer!.
  eapply Forall_Znth with (i0 := (j + 1)%Z) in H0; autorewrite with sublist; try lia.
  forward_if.
  ** forward.
     forward_if.
     ---
     forward.
     entailer!.
     (* -1 case *)
     { unfold ber_fetch_tags.
       repeat rewrite_if_b.
       clear D.
       unfold bft_loop.
    (*   rewrite if_false.
       auto.
       assert (j + 1 <= size - 1)%Z by lia.
     
              
       assert (bft_loop_monotonicity : forall data size j m,
                  (j <= m)%Z ->
                  ((fold_left (append_val data size 4) (range (Z.to_nat j)) 0) 
                      >> Int.repr (8 * 4 - 9)) <> 0 ->
                   (fold_left (append_val data size 4) 
                              (range (Z.to_nat m)) 0 >> Int.repr (8 * 4 - 9)) <> 0).
       { admit. }
       replace (Z.to_nat size - 1)%nat with (Z.to_nat (size -1)).
       eapply bft_loop_monotonicity with (j := (j + 1)%Z).
       lia.
       replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)).
       simpl.
       erewrite fold_left_app.
       simpl.
       unfold append_val at 1.
       cbn in H6.
       setoid_rewrite H6.
       break_if.
       * replace (nth (S (Z.to_nat j)) data 0) with (Znth (j + 1) data). 
         cbn.
         eassumption.
         admit.
       * destruct_orb_hyp.
         discriminate.
       * admit.
       * admit.
       * admit. } 
       rewrite if_false by admit.
       erewrite sepcon_comm.
       erewrite sepcon_assoc.
       erewrite <- D2.
       admit. *)
       admit. }
     admit.
     --- (* end the loop *)
       repeat forward.
       Exists (j + 1)%Z v.
       entailer!.
       repeat split; try lia.
     { generalize H12.
       replace ((Z.to_nat (j + 1))) with (S (Z.to_nat j)).
       simpl.
       erewrite fold_left_app.
       simpl.
       intro.
       unfold append_val at 1.
     (*  replace (((Z.of_nat (S (Z.to_nat j)) <=? size)
      || ((fold_left (append_val data) (range (Z.to_nat j)) 0 >> Int.repr (8 * 4 - 9)) ==
          0))%bool) with true. *)
       erewrite Z2Nat.id; try lia.
       auto.
       erewrite <- Z2Nat.inj_succ.
       auto.
       lia. }
    { intros.
      destruct (zeq i0 (j)).
      erewrite e.
      eassumption.
      eapply H7.
      lia. }
    do 2 f_equal.
    lia.
    f_equal.
    cbn. 
    strip_repr.
    f_equal.
    lia.
    f_equal.
    replace ((Z.to_nat (j + 1))) with (S (Z.to_nat j)).
    simpl.
    erewrite fold_left_app.
    cbn -[skipn].
    unfold append_val at 1.
   (* replace (Z.of_nat (S (Z.to_nat j)) <=? size) with true.
    cbn. *)
    erewrite Z2Nat.id; try lia.
    auto.
    erewrite <- Z2Nat.inj_succ.
    lia.
    lia.
 (*   { symmetry.
      Zbool_to_Prop.
      generalize H8.
      strip_repr.
      erewrite <- Z2Nat.inj_succ.
      erewrite Z2Nat.id.
      all: try lia. } *)
    entailer!.
    (* data_at combine proof *) 
    admit.
  ** (* return skipped case *)
     repeat forward.
     entailer!.
     { do 2 f_equal.
       unfold ber_fetch_tags.
       repeat rewrite_if_b.
       unfold bft_loop.       
       assert (index_spec_Some : forall data1 data2 b j,
                (forall i : Z, 0 <= i < len data1 -> (Znth i data1 & Int.repr 128) <> 0) ->
                 (b & Int.repr 128) = 0 ->
                  index (fun h : int => (h & Int.repr 128) == 0) 
                        (data1 ++ (b :: data2)) j 
                  = Some (j - len data2)%Z).
      { induction data1; intros until j0; intros (* L *) B Z.
        - unfold index.
          cbn -[len].
          erewrite Z. simpl. f_equal.
        - simpl.
          erewrite IHdata1.
          replace ((a & Int.repr 128) == 0) with false.
          auto.
          symmetry.
          eapply Int.eq_false.
          replace a with (Znth 0 (a :: data1)).
          eapply B.
          autorewrite with sublist. list_solve.
          auto.
          intros. 
          replace (Znth i0 data1) with (Znth (i0 + 1) (a :: data1)).
          eapply B.
          list_solve.
          erewrite Znth_pos_cons; try lia.
          repeat f_equal; lia.
          eassumption.
           }
      
      replace (sublist 1 (len data) data)
        with (sublist 1 (j + 1)%Z data ++
                      (Znth (j + 1)%Z data ::
                            sublist (j + 2) (len data) data)).
      erewrite index_spec_Some.
      autorewrite with sublist.
       replace (j +  Z.succ (len data - (j + 2)) - 1 - (len data - (j + 2)))%Z
         with (j )%Z by lia.
      replace (j + 2 <=? size) with true by (symmetry; Zbool_to_Prop; lia).
      cbn.
      lia.
      intros.
      replace (Znth i0 (sublist 1 (j + 1) data)) with 
          (Znth i0  (sublist 1 (len data) data)).
      eapply H7.
      autorewrite with sublist in H31.
      lia.
      erewrite Znth_sublist.
      autorewrite with sublist.
      erewrite Znth_sublist.
      auto.
      lia.
      autorewrite with sublist in H31.      
      lia.
      lia.
      autorewrite with sublist in H31.
      lia.
      erewrite <- H11.
      erewrite Znth_sublist.
      auto.
      lia.
      lia.
      replace (j + 2)%Z with (j + 1 + 1)%Z by lia.
      erewrite Znth_0_cons_sublist.
      autorewrite with sublist.
      auto.
      lia. }
     rewrite if_false by admit.
     erewrite sepcon_comm.
     erewrite sepcon_assoc.
     erewrite <- D2.
     entailer!. 
     admit.
    ++ (* LI to BREAK *) 
     (* forward.
      Exists (j)%Z.
      entailer!.
      repeat split.
      generalize H8.
      strip_repr.
      lia.
      (* 0 <= 2 + j <= Int.max_unsigned *)
      admit.
      eapply H6.
      admit.
      (* fold_left (append_val data size (sizeof tuint)) (range (Z.to_nat j)) 0 <> 0 *)
      (* change LI *)
      assert (index_spec : forall data j,
                (0 <= len data)%Z ->
                (forall i : Z, 0 <= i < len data -> (Znth i data & Int.repr 128) <> 0) ->
                  index (fun h : int => (h & Int.repr 128) == 0) 
                        data j = None).
      { induction data0; intros until j0; intros J B.
        - auto.
        - simpl.
          erewrite IHdata0.
          replace ((a & Int.repr 128) == 0) with false.
          auto.
          symmetry.
          eapply Int.eq_false.
          replace a with (Znth 0 (a :: data0)).
          eapply B.
          autorewrite with sublist.
          list_solve.
          auto.
          list_solve.
          intros. 
          assert (0 <= i0 < len (a :: data0)) as I.
          list_solve.
          replace (Znth i0 data0) with (Znth (i0 + 1) (a :: data0)).
          eapply B.
          list_solve.
          erewrite Znth_pos_cons; try lia.
          repeat f_equal; lia. }

      eapply index_spec.
      list_solve.
      clear H6.
      intros.
      eapply H7.
      (* need to connect len data and j - change break *)
      admit.    *) 
      admit. 
  --  (* BREAK rest POST *)
    Intros j.
    forward.
    (* return 0 *)
    assert (0%Z = fst (ber_fetch_tags data size)) as BF.
    { unfold ber_fetch_tags.
      repeat rewrite_if_b.
      unfold bft_loop.
      repeat rewrite_if_b.
      erewrite H8.
      auto. }
    erewrite <- BF.
    rewrite if_false by lia.
    erewrite sepcon_comm.
    erewrite <- D.
    entailer!.
Admitted.

End Ber_fetch_tag.

