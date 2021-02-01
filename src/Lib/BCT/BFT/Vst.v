Require Import Core.Core Core.StructNormalizer VstLib.
Require Import VST.floyd.proofauto.
 Require Import BFT.Exec. 
Require Import Clight.ber_tlv_tag.
Require Import Core.Notations Core.SepLemmas Core.Tactics Core.VstTactics.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
 
Open Scope Z.

Section Ber_fetch_tag.

Definition ber_fetch_tag_spec : ident * funspec :=
  DECLARE _ber_fetch_tag
    WITH b : block, i : ptrofs, 
         data : list int, size : Z, 
         tag_p : val
    PRE [tptr tvoid, tuint, tptr tuint]
      PROP (0 <= size <= Int.max_unsigned;
            Forall (fun x => 0 <= Int.signed x <= Byte.max_signed) data;
            Ptrofs.unsigned i + (Zlength data) < Ptrofs.modulus;
            0 < len data <= Int.max_unsigned)
      PARAMS (Vptr b i; Vint (Int.repr size); tag_p)
      GLOBALS ()
      SEP (data_at Tsh (tarray tuchar (Zlength data)) 
                   (map Vint data) (Vptr b i);
           data_at_ Tsh tuint tag_p)
    POST [tint]
      let r := ber_fetch_tags data size in
      PROP ()
      LOCAL (temp ret_temp (Vint (fst r)))
      SEP (data_at Tsh (tarray tuchar (Zlength data)) 
                   (map Vint data) (Vptr b i);
           if (0 < fst r)%int 
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

Theorem ber_fetch_tag_correctness : semax_body Vprog Gprog 
                                   (normalize_function f_ber_fetch_tag composites) 
 
                                  ber_fetch_tag_spec.
Admitted.
(* Proof.
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
  simpl.
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
                 PROP (forall n : nat,
                          (n < Z.to_nat j)%nat ->
                          ((fold_left (append_val
                                         (sublist 1 (len data) data))
                                      (range n) 0 >> Int.repr 23) == 0) = true;
                       forall i, (0 <= i < j)%Z -> (Znth i data' & Int.repr 128) <> 0;
                       0 <= j + 2 <= Int.max_unsigned;
                       (0 <= j)%Z;
                       (0 <= j + 1 <= size)%Z)
                 LOCAL (temp _skipped (Vint (Int.repr (2 + j)));
                        temp _ptr (Vptr b (i + 1 + Ptrofs.repr j)%ptrofs);
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
                              (Vptr b (i + 1 + Ptrofs.repr j)%ptrofs);
                      data_at_ Tsh tuint tag_p))
            break:            
             (EX j : Z,
               let val := fold_left 
                        (append_val data')
                              (range (Z.to_nat size - 1)) 0 in
               PROP (size = (j + 1)%Z;
                     forall n, (n < Z.to_nat size)%nat 
                          -> ((fold_left (append_val data')
                                 (range n) 0
                                 >> Int.repr 23) == 0) = true;
                    (index (fun h : int => (h & Int.repr 128) == 0) (size - 1)
                           (data') (len data') = None)) 
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
                      data_at_ Tsh tuint tag_p))
  end.
  -- (* PRE to LI *) 
    Arguments eq_dec : simpl never.
    Exists 0%Z 0.
    autorewrite with sublist.
    entailer!.
    split.
    intros.
    replace n with (Z.to_nat 0).
    simpl.
    auto.
    replace (Z.to_nat 0) with O in * by auto.
    lia.
    intro. lia.
    erewrite data_at_zero_array_eq; auto.
    repeat erewrite sublist_map.
    entailer!.
  -- (* LI C LI *)
    Intros j v.
    forward_if.
    erewrite  Heqdata'.
    assert (Znth j (sublist 1 (len data) data) =
                 (Znth (j + 1) data)) as ZNTH.
    autorewrite with sublist.
    auto.
    ++ 
      assert (data_at Tsh (tarray tuchar (len data - j - 1))
                      (sublist (j + 1) (len data) (map Vint data))
                      (Vptr b (i + 1 + Ptrofs.repr j)%ptrofs) =
              (data_at Tsh tuchar
                   (Vint (Znth j (sublist 1 (len data) data))) 
                   (Vptr b (i + 1 + Ptrofs.repr j)%ptrofs) *
               data_at Tsh (tarray tuchar (len data - j - 2)) 
                       (sublist (j + 1 + 1) (len data) (map Vint data))
                       (Vptr b (i + 1 + Ptrofs.repr j + 1)%ptrofs))%logic) as D2.
  { erewrite split_non_empty_list 
      with (i := Vint ((Znth j (sublist 1 (len data) data)))) 
           (j2 := (len data - j - 2)%Z) 
           (ls' := sublist (j + 1 + 1) (len data) (map Vint data)).
    auto. repeat erewrite <- map_sublist.
    erewrite <- map_cons.
    f_equal. 
    erewrite ZNTH.
    erewrite Znth_0_cons_sublist; try lia; auto.
    
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
     assert (fst (ber_fetch_tags data size) = -1) as F.
     (* -1 case *)
     { unfold ber_fetch_tags.
       repeat rewrite_if_b.
       clear D.   
       unfold bft_loop.
       replace (Z.to_nat (size - 1) + 1)%nat with (Z.to_nat size).
        assert (range_In : forall n m, (0 <= n < m)%nat -> (0 < m)%nat -> In n (range (m))). 
         { induction m; intros N M.
           - lia.
           - simpl.
             erewrite in_app.
             destruct (Nat.eq_dec n (m))%nat.
             + right.
               erewrite e.
               econstructor.
               auto.
             + left.
               eapply IHm; try lia. }
         assert (existsb
        (fun n : nat =>
         negb ((fold_left (append_val (sublist 1 (len data) data)) 
                       (range n) 0 >> Int.repr 23) == 0))
        (range (Z.to_nat (size))) = true) as E.
       { erewrite existsb_exists.
         exists (Z.to_nat (j + 1)).
         split.
        
       eapply range_In.
       split.
       lia.
       eapply Z2Nat.inj_lt; try lia.
       replace 0%nat with (Z.to_nat 0).
       eapply Z2Nat.inj_lt; lia.
       auto.
       erewrite negb_true_iff.
       erewrite Int.eq_false.
       auto.
       auto.
       replace (Z.to_nat (j + 1)) with (S ((Z.to_nat (j)))).
       simpl.
       erewrite fold_left_app.
       simpl.
       unfold append_val at 1.
       generalize H13.
       replace (8 * 4 - 9)%Z with 23 by lia.
       erewrite Z2Nat.id.
       auto.
       lia.
       erewrite <- Z2Nat.inj_succ.
       auto.
       lia. }
       destruct (index (fun h : int => (h & Int.repr 128) == 0) (size - 1)
                  (sublist 1 (len data) data) (len (sublist 1 (len data) data))).
       --  assert (existsb
        (fun n : nat =>
         negb ((fold_left (append_val (sublist 1 (len data) data)) 
                       (range n) 0 >> Int.repr 23) == 0))
        (range (Z.to_nat z)) = true) as E'.
       { (* follows from z <= size -1 *) admit. }
       erewrite E'.
       auto.
       --
       replace (size - 1 + 1)%Z with size by lia.
       erewrite E.
       auto.
       --
       replace 1%nat with (Z.to_nat 1).
       erewrite <- Z2Nat.inj_add.
       f_equal.
       all: try lia.
       auto. }
       rewrite F. 
       simpl.
       entailer!.
     { erewrite sepcon_assoc.
       erewrite <- D2.
       erewrite sepcon_assoc.
       erewrite <- data_at_app_gen.
       erewrite <- D.
       entailer!.
        all: autorewrite with sublist; try lia; auto; strip_repr;
          try list_solve. }
     --- (* end the loop *)
       repeat forward.
       Exists (j + 1)%Z v.
       entailer!.
       repeat split; try lia.
     { generalize H6 H13.
    (*   replace ((Z.to_nat (j + 1))) with (S (Z.to_nat j)).
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
       lia. *) admit. }
     
    { intros.
      destruct (zeq i0 (j)).
      erewrite e.
      eassumption.
      eapply H7.
      lia. }
    do 2 f_equal.
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
    autorewrite with sublist.
    (* data_at combine proof *) 
    { erewrite <- ZNTH.
      erewrite sepcon_assoc.
      erewrite <- D2.
      erewrite <- data_at_app_gen.
      erewrite <- data_at_app_gen.
      entailer!.
       all: autorewrite with sublist; try lia; auto; strip_repr;
          try list_solve.
       erewrite sublist_map.
       erewrite <- map_app.
       f_equal.
       autorewrite with sublist.
       auto. }
  ** (* return skipped case *)
     repeat forward.
        
       remember (((((fold_left (append_val (sublist 1 (len data)  data))) (range (Z.to_nat j))
                           0 << Int.repr 7) or Znth j (sublist 1 (len data)  data)) <<
                Int.repr 2) or (Znth 0 data >> Int.repr 6)) as val.
     assert (ber_fetch_tags data size = (2 + j, val))%Z as RES.
     { unfold ber_fetch_tags.
       repeat rewrite_if_b.
       unfold bft_loop.    
            
      assert ((sublist 1 (len data) data) =
         (sublist 1 (j + 1)%Z data ++
                      (Znth (j + 1)%Z data ::
                            sublist (j + 2) (len data) data))) as DT.
      {  replace (j + 2)%Z with (j + 1 + 1)%Z by lia.
         erewrite Znth_0_cons_sublist.
         autorewrite with sublist.
         auto.
         lia. }
      erewrite DT at 1 2.
      erewrite index_spec_Some.
      autorewrite with sublist.
       replace (j +  Z.succ (len data - (j + 2)) - (len data - (j + 2)))%Z
         with (j + 1)%Z by lia.
      assert (existsb
      (fun n : nat =>
       negb
         ((fold_left (append_val (sublist 1 (len data) data)) (range n) 0 >> Int.repr 23) == 0))
      (range (Z.to_nat (j + 1))) = false) as E by admit.
      erewrite E.
       erewrite DT at 1 2.
      erewrite index_spec_Some.
      autorewrite with sublist.
       replace (j +  Z.succ (len data - (j + 2)) - (len data - (j + 2)))%Z
         with (j + 1)%Z by lia.
       f_equal.
       lia.
       subst.
       assert ((len data - 1 - (len data - (j + 2))) = j + 1)%Z as J.
       lia.
       erewrite J.
        replace (Z.to_nat (j + 1) - 1)%nat with ((Z.to_nat j)).
      replace (Znth (j + 1) data) with
          (Znth j (sublist 1 (len data) data)).
      auto.
      erewrite Z2Nat.inj_add.
      replace (Z.to_nat 1) with 1%nat by auto with arith.
      omega.
      lia.
      lia.
      list_solve.
      intros.
      replace (Znth i0 (sublist 1 (j + 1) data)) with 
          (Znth i0  (sublist 1 (len data) data)).
      subst.
      eapply H7.
      all: try autorewrite with sublist in H25; autorewrite with sublist;
        auto; try lia.
      erewrite <- H12.
      subst.
      erewrite Znth_sublist; try lia; auto.
       intros.
      replace (Znth i0 (sublist 1 (j + 1) data)) with 
          (Znth i0  (sublist 1 (len data) data)).
      subst.
      eapply H7.
      all: try autorewrite with sublist in H25; autorewrite with sublist;
        auto; try lia.
      erewrite <- H12.
      subst.
      erewrite Znth_sublist; try lia; auto.
     
 }
      assert (2 + j = fst (ber_fetch_tags data size))%Z as F.
     { erewrite RES. auto. }
     assert (0 <? fst (ber_fetch_tags data size) = true) as T
     by (Zbool_to_Prop; erewrite <- F; lia).
     erewrite  T.
     erewrite <- F.
     remember (sublist 1 (len data) data) as data'.
     assert (val = snd (ber_fetch_tags data size)) as G.
     { erewrite RES. auto. }
     erewrite G.
     entailer!.
     (*
       (data_at Tsh tuchar (Vint (Znth 0 data)) (Vptr b i) *
   data_at Tsh (tarray tuchar j) (sublist 1 (j + 1) (map Vint data)) (Vptr b (i + 1)%ptrofs) *
   data_at Tsh (tarray tuchar (len data - j - 1)) (sublist (j + 1) (len data) (map Vint data))
     (Vptr b (i + Ptrofs.repr j + 1)%ptrofs))%logic
  |-- data_at Tsh (tarray tuchar (len data)) (map Vint data) (Vptr b i)
      *)
     { 
       erewrite sepcon_comm.
       erewrite sepcon_comm.
       erewrite sepcon_assoc.     
       erewrite sepcon_assoc.
       erewrite <- D2.
       replace (i + Ptrofs.repr j + 1)%ptrofs with (((i + 1) + Ptrofs.repr j)%ptrofs).
       erewrite <- data_at_app_gen.
       erewrite <- D.
       entailer!.
       all: autorewrite with sublist; try lia; auto; try list_solve.
       strip_repr.
       strip_repr.
       f_equal.
       lia. }
    ++ (* LI to BREAK *) 
      forward.
      Exists j.
      assert (size = j + 1)%Z by lia.
      entailer!.
      replace (Z.to_nat (j + 1) - 1)%nat with (Z.to_nat j).
      repeat split;
       try eassumption.
      admit.
      replace (sublist 1 (len data) data) with
          ((sublist 1 (j + 1) data) ++ (sublist (j + 1) (len data) data)).
      eapply index_app.
      econstructor.
      autorewrite with sublist.
      lia.
      eapply index_spec_None.
      list_solve.
      autorewrite with sublist.
      intros.
      replace (Znth i0 (sublist 1 (j + 1) data))
        with (Znth i0 (sublist 1 (len data) data)).
      eapply H7; try lia.
      autorewrite with sublist.
      auto.
      autorewrite with sublist.
      auto.
      strip_repr.
      do 2 f_equal.
      lia.
      erewrite Z2Nat.inj_add; try lia.
      replace (Z.to_nat 1) with 1%nat by auto with arith.
      omega.
      (* data_at *)
      { replace (i + Ptrofs.repr (j + 1))%ptrofs with 
            (i + 1 + Ptrofs.repr j)%ptrofs.
        erewrite <- data_at_app_gen.
        entailer!.
        all: autorewrite with sublist; try lia; auto; try list_solve.
        erewrite sublist_map.
        erewrite <- map_app.
        f_equal.
        autorewrite with sublist.
        auto.
       strip_repr.
       strip_repr.
       f_equal.
       lia.  }
  --  (* BREAK rest POST *)
    Intros j.
    forward.
    (* return 0 *)
    assert (0%Z = fst (ber_fetch_tags data (j + 1))) as BF.
    { unfold ber_fetch_tags.
      repeat rewrite_if_b.
      unfold bft_loop.
      repeat rewrite_if_b.
      erewrite H8.
      replace ((j + 1 - 1 + 1))%Z with (j + 1)%Z by lia.
      assert (existb_forall_false : forall {A} (ls : list A) f, 
                 (forall a, In a ls -> 
                       f a = false) ->
                 existsb f ls = false).
      { induction ls.
        - simpl. auto.
        - intros.
          simpl.
          erewrite H6.
          simpl.
          eapply IHls.
          intros.
          eapply H6.
          eapply in_cons.
          auto.
          econstructor. auto. }                            
      assert (existsb
        (fun n : nat =>
         negb
           ((fold_left (append_val
                       (sublist 1 (len data) data)) (range n) 0 >> Int.repr 23) == 0))
                       (range (Z.to_nat (j))) = false) as G.
      { replace (Z.to_nat (j + 1) - 1)%nat with (Z.to_nat j) in *.
        eapply existb_forall_false.
        intros.
        erewrite negb_false_iff.
        eapply H7.
        assert (range_In_inv : forall m n, In n (range m) -> (n < m)%nat). 
         { 
           induction m; intros N M.
           - contradiction.
           - simpl in M.
             erewrite in_app in M.
             inversion M as [L | R].
             eapply IHm in L.
             lia.
             inversion R.
             lia.
             contradiction. } 
         eapply range_In_inv.
        (* assert (range_In_monotonicity : 
                       forall m2 m1 n, (m1 < m2)%nat
                                  -> In n (range m2) -> In n (range m1)). 
         { 
           induction m2; intros until n; intros M I.
           - contradiction.
           - simpl in *.
             erewrite in_app in I.
             
             eapply IHm2.
             lia.
             destruct (Nat.eq_dec n (S m))%nat.
             + right.
               erewrite e.
               econstructor.
               auto.
             + left.
               eapply IHm; try lia. *)
           auto.
        
    (*   (*  assert (exists x y : Type, x <> y).
         { exists nat.
           exists Z. *)
           replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)).
             assert (range_In_monotonicity : 
                       forall n m1 m2, (m1 <= m2)%nat
                                  -> In n (range m1) -> In n (range m2)). 
         { 
           (*induction m; intros N.
           - simpl.
             assert (n = 0)%nat as M by lia.
             erewrite M.
             lia.
           - simpl.
             erewrite in_app.
             destruct (Nat.eq_dec n (S m))%nat.
             + right.
               erewrite e.
               econstructor.
               auto.
             + left.
               eapply IHm; try lia. *)
           admit.
               }
         eapply range_In_monotonicity with (m1 := Z.to_nat j).
         lia.
         auto.
         admit. (* true as before *) *)
         admit.
         replace 1%nat with (Z.to_nat 1).
         erewrite <- Z2Nat.inj_sub.
         f_equal.
         all: try lia.
         auto. }
      replace (j + 1 - 1)%Z with j by lia.
      admit. }
    admit.
     (* erewrite G.
      
      auto. }
    erewrite <- BF.
    simpl.
    erewrite sepcon_comm.
    erewrite <- D.
    entailer!. *)
Admitted.
*)
End Ber_fetch_tag.

