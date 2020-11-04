Require Import Core.Core  Types VST.floyd.proofauto Core.Notations.
Require Import Core.Tactics.

Open Scope int.

Fixpoint range n :=
  match n with 
  | O => []
  | S m => range m ++ [m]
  end.

Fixpoint index {A} (f : A -> bool) size ls l :=
  match ls with
  | [] => None
  | x :: tl => 
    let i := (l - len tl)%Z in
    if i <=? size 
    then (if f x then Some i else index f size tl l)
    else None
  end.


(* let v := fold_left (append_val data') (range (Z.to_nat j)) 0 in
                 PROP (v >> Int.repr 23 = 0; *)

Definition append_val ls 
  := (fun x y =>
        (x << Int.repr 7) or (Znth (Z.of_nat y) ls & Int.repr 127)). 

(*Definition append_val ls 
  := (fun x y =>
        if x >> Int.repr 23 == 0 
        then (x << Int.repr 7) or (Znth (Z.of_nat y) ls & Int.repr 127)
        else x). *)

Eval cbv in (fold_left ((fun ls x y =>
        if x >> Int.repr 23 == 0 
        then (x << Int.repr 7) or (Znth (Z.of_nat y) ls & Int.repr 127)
        else x) [1]) (range 3%nat) (Int.repr Int.max_unsigned)).  

Definition bft_loop ls size tclass := 
  let i := index (fun h => (h & Int.repr 128) == 0) size ls (len ls) in
  let v := fold_left (append_val ls) (range (Z.to_nat size)) 0 in
  let r := match i with | Some i => i | None => (size + 1)%Z end in 
  let ex := existsb (fun n => 
                let v' := fold_left (append_val ls) (range n) 0 in
                negb (v' >> Int.repr 23 == 0))
              (range (Z.to_nat r)) in
  if ex then (-1, v) else 
  match i with
    | Some i =>
      let v := fold_left (append_val ls) (range (Z.to_nat i - 1)) 0 in     
      ((i + 1)%Z, ((v << Int.repr 7) or Znth (i - 1) ls) << Int.repr 2 or tclass)
    | None => (0%Z, v)
  end.

Definition ber_fetch_tags (ptr : list int) size   :=
  if eq_dec size 0%Z
  then (0%Z, 0)
  else let val := Znth 0 ptr in 
       let tclass := val >> Int.repr 6 in 
       if eq_dec (val & Int.repr 31) (Int.repr 31)
       then bft_loop (sublist 1 (len ptr) ptr) (size - 1) tclass     
       else (1%Z, ((val & Int.repr 31) << Int.repr 2) or tclass).

Lemma index_app_gen : forall A (ls1 ls2 ls : list A) f size j,
                 (size < (j - len ls2) + 1)%Z -> 
                 index f size ls1 (j - len ls2) = None -> 
                 index f size (ls1 ++ ls2) j = None. 
Proof.
  induction ls1; intros.
    - induction ls2.
      + auto.
      + simpl.
        replace (j - len ls2 <=? size) with false.
        auto.
        symmetry.
        Zbool_to_Prop.
        autorewrite with sublist in *.
        list_solve.
    - intros.
      simpl in *.
      break_if; auto.
      replace (j - len ls2 - len ls1 <=? size) with true in *.
      break_if.
      congruence.
      eapply IHls1.
      econstructor.
      lia.
      auto.
      symmetry.
      Zbool_to_Prop.
      autorewrite with sublist in *.
      list_solve.
Qed.

Lemma index_app : forall A (ls1 ls2 ls : list A) f size,
                 (size < len ls1 + 1)%Z -> 
                 index f size ls1 (len ls1) = None -> 
                 index f size (ls1 ++ ls2) (len (ls1 ++ ls2)) = None. 
Proof.
  intros.
  eapply index_app_gen.
  auto.
  list_solve.
  autorewrite with sublist.
  auto.
Qed.

Lemma index_spec_Some : forall data1 data2 size b j,
    (j - len data2 <= size)%Z ->
    (forall i : Z, 0 <= i < len data1 -> (Znth i data1 & Int.repr 128) <> 0) ->
    (b & Int.repr 128) = 0 ->
    index (fun h : int => (h & Int.repr 128) == 0)%int size
          (data1 ++ (b :: data2)) j 
    = Some (j - len data2)%Z.
  { induction data1; intros until j; intros S B Z.
    - unfold index.
      cbn -[len].
      erewrite Z. simpl.
      break_if.
      auto.
      Require Import Core.Tactics.
      Zbool_to_Prop.
      lia.
    - simpl.
      erewrite IHdata1.
      replace ((a & Int.repr 128) == 0) with false.
      break_if.
      auto.
      Zbool_to_Prop.
      autorewrite with sublist in Heqb0.
      list_solve.
      symmetry.
      eapply Int.eq_false.
      replace a with (Znth 0 (a :: data1)).
      eapply B.
      autorewrite with sublist. list_solve.
      auto.
      auto.
      intros.
      replace (Znth i data1) with (Znth (i + 1) (a :: data1)).
      eapply B.
      list_solve.
      erewrite Znth_pos_cons; try lia.
      repeat f_equal; lia.
      eassumption.
  }
Qed.

Lemma index_spec_None : forall data size j,
                 (0 <= len data)%Z ->
                 (forall i : Z, 0 <= i < len data -> (Znth i data & Int.repr 128) <> 0) ->
                 index (fun h : int => (h & Int.repr 128) == 0) size 
                        data j = None.
  { induction data; intros until j; intros J B.
    - auto.
    - simpl.
      erewrite IHdata.
      replace ((a & Int.repr 128) == 0) with false.
      break_if; auto.
      symmetry.
      eapply Int.eq_false.
      replace a with (Znth 0 (a :: data)).
      eapply B.
      autorewrite with sublist.
      list_solve.
      auto.
      list_solve.
      intros. 
      assert (0 <= i < len (a :: data)) as I.
      list_solve.
      replace (Znth i data) with (Znth (i + 1) (a :: data)).
      eapply B.
      list_solve.
      erewrite Znth_pos_cons; try lia.
      repeat f_equal; lia. }
Qed.
