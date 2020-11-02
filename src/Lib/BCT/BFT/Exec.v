Require Import Core.Core  Types VST.floyd.proofauto Core.Notations.

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
  let i := index (fun h => (h & Int.repr 128) == 0) ls (len ls) in
  let v := fold_left (append_val ls) (range (Z.to_nat size)) 0 in
  match i with
    | Some i =>
      if i <=? size then
      let v := fold_left (append_val ls) (range (Z.to_nat i - 1)) 0 in
      ((i + 1)%Z, ((v << Int.repr 7) or Znth (i - 1) ls) << Int.repr 2 or tclass)
      else (0%Z, v)
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

Lemma index_spec_Some : forall data1 data2 b j,
    (forall i : Z, 0 <= i < len data1 -> (Znth i data1 & Int.repr 128) <> 0) ->
    (b & Int.repr 128) = 0 ->
    index (fun h : int => (h & Int.repr 128) == 0)%int 
          (data1 ++ (b :: data2)) j 
    = Some (j - len data2)%Z.
  { induction data1; intros until j; intros (* L *) B Z.
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
      replace (Znth i data1) with (Znth (i + 1) (a :: data1)).
      eapply B.
      list_solve.
      erewrite Znth_pos_cons; try lia.
      repeat f_equal; lia.
      eassumption.
  }
Qed.

Lemma index_spec_None : forall data j,
                 (0 <= len data)%Z ->
                 (forall i : Z, 0 <= i < len data -> (Znth i data & Int.repr 128) <> 0) ->
                 index (fun h : int => (h & Int.repr 128) == 0) 
                        data j = None.
  { induction data; intros until j; intros J B.
    - auto.
    - simpl.
      erewrite IHdata.
      replace ((a & Int.repr 128) == 0) with false.
      auto.
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
