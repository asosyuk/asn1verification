Require Import Core.Core Core.StructNormalizer VstLib.
Require Import VST.floyd.proofauto.
(* Require Import BFT.Exec. *)
Require Import Clight.ber_tlv_tag.
Require Import Core.Notations Core.SepLemmas Core.Tactics Core.VstTactics.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
 
Open Scope int.
 
(*Fixpoint bft_loop n (ptr : list int) size tclass sizeofval : (int * int) := 
  match n with
    | S m =>
       let skip := (len ptr - Z.of_nat n)%Z in
       let (s, val) := bft_loop m ptr size tclass sizeofval in
       if skip <=? size then
      if eq_dec (nth n ptr 0 & Int.repr 128) 0
      then let val' := (val << Int.repr 7) or (nth n ptr 0) in
           let tag_r := (val' << Int.repr 2) or tclass in
           (Int.repr skip, tag_r)
      else 
        let val' := (val << Int.repr 7) or (nth n ptr 0 & Int.repr 127) in
        if eq_dec (val' >> Int.repr (8 * sizeofval - 9)) 0
        then (s, val')
        else (Int.neg 1, val') 
       else (Int.repr skip, val)               
  | O => (0, 0)
  end.

Definition ber_fetch_tags (ptr : list int) size sizeofval  :=
  if eq_dec size 0%Z
  then (0, 0)
  else let val := Znth 0 ptr in 
       let tclass := val >> Int.repr 6 in 
       if eq_dec (val & Int.repr 31) (Int.repr 31)
       then bft_loop (length ptr) (skipn 1 ptr) size tclass sizeofval    
       else (1, ((val & Int.repr 31) << Int.repr 2) or tclass). *)

Fixpoint bft_loop v (ptr : list int) skip (size : Z) tclass (sizeofval : Z)  := 
  match ptr with
    | [] => (0%Z, v)
    | h :: tl => 
      if skip <=? size then
      if eq_dec (h & Int.repr 128) 0 
      then (skip, (v << Int.repr 7) or h)
      else 
        let v := (v << Int.repr 7) or (h & Int.repr 127) in 
        if eq_dec (v >> Int.repr (8 * sizeofval - 9)) 0
        then let (r, v) := bft_loop v tl (skip + 1)%Z size tclass sizeofval in
             (r, v << Int.repr 2 or tclass)
        else (-1, v)
      else (0%Z, v)
  end.          

Definition ber_fetch_tags (ptr : list int) size sizeofval  :=
  if eq_dec size 0%Z
  then (0%Z, 0)
  else let val := Znth 0 ptr in 
       let tclass := val >> Int.repr 6 in 
       if eq_dec (val & Int.repr 31) (Int.repr 31)
       then bft_loop 0 (skipn 1 ptr) 2 size tclass sizeofval    
       else (1%Z, ((val & Int.repr 31) << Int.repr 2) or tclass).

Eval cbv in (Int.repr (2^23 ) >> Int.repr 23).

Eval cbv in ((1 or Int.repr 128)).
Eval cbv in ber_fetch_tags [Int.repr 31; Int.repr 128 or Int.repr 123; Int.repr 128 or 0]
                           32 (sizeof tuint).

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
            0 < len data)
      PARAMS ((Vptr b i); Vint (Int.repr size); tag_p)
      GLOBALS ()
      SEP (data_at Tsh (tarray tuchar (Zlength data)) 
                   (map Vint data) (Vptr b i);
           data_at_ Tsh tuint tag_p)
    POST [tint]
      let r := ber_fetch_tags data size (sizeof tuint) in
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
  match goal with
  | [ _ : _ |-  semax _ ?P ?C ?Post ] =>
    forward_loop (
               EX j : Z, EX v : int, EX k : Z,
                 let v := snd (bft_loop v (sublist 1 j data) k size tclass (sizeof tuint)) in
                 PROP (0 <= j + 1 < len data)
                 LOCAL (temp _skipped (Vint (Int.repr (2 + j)));
                        temp _ptr (Vptr b (i + Ptrofs.repr j + 1)%ptrofs);
                        temp _val (Vint v);
                        temp _t'1 (Vint (Znth 0 data & Int.repr 31)%int);
                        temp _tclass (Vint (Znth 0 data >> Int.repr 6)%int);
                        temp _size (Vint (Int.repr size));
                        temp _tag_r tag_p)
                 SEP (data_at Tsh tuchar (Vint (Znth 0 data)) (Vptr b i);
                      data_at Tsh (tarray tuchar j)
                              (sublist 1 (j + 1) 
                                   (map Vint (sublist 1 (j + 1) data)))
                              (Vptr b (i + 1)%ptrofs);
                      data_at Tsh (tarray tuchar (len data - j - 1)) 
                              (sublist (j + 1) (len data) (map Vint data))
                              (Vptr b (i + Ptrofs.repr j + Ptrofs.repr 1)%ptrofs);
                      data_at_ Tsh tuint tag_p))
            break:
             (EX j : Z, EX v : int,
               let val := (Int.or (v << Int.repr 7) (Znth j data)) in
               PROP (v >> Int.repr (8 * (sizeof tuint) - 9) <> 0) 
                LOCAL (temp _skipped (Vint (Int.repr 2));
                        temp _ptr (Vptr b (i + Ptrofs.repr j)%ptrofs);
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
    Exists 0%Z 0 2.
    autorewrite with sublist.
    entailer!.
    admit.
    erewrite data_at_zero_array_eq; auto.
    entailer!. 
  -- (* LI C LI *)
    Intros j v k.
    forward_if.
    ++ 
            assert (data_at Tsh (tarray tuchar (len data - j - 1))
                      (sublist (j + 1) (len data) (map Vint data))
                      (Vptr b (i + Ptrofs.repr j + 1)%ptrofs) =
          (data_at Tsh tuchar (Vint (Znth (j + 1) data)) 
                   (Vptr b (i + Ptrofs.repr j + 1)%ptrofs) *
          data_at Tsh (tarray tuchar (len data - j - 2)) 
                  (sublist (j + 1 + 1) (len data) (map Vint data))
                  (Vptr b (i + Ptrofs.repr j + 1 + 1)%ptrofs))%logic) as D2.
  { erewrite split_non_empty_list 
      with (i := Vint (Znth (j + 1) data)) 
           (j2 := (len data - j - 2)%Z) 
           (ls' := sublist (j + 1 + 1) (len data) (map Vint data)).
    auto. repeat erewrite <- map_sublist.
    erewrite <- map_cons.
    f_equal. erewrite Znth_0_cons_sublist; try lia; auto.
    all: autorewrite with sublist; strip_repr.
    admit.
  }
  replace (Ptrofs.repr 1) with 1%ptrofs by auto with ptrofs.
  erewrite D2.
  Intros.
  forward.
  entailer!.
  eapply Forall_Znth with (i0 := (j + 1)%Z) in H0; try lia.
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
       admit. }
       rewrite if_false by admit.
       erewrite sepcon_comm.
       erewrite sepcon_assoc.
       erewrite <- D2.
       admit.
     --- (* end the loop *)
       repeat forward.
       Exists (j + 1)%Z v (k - 1)%Z.
       entailer!.
       repeat split; try lia.
       admit.
       do 2 f_equal.
       lia.
       f_equal.
       cbn. 
       admit.
       f_equal.
       assert (forall ls v j a size tclass, 
                  bft_loop v (ls ++ [a]) 
                      (j + 1) size tclass (sizeof tuint) = (r, v) ->
                   (bft_loop v ls j size tclass (sizeof tuint) <<
                     Int.repr 7) or (a & Int.repr 127))%int as K.
       { induction ls.
         - intros. 
           autorewrite with sublist.
           cbn.
           admit.
         - intros.
           cbn.
           cbn in IHls.
           erewrite IHls.
      
       remember ((snd
           (bft_loop v (sublist 1 j data) (j + 2) size (Znth 0 data >> Int.repr 6) (sizeof tuint)) <<
         Int.repr 7) or (Znth (j + 1) data & Int.repr 127)) as val.
       
       replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)).
       simpl.
       replace (j + 1 <=? size) with true.
       clear D2.
       rewrite if_false.
       
       
       assert (forall j data a ls size tclass, 
                  data = ls ++ [a] ->
                  snd (bft_loop data
                      0 (j + 1) size tclass (sizeof tuint)) =
               ((snd (bft_loop ls 0 j size tclass (sizeof tuint)) <<
                     Int.repr 7) or (a & Int.repr 127))) as K.
       { intros. 
         admit. (* need app spec *)
         }
       erewrite K.
       auto.
       admit.
       entailer!.
       admit.
  ** (* return skipped case *)
     repeat forward.
     entailer!.
     admit.
     rewrite if_false by admit.
     erewrite sepcon_comm.
     erewrite sepcon_assoc.
     erewrite <- D2.
     erewrite <- D.
     entailer!.
    ++ forward.
       entailer!.
  --  (* BREAK rest POST *)
    forward.
    entailer!.
    (* return 0 *)
    admit.
    rewrite if_false by admit.
    erewrite sepcon_comm.
    erewrite <- D.
    entailer!.
Admitted.

End Ber_fetch_tag.

