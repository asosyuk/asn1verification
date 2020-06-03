Require Import Core.Core  Core.VstTactics Core.StructNormalizer VstLib DWT.Exec 
        ErrorWithWriter.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_tlv_tag ExecBer_tlv_tag_serialize.
Require Import Core.Notations.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Open Scope IntScope.

(* Fixpoint byte_length'_loop n z i l :=
  match n with
  | O => l
  | S n => if z >> i == 0
          then l 
          else byte_length'_loop n z (i + Int.repr 7) (l + 1)
  end.

Definition byte_length' z := byte_length'_loop 4%nat z (Int.repr 7) 1.

Definition serialize_tag' tval :=
let fix serialize_tag' n i tval :=
  match n with
  | O => [tval & Int.repr 127]
  | S n => (Int.repr 128 or (tval >> i & Int.repr 127)) 
            :: serialize_tag' n (i - Int.repr 7) tval
  end in 
 let s := byte_length' tval in 
 let n := Z.to_nat (Int.unsigned (s - 1)) in
 serialize_tag' n (s * Int.repr  7 - Int.repr 7) tval.

Definition ber_tlv_tag_serialize' (tag size : int): list int * int :=
  let tclass := tag & Int.repr 3 in 
  let tval := tag >> Int.repr 2 in
  if tval <=u Int.repr 30 then
    if eq_dec size 0 
    then ([], 1)
    else ([(tclass << Int.repr 6) or tval], 1) 
  else 
    let required_size := byte_length' tval in
    if eq_dec size 0 
       then ([], required_size + 1)
       else let buf0 := (tclass << Int.repr 6) or Int.repr 31 in
            if (size - 1 <u required_size)
            then ([buf0], required_size + 1)
            else
            (buf0 :: (serialize_tag' tag), required_size + 1). *)

Definition ber_tlv_tag_serialize_spec' : ident * funspec :=
  DECLARE _ber_tlv_tag_serialize
  WITH tag: int, bufp : val, size : int, buf_size : Z
  PRE[tuint, tptr tvoid, tuint]
    PROP((32 <= buf_size)%Z)
    PARAMS(Vint tag; bufp; Vint size)
    GLOBALS()
    SEP(data_at Tsh (tarray tuchar buf_size)
                     (default_val (tarray tuchar buf_size)) bufp )
  POST[tuint]
    let (ls, z) := ber_tlv_tag_serialize' tag size in
    PROP()
    LOCAL(temp ret_temp (Vint z))
    SEP(if eq_dec ls [] 
        then data_at Tsh (tarray tuchar buf_size)
                     (default_val (tarray tuchar buf_size)) bufp 
         else data_at Tsh (tarray tuchar buf_size)
                     (map (fun x => Vint (Int.zero_ext 8 x)) ls ++
                          sublist (len ls) buf_size 
                          (default_val (tarray tuchar buf_size)))
                     bufp). 

Definition Gprog' := ltac:(with_library prog [ber_tlv_tag_serialize_spec']).

Open Scope IntScope.

Theorem ber_tlv_tag_serialize_correct' : 
  semax_body Vprog Gprog' (normalize_function f_ber_tlv_tag_serialize composites)
             ber_tlv_tag_serialize_spec'.
Proof.
  start_function.
  remember (tag >> Int.repr 2) as tval.
  assert (len (default_val (tarray tuchar buf_size)) = buf_size) as LB.
  {  unfold default_val;
        simpl;
        try erewrite Zlength_list_repeat;
        try nia; auto. }
  repeat forward.
  forward_if.
  assert (((tag >> Int.repr 2) <=u Int.repr 30) = true) as C.
  { unfold Int.ltu.
    break_if;
    autorewrite with norm in *; try nia.
    auto.  }
  - forward_if (
       PROP()
       LOCAL()
       SEP(if eq_dec size 0 
           then data_at_ Tsh (tarray tuchar buf_size) bufp 
           else (data_at Tsh (tarray tuchar buf_size)
    (upd_Znth 0 (default_val (tarray tuchar buf_size))
       (Vint
          (Int.zero_ext 8
             (Int.or (Int.shl 
                        ((tag & Int.repr 3)) (Int.repr 6)) 
                     (tag >> Int.repr 2)%int)))) bufp))).
    + forward. 
      rewrite_if_b. entailer!.
    + forward.
      rewrite_if_b.
      entailer!.
    + unfold POSTCONDITION.
      unfold abbreviate. 
      break_let.
      forward.
      break_if; unfold ber_tlv_tag_serialize' in *; rewrite C in *;
        rewrite_if_b.
      * inversion Heqp.
        rewrite_if_b.
        entailer!.               
      * inversion Heqp.
        rewrite if_false by congruence.
        erewrite upd_Znth_unfold.
        rewrite LB.
        entailer!.
        nia.
  - (* 30 < tag *)
    assert (((tag >> Int.repr 2) <=u Int.repr 30) = false) as C.
    { unfold Int.ltu.
      break_if;
        autorewrite with norm in *; try nia.
      auto.  }
    forward_if (
       PROP()
       LOCAL(if eq_dec size 0 
             then temp _buf__1 bufp
             else temp _buf__1 (offset_val 1 bufp)  ;
             if eq_dec size 0 
             then temp _size (Vint size)
             else temp _size (Vint (size - 1));
            temp _tval (Vint (tag >> Int.repr 2)))
       SEP(if eq_dec size 0 
           then data_at Tsh (tarray tuchar buf_size)
                     (default_val (tarray tuchar buf_size)) bufp  
           else (data_at Tsh (tarray tuchar buf_size)
    (upd_Znth 0 (default_val (tarray tuchar buf_size))
       (Vint
          (Int.zero_ext 8
             (Int.or (Int.shl 
                        ((tag & Int.repr 3)) (Int.repr 6)) 
                     (Int.repr 31))))) bufp))).
    + unfold tarray. 
      erewrite split2_data_at_Tarray_tuchar with (n1 := 1%Z). 
      erewrite sublist_one.
      erewrite data_at_tuchar_singleton_array_eq.
      Intros.
      repeat forward.
      repeat rewrite_if_b.
      entailer!.
      erewrite <- data_at_tuchar_singleton_array_eq.
      erewrite upd_Znth_unfold.
      erewrite sublist_nil.
      erewrite app_nil_l.
      erewrite split2_data_at_Tarray_app with (mid := 1%Z).
      replace (len (default_val (tarray tuchar buf_size))) with buf_size
        by eassumption. (* rewrite cannot find the term - bug? *)
      entailer!.
      all: try nia;
        unfold default_val;
        simpl;
        try erewrite Zlength_list_repeat;
        try nia; auto.
    + forward.
      repeat rewrite_if_b.
      entailer!.
    + (* loop *)
      break_if.
      ++ repeat forward.        
         forward_loop 
      (EX i j: int, 
          PROP ()
          LOCAL (temp _tval (Vint (tag >> Int.repr 2));
                 temp _i (Vint i);
                 temp _required_size (Vint j);
                 temp _size (Vint size);
                 temp _buf__1 bufp)
          SEP (data_at Tsh (tarray tuchar buf_size)
                       (default_val (tarray tuchar buf_size)) bufp))
      break: (EX i: int, 
                 PROP (((tag >> Int.repr 2) >> i == 0)%int = true 
                       \/ Int.unsigned i >= 8 * sizeof tuint)
                 LOCAL (temp _required_size (Vint (byte_length' tval));
                       temp _tval (Vint (tag >> Int.repr 2));
                       temp _i (Vint i);
                       temp _size (Vint size);
                       temp _buf__1 bufp)
                 SEP (data_at Tsh (tarray tuchar buf_size)
                              (default_val (tarray tuchar buf_size)) bufp)).
         * (* Pre implies Inv *)
           Exists (Int.repr 7).
           Exists 1.
           entailer!.
         * (* Inv exec fn Break *)
           Intros i j.
           forward_if; repeat forward.
           forward_if;
            repeat forward.
           Exists (i + Int.repr 7).
           Exists (j + 1).
           entailer!.
           Exists i.
           entailer!.
           rewrite H2.
           admit. (* need to replace j *)
           Exists i.
           entailer!.
           admit.
         * (* Post exec rest of the fn *)
           Intros i.
           forward_if.
           unfold POSTCONDITION.
           unfold abbreviate. 
           break_let.
           forward.
            unfold ber_tlv_tag_serialize' in *; rewrite C in *;
              inversion Heqp;
              rewrite_if_b.
           entailer!.
           eapply ltu_false_inv in H2.
           rewrite e in H2.
           replace (Int.unsigned 0) with 0%Z in * by auto with ints. 
           assert (1 <= Int.unsigned (byte_length' tval))%Z as BL.
           { unfold byte_length'.
             repeat break_if; discriminate. }
           nia.
     ++ repeat forward.        
         forward_loop 
      (EX i j: int, 
          PROP ()
          LOCAL (temp _tval (Vint (tag >> Int.repr 2));
                 temp _i (Vint i);
                 temp _required_size (Vint j);
                 temp _size (Vint (size - 1));
                 temp _buf__1  (offset_val 1 bufp))
           SEP ((data_at Tsh (tarray tuchar buf_size)
    (upd_Znth 0 (default_val (tarray tuchar buf_size))
       (Vint
          (Int.zero_ext 8
             (Int.or (Int.shl 
                        ((tag & Int.repr 3)) (Int.repr 6)) 
                     (Int.repr 31))))) bufp)))
      break: (EX i: int, 
                 PROP (((tag >> Int.repr 2) >> i == 0)%int = true 
                       \/ Int.unsigned i >= 8 * sizeof tuint)
                 LOCAL (temp _required_size (Vint (byte_length' tval));
                       temp _tval (Vint (tag >> Int.repr 2));
                       temp _i (Vint i);
                       temp _size (Vint (size - 1));
                       temp _buf__1  (offset_val 1 bufp))
                  SEP ((data_at Tsh (tarray tuchar buf_size)
    (upd_Znth 0 (default_val (tarray tuchar buf_size))
       (Vint
          (Int.zero_ext 8
             (Int.or (Int.shl 
                        ((tag & Int.repr 3)) (Int.repr 6)) 
                     (Int.repr 31))))) bufp))).
         * (* Pre implies Inv *)
           Exists (Int.repr 7).
           Exists 1.
           entailer!.
         * (* Inv exec fn Break *)
           Intros i j.
           forward_if; repeat forward.
           forward_if;
            repeat forward.
           Exists (i + Int.repr 7).
           Exists (j + 1).
           entailer!.
           Exists i.
           entailer!.
           rewrite H2.
           admit. (* need to replace j *)
           Exists i.
           entailer!.
           admit.
         * (* Post exec rest of the fn *)
           Intros i.
           forward_if.
           unfold POSTCONDITION.
           unfold abbreviate. 
           break_let.
           forward.
           unfold ber_tlv_tag_serialize' in *; rewrite C in *;
             rewrite_if_b.
           entailer!.
           rewrite H2 in *.
           inversion Heqp.
           reflexivity.
           rewrite H2 in *.
           inversion Heqp.
           rewrite if_false by congruence.
           entailer!.
           erewrite upd_Znth_unfold.
           erewrite sublist_nil.
           erewrite app_nil_l.
           replace (len (default_val (tarray tuchar buf_size))) with buf_size
             by eassumption. 
           entailer!.
           nia.
           forward.
           entailer!.
           admit. (* do we assume that buf + 1 is not null? *)
           forward.
           remember (default_val (tarray tuchar buf_size)) as default_list.
           remember (Int.zero_ext 8 (((tag & Int.repr 3) << Int.repr 6) or Int.repr 31)) as e0.
(*
           Fixpoint serialize_tag_loop  n i tval :=
             match n with
             | O => []
             | S n => (Int.repr 128 or (tval >> i & Int.repr 127)) 
                       :: serialize_tag_loop n (i - Int.repr 7) tval
             end. 
           Definition serialize_tag tval :=
             let s := byte_length' tval in 
             let n := Z.to_nat (Int.unsigned (s - 1)) in
             serialize_tag_loop n (s * Int.repr  7 - Int.repr 7) tval. *)

(* [Vint (Int.repr 128 or ((tval >> (i - Int.repr (v*7))) & (Int.repr 127)))] *)
           forward_loop  (EX i : int, EX v : Z, EX ls : list val, 
                             PROP ()
                             LOCAL ( temp _tval (Vint (tag >> Int.repr 2));
                                     temp _i (Vint i);
                                     temp _required_size (Vint (byte_length' tval));
                                     temp _size (Vint (size - 1));
                                     temp _buf__1 (offset_val (v + 1) bufp);
                                     temp _end
       (force_val (sem_binary_operation' Osub (tptr tuchar) tint
             (eval_binop Oadd (tptr tuchar) tuint (offset_val 1 bufp) 
                         (Vint (byte_length' tval))) (Vint (Int.repr 1)))))
          SEP (data_at Tsh (tarray tuchar 1) [Vint e0] bufp;
               data_at Tsh (tarray tuchar v) (ls)
                        (offset_val 1 bufp);
                        data_at Tsh (tarray tuchar (buf_size - v)) 
                        (skipn (Z.to_nat v) default_list) (offset_val (v + 1) bufp)))
          break:(EX i: Z, PROP ()
                          LOCAL ( temp _tval (Vint (tag >> Int.repr 2));
                                  temp _i (Vint (Int.repr i));
                                  temp _required_size (Vint (byte_length' tval));
                                  temp _size (Vint size);
                                  temp _buf__1 (offset_val i bufp))
                          SEP (data_at Tsh (tarray tuchar buf_size)
                       (default_val (tarray tuchar buf_size)) (offset_val i bufp))).
          *** Exists (i - Int.repr 7).
              Exists 0%Z.
              Exists (@nil val).
              entailer!.
              erewrite data_at_tuchar_zero_array_eq.
              entailer!.
              all: admit.
              (* Search upd_Znth.
              erewrite upd_Znth_unfold.
              erewrite sublist_nil.
              erewrite app_nil_l.
              assert (forall (a : val) ls, a :: ls = [a] ++ ls) as LS.
              { intros.
                destruct ls; econstructor. }
              erewrite <- LS.
              simpl.
              admit.
              admit. *)
          *** Intros j v ls.
              forward_if.
              admit.
              unfold tarray. 
              erewrite split2_data_at_Tarray_tuchar with (n0 := (buf_size - v)%Z)  (n1 := 1%Z).
               erewrite sublist_one.
              erewrite data_at_tuchar_singleton_array_eq at 1.
              erewrite data_at_tuchar_singleton_array_eq at 1.
              Intros.
              forward.
              entailer!.
              admit.
              repeat forward.
              
              Exists (j - Int.repr 7).
              Exists (v + 1)%Z.
              Exists (ls ++ [Vint (Int.repr 128 or ((tval >> j) & (Int.repr 127)))]).
              entailer!.
              all: try nia.
              1-4: admit.
              forward.
          *** Intro x.
              unfold tarray. 
              erewrite split2_data_at_Tarray_tuchar with (n1 := 1%Z). 
              Intros.
              erewrite sublist_one.
              erewrite data_at_tuchar_singleton_array_eq.
              forward.
              unfold POSTCONDITION.
              unfold abbreviate. 
              break_let.
              forward.
               unfold ber_tlv_tag_serialize' in *; rewrite C in *;
              rewrite_if_b.
               entailer!.
               admit.
Admitted.
