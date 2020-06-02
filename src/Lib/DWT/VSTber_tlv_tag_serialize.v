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
      (EX i: int, 
          PROP ((Int.unsigned i <= 39)%Z;
               i = Int.repr 7 \/ i = Int.repr 14 \/ i = Int.repr 21 \/ i = Int.repr 28 \/ (32 < Int.unsigned i)%Z )
          LOCAL (temp _tval (Vint (tag >> Int.repr 2));
                 temp _i (Vint i);
                 temp _required_size (Vint (Int.repr 5 - ((Int.repr 39 - i) // (Int.repr 7))));
                 temp _size (Vint size);
                 temp _buf__1 bufp
                )
          SEP (data_at Tsh (tarray tuchar buf_size)
                       (default_val (tarray tuchar buf_size)) bufp))
      break: (EX i: int, 
                 PROP (((tag >> Int.repr 2) >> i == 0)%int = true 
                       \/ Int.unsigned i >= 8 * sizeof tuint ;
                       (i = Int.repr 7 
                       \/ i = Int.repr 7 + Int.repr 7 
                       \/ i = Int.repr 7 + Int.repr 7 + Int.repr 7 
                       \/ i = Int.repr 7 + Int.repr 7 + Int.repr 7 + Int.repr 7)%int
                       \/ (32 < Int.unsigned i)%Z )
                 LOCAL (temp _required_size (Vint (Int.repr 5 - ((Int.repr 39 - i) // (Int.repr 7))));
                       temp _tval (Vint (tag >> Int.repr 2));
                       temp _i (Vint i);
                       temp _size (Vint size);
                       temp _buf__1 bufp)
                 SEP (data_at Tsh (tarray tuchar buf_size)
                              (default_val (tarray tuchar buf_size)) bufp)).
         * (* Pre implies Inv *)
           Exists (Int.repr 7).
           entailer!.
         * (* Inv exec fn Break *)
           Intros i.
           forward_if; repeat forward.
           forward_if;
            repeat forward.
           Exists (i + Int.repr 7).
           entailer!.
           admit. 
           Exists i.
           entailer!.
           rewrite H4. 
           auto.
           cbn.
           admit.
           Exists i.
           entailer!.
           cbn.
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
           f_equal.
           unfold byte_length'.
           unfold byte_length'_loop.
           destruct  H1.
           repeat break_or_hyp.
             1-6: try rewrite H1 in *. cbv; auto.
           normalize.
            1-4: normalize; try rewrite H1 in *. 
            admit.
             normalize; try rewrite H1 in *. 
             1-4: admit.

           
           
           
          (* eapply ltu_false_inv in H2.
           rewrite e in H2.
           replace (Int.unsigned 0) with 0%Z in * by auto with ints. *)
           admit.
     ++ repeat forward.
        forward_loop 
      (EX i: int, EX n : nat,
          PROP ()
          LOCAL (temp _tval (Vint (tag >> Int.repr 2));
                 temp _i (Vint i);
                 temp _required_size 
                      (Vint (byte_length'_loop n tval i 1))%int;
                temp _size (Vint (size - 1));
                temp _buf__1 (offset_val 1 bufp))
          SEP ((data_at Tsh (tarray tuchar buf_size)
    (upd_Znth 0 (default_val (tarray tuchar buf_size))
       (Vint
          (Int.zero_ext 8
             (Int.or (Int.shl 
                        ((tag & Int.repr 3)) (Int.repr 6)) 
                     (Int.repr 31))))) bufp)))
      break: (EX i j : int, 
                 PROP (((tag >> Int.repr 2) >> i == 0)%int = true 
                       \/ Int.unsigned i >= 8 * sizeof tuint)
                 LOCAL (temp _required_size (Vint (byte_length' tval));
                       temp _tval (Vint (tag >> Int.repr 2));
                       temp _i (Vint i);
                       temp _size (Vint (size - 1));
                       temp _buf__1 (offset_val 1 bufp))
                 SEP ( (data_at Tsh (tarray tuchar buf_size)
    (upd_Znth 0 (default_val (tarray tuchar buf_size))
       (Vint
          (Int.zero_ext 8
             (Int.or (Int.shl 
                        ((tag & Int.repr 3)) (Int.repr 6)) 
                     (Int.repr 31))))) bufp))).
         * (* Pre implies Inv *)
           Exists (Int.repr 7).
           Exists 0%nat.
           entailer!.
         * (* Inv exec fn Post *)
           Intros i m.
           forward_if; repeat forward.
           forward_if;
           repeat forward.
           Exists (i + Int.repr 7).
           Exists (S m)%nat.
           entailer!.
           simpl.
          all:  admit.
        * Intros i j.
           forward_if.
          **
            unfold POSTCONDITION.
            unfold abbreviate. 
            break_let.
            forward.
            unfold ber_tlv_tag_serialize' in *; rewrite C in *;
              rewrite_if_b.
            assert (ExecBer_tlv_tag_serialize.byte_length' (tag >> Int.repr 2) = j) as J by admit.
            rewrite J in *.
            rewrite H2 in *.
            inversion Heqp.
            rewrite if_false by congruence.
            entailer!.
            admit.
          ** repeat forward.
             entailer!.
             admit.
             forward_loop  (EX i v: Z, 
                             PROP ()
                             LOCAL ( temp _tval (Vint (tag >> Int.repr 2));
                                     temp _i (Vint (Int.repr i));
                                     temp _required_size (Vint j);
                                     temp _size (Vint (size - 1));
                                     temp _buf__1 (offset_val v bufp);
                                     temp _end
       (force_val
          (sem_binary_operation' Osub (tptr tuchar) tint
             (eval_binop Oadd (tptr tuchar) tuint (offset_val v bufp) (Vint j)) (Vint (Int.repr 1)))))
          SEP (data_at Tsh (tarray tuchar (buf_size - v))
                       (default_val (tarray tuchar (buf_size - v))) (offset_val v bufp)))
          break:(EX i: Z, 
                                PROP ()
                                LOCAL ( temp _tval (Vint (tag >> Int.repr 2));
                                        temp _i (Vint (Int.repr i));
                                        temp _required_size (Vint j);
                                        temp _size (Vint size);
                                        temp _buf__1 (offset_val i bufp))
          SEP (data_at Tsh (tarray tuchar buf_size)
                       (default_val (tarray tuchar buf_size)) (offset_val i bufp))).
          *** Exists (Int.unsigned i - 7)%Z.
              Exists 1%Z.
              entailer!.
              admit.
          *** Intros x y.
              forward_if.
              admit.
              unfold tarray. 
              erewrite split2_data_at_Tarray_tuchar with (n1 := 1%Z). 
              Intros.
              erewrite sublist_one.
              erewrite data_at_tuchar_singleton_array_eq.
              forward.
              entailer!.
              admit.
              repeat forward.
              Exists (x - 7)%Z.
              Exists (y + 1)%Z.
              entailer!.
              all: try nia.
              all: admit.
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
