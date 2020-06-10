Require Import Core.Core  Core.VstTactics Core.StructNormalizer VstLib DWT.Exec 
        ErrorWithWriter.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_tlv_tag ExecBer_tlv_tag_serialize.
Require Import Core.Notations Core.SepLemmas.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Open Scope IntScope.

Proposition split_non_empty_list (cs : compspecs) i ls' ls sh b ofs j1 j2:
      ls = i::ls' -> 
      j1 = Zlength ls ->
      j2 = Zlength ls' ->
      data_at sh (tarray tuchar j1) ls (Vptr b ofs) =
     (data_at sh tuchar i (Vptr b ofs) *
      data_at sh (tarray tuchar j2) ls' (Vptr b (ofs + 1)%ptrofs))%logic.
Admitted.

Lemma data_at_app2 : forall (cs : compspecs) sh ls1 ls2 b ofs j1 j2,
    j1 = Zlength ls1 ->
    j2 = Zlength ls2 ->
    data_at sh (tarray tuchar (j1 + j2)) (ls1 ++ ls2) (Vptr b ofs) =
   (data_at sh (tarray tuchar j1) ls1 (Vptr b ofs) *
    data_at sh (tarray tuchar j2) ls2 (Vptr b (ofs + (Ptrofs.repr j1))%ptrofs))%logic.
Admitted.

Lemma data_at_app3 : forall (cs : compspecs) sh ls1 ls2 ls3 b ofs j1 j2 j3,
    Zlength ls1 = j1 ->
    Zlength ls2 = j2 ->
    Zlength ls3 = j3 ->
    data_at sh (tarray tuchar (j1 + j2 + j3)) (ls1 ++ ls2 ++ ls3) (Vptr b ofs) =
   (data_at sh (tarray tuchar j1) ls1 (Vptr b ofs) *
    data_at sh (tarray tuchar j2) ls2 (Vptr b (ofs + (Ptrofs.repr j1))%ptrofs) *
    data_at sh (tarray tuchar j3) ls2 (Vptr b (ofs + (Ptrofs.repr (j1 + j2)))%ptrofs))%logic.
Admitted.

Definition ber_tlv_tag_serialize_spec' : ident * funspec :=
  DECLARE _ber_tlv_tag_serialize
  WITH tag: int, buf_b : block, buf_ofs : ptrofs, size : int, buf_size : Z
  PRE[tuint, tptr tvoid, tuint]
    PROP((32 <= buf_size)%Z)
    PARAMS(Vint tag; (Vptr buf_b buf_ofs); Vint size)
    GLOBALS()
    SEP(data_at Tsh (tarray tuchar buf_size)
                    (default_val (tarray tuchar buf_size)) 
                    (Vptr buf_b buf_ofs))
  POST[tuint]
    let (ls, z) := ber_tlv_tag_serialize' tag size in
    PROP()
    LOCAL(temp ret_temp (Vint z))
    SEP(if eq_dec ls [] 
        then data_at Tsh (tarray tuchar buf_size)
                         (default_val (tarray tuchar buf_size))
                         (Vptr buf_b buf_ofs) 
        else data_at Tsh (tarray tuchar buf_size)
                         (map (fun x => Vint (Int.zero_ext 8 x)) ls ++
                          sublist (len ls) buf_size (default_val (tarray tuchar buf_size)))
                         (Vptr buf_b buf_ofs)).
    (* SEP(if eq_dec ls [] 
        then data_at Tsh (tarray tuchar buf_size)
                     (default_val (tarray tuchar buf_size))
                     (Vptr buf_b buf_ofs) 
        else
          data_at Tsh (tarray tuchar buf_size)
                  (map (fun x => Vint (Int.zero_ext 8 x)) ls) 
                  (Vptr buf_b buf_ofs) *
          data_at Tsh (tarray tuchar (buf_size - len ls))
                  (default_val (tarray tuchar (buf_size - len ls))) 
                  (Vptr buf_b (buf_ofs + Ptrofs.repr (len ls))%ptrofs)).  *)

Definition Gprog' := ltac:(with_library prog [ber_tlv_tag_serialize_spec']).

Open Scope IntScope.

Theorem ber_tlv_tag_serialize_correct' : 
  semax_body Vprog Gprog' (normalize_function f_ber_tlv_tag_serialize composites)
             ber_tlv_tag_serialize_spec'.
Proof.
  start_function.
  remember (tag >> Int.repr 2) as tval.
  remember (Int.zero_ext 8 (((tag & Int.repr 3) << Int.repr 6) or tval)) as e0. 
  remember (default_val (tarray tuchar buf_size)) as default_list.
  remember (Int.zero_ext 8 (((tag & Int.repr 3) << Int.repr 6) or Int.repr 31)) as e1.
  assert (len default_list = buf_size) as LB.
  {  subst; unfold default_val;
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
           then data_at_ Tsh (tarray tuchar buf_size) (Vptr buf_b buf_ofs) 
           else data_at Tsh (tarray tuchar buf_size)
                        (upd_Znth 0 (default_val (tarray tuchar buf_size))
                                  (Vint e0)) (Vptr buf_b buf_ofs))).
    + forward. 
      rewrite_if_b.
      entailer!.
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
             then temp _buf__1 (Vptr buf_b buf_ofs)
             else temp _buf__1 (offset_val 1 (Vptr buf_b buf_ofs))  ;
             if eq_dec size 0 
             then temp _size (Vint size)
             else temp _size (Vint (size - 1));
            temp _tval (Vint tval))
       SEP(if eq_dec size 0 
           then data_at Tsh (tarray tuchar buf_size)
                     (default_val (tarray tuchar buf_size)) (Vptr buf_b buf_ofs)  
           else data_at Tsh (tarray tuchar buf_size)
                        (upd_Znth 0 (default_val (tarray tuchar buf_size))
                                  (Vint e1)) (Vptr buf_b buf_ofs))).
    + rewrite <- LB.     
      erewrite split_data_at_sublist_tuchar with (j := 1%Z).
      erewrite sublist_one.
      erewrite data_at_tuchar_singleton_array_eq.
      Intros.
      repeat forward.
      repeat rewrite_if_b.
      entailer!.
      erewrite upd_Znth_unfold.
      erewrite sublist_nil.
      erewrite app_nil_l.
      remember (default_val (tarray tuchar buf_size)) as default_list.
      remember (Int.zero_ext 8 (((tag & Int.repr 3) << Int.repr 6) or Int.repr 31)) as e1.     
      erewrite <- split_non_empty_list with
          (j1 := buf_size)
          (ls :=  ([Vint e1] ++ sublist 1 (len default_list) default_list)).
      entailer!.
      reflexivity.
      all: try nia;
        unfold default_val;
        simpl;
        try erewrite Zlength_list_repeat;
        try nia; auto.
      all: admit.
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
                 temp _buf__1 (Vptr buf_b buf_ofs))
          SEP (data_at Tsh (tarray tuchar buf_size)
                       (default_val (tarray tuchar buf_size)) (Vptr buf_b buf_ofs)))
      break: (EX i: int, 
                 PROP (((tag >> Int.repr 2) >> i == 0)%int = true 
                       \/ Int.unsigned i >= 8 * sizeof tuint)
                 LOCAL (temp _required_size (Vint (byte_length' tval));
                       temp _tval (Vint (tag >> Int.repr 2));
                       temp _i (Vint i);
                       temp _size (Vint size);
                       temp _buf__1 (Vptr buf_b buf_ofs))
                 SEP (data_at Tsh (tarray tuchar buf_size)
                              (default_val (tarray tuchar buf_size)) (Vptr buf_b buf_ofs))).
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
             unfold byte_length'_loop.
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
                 temp _buf__1  (offset_val 1 (Vptr buf_b buf_ofs)))
           SEP ((data_at Tsh (tarray tuchar buf_size)
    (upd_Znth 0 (default_val (tarray tuchar buf_size)) (Vint e1)) (Vptr buf_b buf_ofs))))
      break: (EX i: int, 
                 PROP (((tag >> Int.repr 2) >> i == 0)%int = true 
                       \/ Int.unsigned i >= 8 * sizeof tuint)
                 LOCAL (temp _required_size (Vint (byte_length' tval));
                       temp _tval (Vint (tag >> Int.repr 2));
                       temp _i (Vint i);
                       temp _size (Vint (size - 1));
                       temp _buf__1  (offset_val 1 (Vptr buf_b buf_ofs)))
                  SEP ((data_at Tsh (tarray tuchar buf_size)
    (upd_Znth 0 (default_val (tarray tuchar buf_size))
       (Vint e1)) (Vptr buf_b buf_ofs)))).
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
           forward.
           forward_loop (
               EX i : int, EX v : Z, EX ls : list int, 
                           PROP ()
                           LOCAL (temp _tval (Vint (tag >> Int.repr 2));
                                  temp _i (Vint i);
                                  temp _required_size (Vint (byte_length' tval));
                                  temp _size (Vint (size - 1));
                                  temp _buf__1 (offset_val (v + 1) (Vptr buf_b buf_ofs));
                                  temp _end
          (force_val (sem_binary_operation' Osub (tptr tuchar) tint
             (eval_binop Oadd (tptr tuchar) tuint (offset_val 1 (Vptr buf_b buf_ofs)) 
                         (Vint (byte_length' tval))) (Vint (Int.repr 1)))))
          SEP (data_at Tsh (tarray tuchar 1) [Vint e1] (Vptr buf_b buf_ofs);
               data_at Tsh (tarray tuchar v) (map Vint ls)
                        (offset_val 1 (Vptr buf_b buf_ofs));
               data_at Tsh (tarray tuchar (buf_size - v - 1)) 
                                    (sublist (v + 1) buf_size default_list) 
                                    (offset_val (v + 1) (Vptr buf_b buf_ofs))))

          break: (EX i: int, EX ls : list int,

                       PROP (let s := byte_length' tag in 
                             let n := Z.to_nat (Int.unsigned (s - 1)) in
                             ls = serialize_tag_loop n
                                (s * Int.repr  7 - Int.repr 7)%int tag)

                       LOCAL (temp _tval (Vint (tag >> Int.repr 2));
                              temp _i (Vint i);
                              temp _required_size (Vint (byte_length' tval));
                              temp _size (Vint (size - 1));
                              temp _buf__1 (offset_val (len ls + 1) (Vptr buf_b buf_ofs)))

                       SEP (data_at Tsh (tarray tuchar 1) [Vint e1] (Vptr buf_b buf_ofs);
                            data_at Tsh (tarray tuchar (len ls)) (map Vint ls)
                                    (offset_val 1 (Vptr buf_b buf_ofs));
                            data_at Tsh (tarray tuchar (buf_size - (Zlength ls))) 
                                    (sublist (len ls + 1) buf_size default_list) 
                                    (offset_val ((Zlength ls) + 1) (Vptr buf_b buf_ofs)))).
          *** Exists (i - Int.repr 7).
              Exists 0%Z.
              Exists (@nil int).
              entailer!.
              erewrite data_at_tuchar_zero_array_eq.
              entailer!.
              erewrite <- data_at_app2.
              erewrite upd_Znth_unfold.
              erewrite sublist_nil.
              erewrite app_nil_l.
              replace (len (default_val (tarray tuchar buf_size))) with buf_size.
              entailer!.
              replace (1 + (buf_size - 1))%Z with buf_size by nia.
              entailer!.
              nia.
              reflexivity.
              autorewrite with sublist norm; auto.
              cbn; auto.
          *** Intros j v ls.
              forward_if.
              admit.
              unfold tarray. 
              erewrite split2_data_at_Tarray_tuchar with (n0 := (buf_size - v - 1)%Z)  (n1 := 1%Z).
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
              Exists (ls ++ [Int.repr 128 or ((tval >> j) & (Int.repr 127))]).
              entailer!.
              all: try nia.
              1-4: admit.
              forward.
              Exists j.
              Exists ls.
              entailer!.
              assert (len ls = v) by admit.              
              subst.
              admit.
               assert (len ls = v) by admit.              
              subst.
              entailer!.
              admit.
          *** Intros i0 ls.
              unfold offset_val.
              erewrite split_non_empty_list
                with (ls' := (sublist (len ls + 1 + 1) buf_size default_list))
                     (j2 := (buf_size - len ls - 1 - 1)%Z)
                     (ofs := (buf_ofs + Ptrofs.repr (len ls + 1))%ptrofs).
              Intros.
              forward.
              unfold POSTCONDITION.
              unfold abbreviate. 
              break_let.
              forward.
               unfold ber_tlv_tag_serialize' in *; rewrite C in *;
              rewrite_if_b.
               rewrite H2 in *.
               inversion Heqp.
                rewrite_if_b.
                rewrite if_false by congruence.               
               unfold serialize_tag'.
               rewrite <- H3.
               clear H3.
               entailer!.
               remember (default_val (tarray tuchar buf_size)) as default_list.
               remember (Int.zero_ext 8 (((tag & Int.repr 3) << Int.repr 6) or Int.repr 31)) as e1.
               remember (Int.zero_ext 8 ((tag >> Int.repr 2) & Int.repr 127)) as e_n.
               unfold offset_val.
               simpl.
               erewrite <- data_at_tuchar_singleton_array_eq.
               erewrite <- data_at_app2.
               replace (1 + len ls)%Z with (len ls + 1)%Z by nia.
                erewrite <- data_at_app2.
                replace (buf_ofs + Ptrofs.repr (len ls + 1) + 1)%ptrofs
                        with (buf_ofs + Ptrofs.repr (len ls + 1 + 1))%ptrofs.
                erewrite <- data_at_app2.
                autorewrite with sublist norm.
Admitted.
