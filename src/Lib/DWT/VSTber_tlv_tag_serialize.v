Require Import Core.Core  Core.VstTactics Core.StructNormalizer VstLib DWT.Exec 
        ErrorWithWriter.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_tlv_tag ExecBer_tlv_tag_serialize.
Require Import Core.Notations Core.SepLemmas.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Open Scope IntScope.

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
  - remember (Int.zero_ext 8 (Int.or (Int.shl ((tag & Int.repr 3)) (Int.repr 6)) 
                                (tag >> Int.repr 2)%int)) as e0.
    forward_if (
       PROP()
       LOCAL()
       SEP(if eq_dec size 0 
           then data_at_ Tsh (tarray tuchar buf_size) (Vptr buf_b buf_ofs) 
           else data_at Tsh (tarray tuchar buf_size)
                        (upd_Znth 0 (default_val (tarray tuchar buf_size))
                                  (Vint e0)) (Vptr buf_b buf_ofs))).
        (* (data_at Tsh (tarray tuchar buf_size) [Vint e0] (Vptr buf_b buf_ofs) *
          data_at Tsh (tarray tuchar (buf_size - 1))
                  (default_val (tarray tuchar (buf_size - 1))) 
                  (Vptr buf_b (buf_ofs + 1)%ptrofs)))). *)
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
    remember (Int.zero_ext 8 (((tag & Int.repr 3) << Int.repr 6) or Int.repr 31)) as e0. 
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
                                  (Vint e0)) (Vptr buf_b buf_ofs))).
    + remember (default_val (tarray tuchar buf_size)) as default_list.
      rewrite <- LB.
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
      assert (forall (cs : compspecs) i ls' ls sh b ofs z,
      ls = i::ls'  -> 
      z = Zlength ls' ->
      (Ptrofs.unsigned ofs + Zlength ls < Ptrofs.modulus)%Z -> 
      data_at sh (tarray tuchar (Zlength ls)) ls (Vptr b ofs) =
      (data_at sh tuchar i (Vptr b ofs) *
      data_at sh (tarray tuchar z) ls'
              (Vptr b (Ptrofs.add ofs Ptrofs.one))))%logic as SP by admit.
       remember (default_val (tarray tuchar buf_size)) as default_list.
       remember (Int.zero_ext 8 (((tag & Int.repr 3) << Int.repr 6) or Int.repr 31)) as e0.
      erewrite <- SP  with (ls :=  ([Vint e0] ++ sublist 1 (len default_list) default_list)).
      replace  buf_size with (len ([Vint e0] ++ sublist 1 (len default_list) default_list)).
      entailer!.
      admit.
      admit.
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
    (upd_Znth 0 (default_val (tarray tuchar buf_size))
       (Vint
          (Int.zero_ext 8
             (Int.or (Int.shl 
                        ((tag & Int.repr 3)) (Int.repr 6)) 
                     (Int.repr 31))))) (Vptr buf_b buf_ofs))))
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
       (Vint
          (Int.zero_ext 8
             (Int.or (Int.shl 
                        ((tag & Int.repr 3)) (Int.repr 6)) 
                     (Int.repr 31))))) (Vptr buf_b buf_ofs)))).
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
           remember (default_val (tarray tuchar buf_size)) as default_list.
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
          SEP (data_at Tsh (tarray tuchar 1) [Vint e0] (Vptr buf_b buf_ofs);
               data_at Tsh (tarray tuchar v) (map Vint ls)
                        (offset_val 1 (Vptr buf_b buf_ofs));
               data_at Tsh (tarray tuchar (buf_size - v)) 
                        (skipn (Z.to_nat v) default_list) 
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

                       SEP (data_at Tsh (tarray tuchar 1) [Vint e0] (Vptr buf_b buf_ofs);
                            data_at Tsh (tarray tuchar (len ls)) (map Vint ls)
                                    (offset_val 1 (Vptr buf_b buf_ofs));
                            data_at Tsh (tarray tuchar (buf_size - (Zlength ls))) 
                                    (sublist (len ls) buf_size default_list) 
                                    (offset_val ((Zlength ls) + 1) (Vptr buf_b buf_ofs)))).
          *** Exists (i - Int.repr 7).
              Exists 0%Z.
              Exists (@nil int).
              entailer!.
              erewrite data_at_tuchar_zero_array_eq.
              entailer!.
              all: admit.
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
              unfold tarray. 
              erewrite split2_data_at_Tarray_tuchar with (n0 := (buf_size - (len ls))%Z) 
                                                         (n1 := 1%Z).
              erewrite sublist_one.
              erewrite data_at_tuchar_singleton_array_eq at 1.
              erewrite data_at_tuchar_singleton_array_eq at 1.
              Intros.
              forward.
              erewrite <- data_at_tuchar_singleton_array_eq at 1.
              erewrite <- data_at_tuchar_singleton_array_eq at 1.
              assert ((field_address0 (Tarray tuchar (buf_size - len ls) noattr) (SUB 1)
          (offset_val (len ls + 1) (Vptr buf_b buf_ofs))) = offset_val 1 (offset_val (len ls + 1) (Vptr buf_b buf_ofs))).
              { 
                rewrite field_address0_offset.
                simpl.
                reflexivity.
                econstructor.
                easy.
                repeat split.
                simpl; autorewrite with norm.
                admit.
                                constructor.
                intros.
                repeat econstructor.
                simpl; autorewrite with norm.
                reflexivity.
                all: try nia || auto with zarith.
                autorewrite with sublist.
                simpl.
                admit.
              }
              rewrite H4.
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
               
               all: try nia.
               remember ((((tag & Int.repr 3) << Int.repr 6) or Int.repr 31)) as e0.   
               unfold serialize_tag'.
               rewrite <- H3.
               clear H3.
               entailer!.
               remember (default_val (tarray tuchar buf_size)) as default_list.
               remember (Int.zero_ext 8 (((tag & Int.repr 3) << Int.repr 6) or Int.repr 31)) as e0.
               remember (Int.zero_ext 8 ((tag >> Int.repr 2) & Int.repr 127)) as e_n.
               unfold offset_val.
               simpl.
 assert (forall (cs : compspecs) sh ls1 ls2 b ofs j1 j2,
    Zlength ls1 = j1 ->
    Zlength ls2 = j2 ->
    data_at sh (tarray tuchar (j1 + j2)) (ls1 ++ ls2) (Vptr b ofs) =
    (data_at sh (tarray tuchar j1) ls1 (Vptr b ofs) *
     data_at sh (tarray tuchar j2) ls2
             (Vptr b (Ptrofs.add ofs (Ptrofs.repr j1))))%logic) as SP by admit.
 unfold tarray in *.
               erewrite <- SP.
               replace (1 + len ls)%Z with (len ls + 1)%Z by nia.
               erewrite <- SP.
                erewrite <- SP.
                normalize.
                autorewrite with norm.
             (*  replace (Vint e_n) with (Znth 0 (Vint e_n :: skipn (length ls - 1)%nat default_list)).
               erewrite <- sublist_one with (hi := 1%Z).
            
               replace (skipn (Datatypes.length ls) default_list) with 
                 (Vint e_n :: skipn (length ls - 1)%nat default_list) at 1.  
               replace (buf_size - len ls - 1)%Z with ((buf_size - len ls) - 1)%Z by nia.
               rewrite sepcon_assoc.
               unfold tarray.
               erewrite <- split2_data_at_Tarray_tuchar.
               replace (len ((((tag & Int.repr 3) << Int.repr 6) or Int.repr 31) :: ls)) with
                   (len ls + 1)%Z.
               replace (map (fun x : int => Vint (Int.zero_ext 8 x)) ls) with (map Vint ls).
               replace (Vint e0 :: map Vint ls) with ([Vint e0] ++ (map Vint ls)).
               unfold offset_val.
               break_match.
               admit.
               admit.
               admit.
               admit.
               admit.
               pose proof combine_data_at_sublist_tuchar.
               unfold tarray in *.
               replace (data_at Tsh (Tarray tuchar buf_size noattr)
        (([Vint e0]
           ++ map Vint ls) 
           ++ sublist (len ls + 1) buf_size default_list) 
        (Vptr b i1))
              with
                (data_at Tsh (Tarray tuchar
                (len (([Vint e0] ++ map Vint ls) 
                        ++ sublist (len ls + 1) buf_size default_list))
                noattr)
                         (([Vint e0] ++ 
                                     map Vint ls)
                            ++ sublist (len ls + 1) buf_size default_list) 
                         (Vptr b i1)).
                erewrite H16 with (j := 1%Z).
                replace (len (([Vint e0] ++ map Vint ls) ++ sublist (len ls + 1) buf_size default_list) - 1)%Z
               with (len ((map Vint ls) ++ sublist (len ls + 1) buf_size default_list)).
                instantiate (2 := [Vint e0]).
                 instantiate (1 :=  (map Vint ls) ++ sublist (len ls + 1) buf_size default_list).
                 replace  (data_at Tsh
         (Tarray tuchar
            (len (([Vint e0] ++ map Vint ls) ++ sublist (len ls + 1) buf_size default_list) - 1)
            noattr) (map Vint ls ++ sublist (len ls + 1) buf_size default_list)
         (Vptr b (i1 + Ptrofs.repr 1)%ptrofs))%logic
                          with 

 (data_at Tsh
         (Tarray tuchar
            (len ((map Vint ls) ++ sublist (len ls + 1) buf_size default_list))
            noattr) (map Vint ls ++ sublist (len ls + 1) buf_size default_list)
         (Vptr b (i1 + Ptrofs.repr 1)%ptrofs))%logic.
                  erewrite H16 with (j := len ls) (ls1 :=  (map Vint ls))
                                    (ls2 := (Vint e_n :: skipn (Datatypes.length ls - 1) default_list)).
                  entailer!.


                 replace  (data_at Tsh
         (Tarray tuchar
            (len (([Vint e0] ++ map Vint ls) ++ sublist (len ls + 1) buf_size default_list) - 1)
            noattr) [Vint e0] (Vptr b (i1 + Ptrofs.repr 1))) with
( data_at Tsh
         (Tarray tuchar
            (len (map Vint ls) ++ sublist (len ls + 1) buf_size default_list))
            noattr) [Vint e0] (Vptr b (i1 + Ptrofs.repr 1)).
               autorewrite with sublist.
                erewrite H16.
 (ls := [Vint e0]).
                
                

               replace buf_size with
                   (len (([Vint e0] ++ map Vint ls) ++ sublist (len ls + 1) buf_size default_list))
                   at 2.
               erewrite H16.
               replace (len ls) with (len (Vint e0:: map Vint ls) - 1)%Z.
               erewrite <- H16.
                erewrite <- H16.
               replace (len ls) with (len (e0::ls) - 1)%Z.
               replace  (data_at Tsh (Tarray tuchar 1 noattr) [Vint e0] (Vptr b i1) *
   data_at Tsh (Tarray tuchar (len (e0 :: ls) - 1) noattr) (map Vint ls)
     (Vptr b (i1 + Ptrofs.repr 1)%ptrofs))%logic with
                    (data_at Tsh (Tarray tuchar (len (e0 :: ls)) noattr) (Vint e0:: (map Vint ls)) (Vptr b i1)). admit.
               erewrite H16.

               replace buf_size with
                   (len (([Vint e0] ++ map Vint ls) ++ sublist (len ls + 1) buf_size default_list))
                   at 2.
               erewrite H16.
               

               assert (forall (cs : compspecs) sh ls ls1 ls2 b ofs j,
                           (Ptrofs.unsigned ofs + Zlength ls < Ptrofs.modulus)%Z ->
                           0 <= j <= Zlength ls ->
                           ls = ls1 ++ ls2 ->
                           data_at sh (tarray tuchar (Zlength ls)) ls (Vptr b ofs) =
                           (data_at sh (tarray tuchar j) ls1 (Vptr b ofs) *
                            data_at sh (tarray tuchar (Zlength ls - j)) ls2
                                    (Vptr b (ofs + (Ptrofs.repr j))%ptrofs)))%logic.
               { intros.
                  erewrite  split_data_at_sublist_tuchar.
               
               erewrite <- split_data_at_sublist_tuchar.
               Search data_at sublist.
               
               all: admit. *)
Admitted.
