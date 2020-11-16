Require Import Core.Core Core.VstTactics Core.StructNormalizer VstLib
        ErrorWithWriter.
Require Import Core.Tactics.
               
Require Import VST.floyd.proofauto.
Require Import Clight.ber_tlv_tag Exec.Ber_tlv_tag_serialize.
Require Import Core.Notations Core.SepLemmas.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Open Scope Z.

Definition ber_tlv_tag_serialize_spec : ident * funspec :=
  DECLARE _ber_tlv_tag_serialize
  WITH tag : int, buf_b : block, buf_ofs : ptrofs, buf_size : Z
  PRE[tuint, tptr tvoid, tuint]
    PROP(buf_size = 0 \/ buf_size = 32;
         Ptrofs.unsigned buf_ofs + buf_size < Ptrofs.modulus)
    PARAMS(Vint tag; (Vptr buf_b buf_ofs); Vint (Int.repr buf_size))
    GLOBALS()
    SEP(data_at Tsh (tarray tuchar buf_size)
                    (default_val (tarray tuchar buf_size)) 
                    (Vptr buf_b buf_ofs))
  POST[tuint]
    PROP()
    LOCAL(temp ret_temp
               (Vint (Int.repr (snd (tag_serialize tag (Int.repr buf_size))))))
    SEP(let (ls, z) := tag_serialize tag (Int.repr buf_size) in
        data_at Tsh (tarray tuchar buf_size)
                         (map Vint ls 
                              ++ sublist (len ls) buf_size 
                             (default_val (tarray tuchar buf_size)))
                         (Vptr buf_b buf_ofs)).

Definition Gprog := ltac:(with_library prog [ber_tlv_tag_serialize_spec]).

Open Scope IntScope.

Theorem ber_tlv_tag_serialize_correct : 
  semax_body Vprog Gprog (normalize_function f_ber_tlv_tag_serialize composites)
             ber_tlv_tag_serialize_spec.
Proof.
  start_function.
  remember (Int.shru tag (Int.repr 2)) as tval.
  remember (Int.zero_ext 8 (((tag & Int.repr 3) << Int.repr 6) or tval)) as e0. 
  remember (default_val (tarray tuchar buf_size)) as default_list.
  remember (Int.zero_ext 8 (((tag & Int.repr 3) << Int.repr 6) or Int.repr 31)) as e1.
  assert (len default_list = buf_size) as LB.
  {  subst; unfold default_val;
        simpl;
        try erewrite Zlength_list_repeat;
        try nia; auto. }
  pose proof (req_size_32 tval) as R.
  repeat forward.
  forward_if.
  - forward_if (
       PROP()
       LOCAL()
       SEP(if eq_dec (Int.repr buf_size) 0 
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
      try break_let.
      forward.
     break_if; unfold tag_serialize in *.
     replace (30 >=? Int.unsigned (tag >>u Int.repr 2)) with true in *.
     rewrite_if_b.
     inversion Heqp.
     entailer!.
     autorewrite with sublist.
     erewrite sublist_same_gen.
     entailer!.
     lia.
     setoid_rewrite LB. lia.
     symmetry.
     Zbool_to_Prop.
     lia.
     replace (30 >=? Int.unsigned (tag >>u Int.repr 2)) with true in *.
     rewrite_if_b.
     inversion Heqp.
     entailer!.
     erewrite upd_Znth_unfold.
     setoid_rewrite LB.
     entailer!.
     setoid_rewrite LB.
     assert (buf_size <> 0%Z).
     eapply repr_neq_e in n; try lia.
     lia.
     symmetry.
     Zbool_to_Prop.
     lia.
  - (* 30 < tag *) 
    forward_if (
       PROP()
       LOCAL(if eq_dec (Int.repr buf_size) 0 
             then temp _buf__1 (Vptr buf_b buf_ofs)
             else temp _buf__1 (offset_val 1 (Vptr buf_b buf_ofs));
             if eq_dec (Int.repr buf_size) 0 
             then temp _size (Vint (Int.repr buf_size))
             else temp _size (Vint (Int.repr (buf_size - 1)));
            temp _tval (Vint tval))
       SEP(if eq_dec (Int.repr buf_size) 0 
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
      replace (len (default_val (tarray tuchar buf_size))) with buf_size.
      auto.
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
      all: autorewrite with sublist;
      try erewrite Zlength_sublist_correct;
          try nia;  try setoid_rewrite LB; try nia.
    + forward.
      repeat rewrite_if_b.
      entailer!.
    + break_if.
      assert (buf_size = 0%Z) as S.
      eapply repr_inj_unsigned; strip_repr.
      assert ((30 >=? Int.unsigned (tag >>u Int.repr 2)) = false) as C.
           { erewrite Z.geb_leb. 
             Zbool_to_Prop.
             nia. }
      ++ repeat forward.        
         forward_loop 
      (EX i: Z, 
          PROP (i = 1%Z \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5; 
                forall j, 0 <= j < i ->
                     (Int.shru tval (Int.repr j * Int.repr 7) == 0)%int = false)
          LOCAL (temp _tval (Vint (Int.shru tag (Int.repr 2)));
                 temp _i (Vint (Int.repr (i * 7)));
                 temp _required_size (Vint (Int.repr i));
                 temp _size (Vint (Int.repr buf_size));
                 temp _buf__1 (Vptr buf_b buf_ofs))
          SEP (data_at Tsh (tarray tuchar buf_size)
                       (default_val (tarray tuchar buf_size))
                       (Vptr buf_b buf_ofs)))
      break: (let r := required_size (tag >>u(Int.repr 2)) in
              PROP ()
              LOCAL (temp _required_size (Vint (Int.repr r));
                     temp _tval (Vint (tag >>u Int.repr 2));
                     temp _i (Vint (Int.repr (r * 7)));
                     temp _size (Vint (Int.repr buf_size));
                     temp _buf__1 (Vptr buf_b buf_ofs))
                 SEP (data_at Tsh (tarray tuchar buf_size)
                              default_list
                              (Vptr buf_b buf_ofs))).
         * Exists 1%Z.
           entailer!.
           intros. 
           replace x with 0%Z by nia.
           erewrite Int.shru_zero.
           destruct  (Int.shru tag (Int.repr 2) == 0) eqn : T.
           eapply int_eq_e in T.
           rewrite T in *.
           cbv in C.
           congruence.
           auto.
         * Intro i.
           forward_if; repeat forward.
           forward_if;
            repeat forward.
           rewrite Int.unsigned_repr in H2.
           entailer!.
           rep_omega.
           Exists (i + 1)%Z.
           rewrite Int.unsigned_repr in H2;
             try rep_omega.
           entailer!.
           split.
        ** intros.
           destruct (zeq j i).
           subst.
           eapply Int.eq_false.
           autorewrite with norm.
           eassumption.
           eapply H4.
           nia.
        ** do 2 f_equal.
           nia.
        ** entailer!.
           assert (required_size (tag >>u (Int.repr 2)) = i) as RS.
           eapply required_size_spec; auto.
           autorewrite with norm.
           eassumption.
           subst.
           intuition.
        ** entailer!.
           rewrite Int.unsigned_repr in H2;
             try rep_omega.
           replace i with 5 in * by nia.
           assert (required_size (tag >>u (Int.repr 2)) = 5) as RS.
           eapply required_size_spec; auto.
           autorewrite with norm.
           cbn.
           erewrite shr_lt_zero_35.
           break_if; auto.
           unfold Int.ltu in Heqb.
           break_if; autorewrite with norm in *.
           replace (Int.unsigned 0) with 0%Z in * by auto with ints.
           nia.
           congruence.
           rewrite RS.
           intuition.
         * (* Post exec rest of the fn *)
           simpl. 
           forward_if.
           unfold POSTCONDITION.
           unfold abbreviate. 
           try break_let.
           forward.
           unfold tag_serialize in *.
           rewrite C in *.
           repeat rewrite_if_b.
           rewrite Int.unsigned_repr in H2;
            try rep_omega.           
           simpl in Heqp.
           replace (-1 <? required_size (tag >>u Int.repr 2)) with true in *
             by (symmetry; Zbool_to_Prop; lia).
           inversion Heqp.  
           autorewrite with sublist.
           entailer!.
           generalize H2.
           strip_repr.
           intro. subst. lia.
           subst; strip_repr.
           ++
              assert (buf_size <> 0%Z) as S.
              {  eapply repr_neq_e in n; lia. }
              repeat forward. 
         forward_loop (EX i: Z, 
          PROP (i = 1%Z \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5; 
                forall j, 0 <= j < i ->
                     (Int.shru tval (Int.repr j * Int.repr 7) == 0)%int = false)
          LOCAL (temp _tval (Vint (tag >>u (Int.repr 2)));
                 temp _i (Vint (Int.repr (i * 7)));
                 temp _required_size (Vint (Int.repr i));
                 temp _size (Vint (Int.repr (buf_size - 1)));
                 temp _buf__1 (offset_val 1 (Vptr buf_b buf_ofs)))
          SEP ((data_at Tsh (tarray tuchar buf_size)
                        (upd_Znth 0 (default_val (tarray tuchar buf_size))
                                  (Vint e1)) (Vptr buf_b buf_ofs))))
      break: (let r := required_size (tag >>u (Int.repr 2)) in
              PROP ()
              LOCAL (temp _required_size (Vint (Int.repr r));
                     temp _tval (Vint (tag >>u Int.repr 2));
                     temp _i (Vint (Int.repr (r * 7)));
                     temp _size (Vint (Int.repr (buf_size - 1)));
                     temp _buf__1 (offset_val 1 (Vptr buf_b buf_ofs)))
                 SEP ((data_at Tsh (tarray tuchar buf_size)
                               (upd_Znth 0 (default_val (tarray tuchar buf_size)) 
                                         (Vint e1)) (Vptr buf_b buf_ofs)))).
         * Exists 1%Z.
           entailer!.
           intros. 
           replace x with 0%Z by nia.
           erewrite Int.shru_zero.
           destruct  (Int.shru tag (Int.repr 2) == 0) eqn : T.
           eapply int_eq_e in T.
           rewrite T in *.
           cbv in H1.
           congruence.
           auto.
         * Intro i.
           forward_if; repeat forward.
           forward_if;
             repeat forward.
           rewrite Int.unsigned_repr in H2.
           entailer!.
           rep_omega.
           Exists (i + 1)%Z.
           rewrite Int.unsigned_repr in H2; try rep_omega.
           entailer!.
           split.
        ** intros.
           destruct (zeq j i).
           subst.
           eapply Int.eq_false.
           autorewrite with norm.
           eassumption.
           eapply H4.
           nia.
        ** do 2 f_equal.
           nia.
        ** entailer!.
           assert (required_size (tag >>u (Int.repr 2)) = i) as RS.
           eapply required_size_spec; auto.
           autorewrite with norm.
           eassumption.
           subst.
           intuition.
        ** entailer!.
           rewrite Int.unsigned_repr in H2; try rep_omega.
           replace i with 5 in * by nia.
           assert (required_size (tag >>u (Int.repr 2)) = 5) as RS.
           eapply required_size_spec; auto.
           autorewrite with norm.
           cbn.
           erewrite shr_lt_zero_35.
           break_if; auto.
           unfold Int.ltu in Heqb.
           break_if; autorewrite with norm in *.
           replace (Int.unsigned 0) with 0%Z in * by auto with ints.
           nia.
           congruence.
           rewrite RS.
           intuition.
         * (* Post exec rest of the fn *)
            assert ((30 >=? Int.unsigned (tag >>u Int.repr 2)) = false) as C.
           { erewrite Z.geb_leb. 
             Zbool_to_Prop.
             nia. }
           simpl.
           forward_if.
           unfold POSTCONDITION.
           unfold abbreviate. 
           try break_let.
           forward.
           unfold tag_serialize in *.
           rewrite C in *.         
           rewrite Int.unsigned_repr in *;
             try rep_omega.
           forward.
           forward.
           normalize.
           strip_repr.
           remember (required_size tval) as r.
           forward_loop (
               EX v : Z, EX ls : list int,
               PROP ((Int.unsigned Int.zero <= v)%Z; 
                     (v <= r)%Z;
                     ls = 
                     serialize_tag_loop (r - v)%Z (Z.to_nat v) tval)
               LOCAL (temp _tval (Vint tval);
                      temp _i (Vint (Int.repr ((r * 7) - (v + 1) * 7)%Z));
                      temp _required_size (Vint (Int.repr r));
                      temp _size (Vint (Int.repr (buf_size - 1)));
                      temp _buf__1 (offset_val (v + 1) (Vptr buf_b buf_ofs));
                      temp _end
                      (Vptr buf_b
                            (buf_ofs +
                             Ptrofs.repr (1 + required_size (tag >>u Int.repr 2))
                             - Ptrofs.repr 1)%ptrofs))
               SEP (data_at Tsh (tarray tuchar 1) [Vint e1] (Vptr buf_b buf_ofs);
                    data_at Tsh (tarray tuchar v) (map Vint ls)
                            (offset_val 1 (Vptr buf_b buf_ofs));
                    data_at Tsh (tarray tuchar (buf_size - v - 1)) 
                                    (sublist (v + 1) buf_size default_list) 
                                    (offset_val (v + 1) (Vptr buf_b buf_ofs))))
          break: (EX ls : list int, EX j: int, 
                 PROP (let n := (Z.to_nat r) in
                       ls = serialize_tag_loop 0 n tval)
                 LOCAL (temp _tval (Vint (tag >>u Int.repr 2));
                        temp _i (Vint j);
                        temp _required_size (Vint (Int.repr r));
                        temp _size (Vint (Int.repr (buf_size - 1)));
                        temp _buf__1 (offset_val (len ls + 1) (Vptr buf_b buf_ofs));
                        temp _end
                             (Vptr buf_b
                                   (buf_ofs +
                                    Ptrofs.repr (1 + 
                                                 required_size (tag >>u Int.repr 2))
                                    - Ptrofs.repr 1)%ptrofs))

                 SEP (data_at Tsh (tarray tuchar 1) [Vint e1] (Vptr buf_b buf_ofs);
                      data_at Tsh (tarray tuchar (len ls)) 
                              (map Vint ls)
                              (offset_val 1 (Vptr buf_b buf_ofs));
                      data_at Tsh (tarray tuchar (buf_size - len ls - 1)) 
                                    (sublist (len ls + 1) buf_size default_list) 
                                    (offset_val ((len ls) + 1) (Vptr buf_b buf_ofs)))).
          *** Exists 0%Z.
              Exists (@nil int).
              erewrite data_at_tuchar_zero_array_eq.
              entailer!.
              erewrite <- data_at_app.
              erewrite upd_Znth_unfold.
              erewrite sublist_nil.
              erewrite app_nil_l.
              setoid_rewrite LB.
              replace (1 + (buf_size - 1))%Z with buf_size by nia.
              entailer!.
              all: try setoid_rewrite LB;
                autorewrite with sublist norm; cbn; auto;
                  try rep_omega.
          ***
            Intros v ls.
            forward_if.
           +++
           (*  assert (0 <= v + 1 <= (required_size (tag >>u Int.repr 2))) as VR.
               { rewrite Int.unsigned_repr in H2; try rep_omega.
               by admit. *)
             rewrite Int.unsigned_repr in H2; try rep_omega.
             assert (0 <= v + 1 <= (required_size (tag >>u Int.repr 2))) as VR.
                    admit. 
             unfold test_order_ptrs.
             unfold sameblock.
             subst.
             destruct peq; [simpl  |contradiction].
             apply andp_right.
             { apply derives_trans 
                 with (Q := valid_pointer 
                              (Vptr buf_b (buf_ofs + Ptrofs.repr (v + 1))%ptrofs)).               
                entailer!.
               apply valid_pointer_weak. }
             { assert (0 < buf_size - v - 1)%Z as LD by
                     (try erewrite LB; nia).
               assert (sizeof (tarray tuchar (buf_size - v - 1)) > 0) by (simpl; nia).
               remember (default_val (tarray tuchar buf_size)) as default_list.
               remember (required_size (tag >>u Int.repr 2)) as r.
               assert (data_at Tsh (tarray tuchar (buf_size - v - 1))
                               (sublist (v + 1) buf_size (default_val (tarray tuchar buf_size)))
                               (Vptr buf_b (buf_ofs + Ptrofs.repr (v + 1))%ptrofs)
                               |-- weak_valid_pointer
                               (Vptr buf_b
                                     (buf_ofs +  Ptrofs.repr (1 + r) - Ptrofs.repr 1)%ptrofs)).
               { apply derives_trans 
                   with (Q := valid_pointer 
                                (Vptr buf_b (buf_ofs
                                             + Ptrofs.repr
                                                 (1 + r) - Ptrofs.repr 1)%ptrofs)). 
                 assert (sizeof (tarray tuchar (buf_size - v - 1)) > 0) by (simpl; nia).
                 replace (buf_ofs + Ptrofs.repr (1 + r) - Ptrofs.repr 1)%ptrofs
                   with (buf_ofs + Ptrofs.repr r)%ptrofs.
                 Open Scope Z.
                 erewrite data_at_app_gen
                   with (j1 := r - (v + 1))
                        (j2 := len default_list - r)
                        (ls1 := sublist (v + 1) r default_list)
                        (ls2 := sublist r (len default_list) default_list). 
                 assert ((buf_ofs + Ptrofs.repr (v + 1) + Ptrofs.repr (r - (v + 1)))%ptrofs =
                         (buf_ofs + Ptrofs.repr r)%ptrofs) as PTR.
                 {  ptrofs_compute_add_mul; try rep_omega.
                    f_equal.
                    rep_omega.}
                 rewrite PTR.
                 assert (sizeof (tarray tuchar (len default_list -  r)) > 0).
                 { simpl.
                   setoid_rewrite LB. 
                   nia. }
                 eapply sepcon_valid_pointer2.
                 eapply data_at_valid_ptr; auto.
                 1-5:  replace (Int.unsigned 0%int) with 0%Z in * by auto with ints.
                 4: erewrite sublist_split with (mid := r); subst; auto; try nia.
                 all: try erewrite Zlength_sublist_correct;
                   try nia;  try setoid_rewrite LB; try nia; auto.
                 Focus 3. apply valid_pointer_weak. 
                 try erewrite Zlength_sublist_correct;
                   try nia;  try setoid_rewrite LB; ptrofs_compute_add_mul; try rep_omega.
                 erewrite Ptrofs.sub_add_opp.
                 unfold Ptrofs.neg.
                 normalize.
                 f_equal.
                 rewrite Ptrofs.unsigned_repr.
                 f_equal.
                 nia.
                 rep_omega.  }
               entailer!. }
           +++
             rewrite Int.unsigned_repr in H2; try rep_omega.
             replace (Int.unsigned 0%int) with 0 in * by auto with ints.
             eapply typed_true_ptr_lt in H6.
             assert ( Ptrofs.unsigned buf_ofs +  v + 1 <
                      Ptrofs.unsigned buf_ofs + 1 +
                      required_size (tag >>u Int.repr 2) - 1) as PT.
             { generalize H6.
               unfold Ptrofs.sub.
               ptrofs_compute_add_mul.             
               all: subst; rep_omega_setup; auto with ints; 
                 autorewrite with norm; try rep_omega; try nia. }
             unfold offset_val.
             erewrite split_non_empty_list with 
                 (j2 := (len default_list - (v + 1) - 1)%Z)
                 (ls' := (sublist (v + 1 + 1) buf_size default_list))
                 (ls := (sublist (v + 1) buf_size default_list)).            
             assert (v < required_size tval)%Z by (subst; lia).
             Intros.
             assert (len default_list - (v + 1) - 1 =
                     len (sublist (v + 1 + 1) (len default_list) default_list)) as LEN.
             { erewrite Zlength_sublist_correct.
               nia.
               rewrite LB.
               all: try nia. }
             forward.
             entailer!.
             unfold Int.iwordsize.
             ints_compute_add_mul.
             cbn - [required_size].
             all: try rep_omega.
             repeat forward.
             remember
               (Int.zero_ext 8
                             (Int.repr 128
                                       or (((tag >>u Int.repr 2) >>u
                                                                 Int.repr ((required_size (tag >>u Int.repr 2) - (len ls + 1)) * 7)) & Int.repr 127))%int)%int
               as e_v.
             Exists (v + 1) (ls ++ [e_v]).
             assert (v = len ls) as VLS.
             { subst.
               erewrite loop_len_req_size.
               erewrite Z2Nat_id';
                 erewrite Zmax0r; try nia. }
             entailer!.
             split.
             erewrite Z.add_1_r at 3.
             erewrite Z2Nat.inj_succ.       
             simpl. f_equal. rewrite H5 at 1. 
             replace (required_size (tag >>u Int.repr 2)  - len ls) 
               with (required_size (tag >>u Int.repr 2)  - (len ls + 1) + 1) by nia.
             reflexivity.
             normalize.
             do 2 f_equal. nia.
             replace (required_size (tag >>u Int.repr 2) * 7 - (len ls + 1) * 7)
               with
                 ((required_size (tag >>u Int.repr 2) - (len ls + 1)) * 7) by nia.
             remember
               (Int.zero_ext 8
                             (Int.repr 128
                                       or (((tag >>u Int.repr 2) >>u
                            Int.repr ((required_size (tag >>u Int.repr 2)
                                       - (len ls + 1)) * 7)) & 
                                           Int.repr 127))%int)%int
               as e_v.
             unfold offset_val.
             simpl.
             erewrite <- data_at_tuchar_singleton_array_eq.
             remember (default_val (tarray tuchar buf_size)) as default_list.
             replace (buf_ofs + Ptrofs.repr (len ls + 1) + 1)%ptrofs
               with (buf_ofs +  Ptrofs.repr (len ls + 1 + 1))%ptrofs. 
             
             replace (buf_ofs + Ptrofs.repr ((len ls) + 1))%ptrofs
               with (buf_ofs + 1 + Ptrofs.repr (len ls))%ptrofs. 
             erewrite <- data_at_app.
             erewrite map_app.
             rewrite <- LB.
             entailer!.
             all: replace (Int.unsigned 0%int) with 0%Z in * 
               by (autorewrite with norm; auto);
               autorewrite with list sublist;
               try rep_omega.
             all: ptrofs_compute_add_mul; 
               replace (Ptrofs.unsigned 1%ptrofs) with 1 by auto with ptrofs;
               autorewrite with norm;
               try nia; try rep_omega; f_equal; try nia.
             instantiate (1 := Znth (v + 1) default_list).
             erewrite sublist_split with (mid := v + 1 + 1).
             erewrite sublist_len_1.
             reflexivity.
             all: try setoid_rewrite LB; try nia.
             subst. rep_omega.
           +++
             eapply typed_false_ptr_lt in H6.
             replace (Int.unsigned 0%int) with 0 in * by auto with ints.
             rewrite Int.unsigned_repr in H2; try rep_omega.
             assert ( Ptrofs.unsigned buf_ofs +  v + 1 >=
                      Ptrofs.unsigned buf_ofs + 1 +
                      required_size (tag >>u Int.repr 2) - 1) as PT.
             { generalize H6.
               unfold Ptrofs.sub.
               ptrofs_compute_add_mul.             
               all: subst; rep_omega_setup; auto with ints; 
                 autorewrite with norm; try rep_omega; try nia. }
             assert (required_size tval < buf_size) by (subst; nia).
             assert (v + 1 >= required_size tval)%Z. 
             { subst; lia. } 
             repeat forward.
             assert (v = r \/ v + 1 = r) as V by nia.
             inversion V as [V1 | V2].
             { rewrite V1.
             rewrite Heqr.  
             Exists ls (Int.repr ((r * 7) - (r + 1) * 7)%Z).
             replace (required_size tval - required_size tval)%Z with 0%Z by nia.
             entailer!.
             split.
             replace (required_size (tag >>u Int.repr 2) 
                      - required_size (tag >>u Int.repr 2))%Z with 0%Z by nia.
             reflexivity.
             erewrite Zlength_map in H12.
             setoid_rewrite H12.
             reflexivity.
             replace (required_size (tag >>u Int.repr 2) -
                      required_size (tag >>u Int.repr 2))%Z with 0%Z in * by nia.
             remember (tag >>u Int.repr 2) as tval.
             remember (serialize_tag_loop 0 (Z.to_nat (required_size tval)) tval) as ls.
             assert (required_size tval = len ls) as L.
             {  erewrite Zlength_map in H12.
                subst.
                rewrite <- H12 at 1.
                reflexivity. }
             rewrite L.
             entailer!. }

            { (* erewrite V2 in *.
              rewrite Heqr.  
              lia.
              Exists ls (Int.repr ((r * 7) - r * 7)%Z).   
              replace (required_size tval * 7 - required_size tval * 7)
                with 0%Z by nia.
              erewrite H5 at 2.
              entailer!.
              assert (required_size (tag >>u Int.repr 2) = len ls + 1) as L.
             {  subst. 
                erewrite Zlength_map in V2.
                lia. }
             split.
             admit. (* ls ??? *)
             split.
              replace (required_size (tag >>u Int.repr 2) * 7
                       - required_size (tag >>u Int.repr 2) * 7)
                 with 0%Z by nia.
              auto.
             f_equal.
             lia.
             erewrite Zlength_map in H14.           
              assert (required_size (tag >>u Int.repr 2) = len ls + 1) as L.
             {  subst. 
                erewrite Zlength_map in V2.
                lia. }
             rewrite L.
             repeat erewrite Zlength_map.
             entailer!.   *) admit. }
            subst; rep_omega.
             *** 
               Intros ls j.
               rewrite Int.unsigned_repr in H2; try rep_omega.
               unfold offset_val.
               erewrite split_non_empty_list
                 with (ls' := sublist (len ls + 1 + 1) buf_size default_list)
                      (j2 := (buf_size - (len ls + 1 + 1))%Z)
                      (ofs := (buf_ofs + Ptrofs.repr (len ls + 1))%ptrofs).
               Intros.
               forward.
               unfold POSTCONDITION.
               unfold abbreviate.
               break_let.
               pose proof (req_size_32 tval).
               assert (required_size tval < buf_size) by (subst; lia).
               forward.
               unfold tag_serialize in *.
               rewrite C in *.
               rewrite Int.unsigned_repr in *.
               rewrite_if_b.
                assert ((buf_size - 1 <? required_size (tag >>u Int.repr 2)) = false) as FS.
                { Zbool_to_Prop.
                  nia. }
               rewrite FS in *.
               inversion Heqp.
               unfold offset_val.                   
               erewrite <- data_at_tuchar_singleton_array_eq.
               erewrite <- data_at_app.
               replace (1 + len ls)%Z with (len ls + 1)%Z by nia.
               erewrite <- data_at_app.
               (* setoid_rewrite <- H6. *)
               remember (Int.zero_ext 8 (((tag & Int.repr 3)
                                            << Int.repr 6) or Int.repr 31)%int) as e0.
               remember (Int.zero_ext 8 ((tag >>u Int.repr 2) & Int.repr 127)%int) as e_n.
               replace (buf_ofs + Ptrofs.repr (len ls + 1) + 1)%ptrofs with 
                   (buf_ofs + Ptrofs.repr (len ls + 1 + 1))%ptrofs.
               erewrite <- data_at_app.
               replace (len ls + 1 + 1 + (buf_size - (len ls + 1 + 1))) with buf_size by nia.
               unfold serialize_tag.
               admit.
               all: (autorewrite with sublist;
                     try nia; auto).
               all: try erewrite Zlength_sublist_correct;
                 try nia.
               Focus 7.
               instantiate (1 := Znth (len ls + 1) default_list).
               erewrite sublist_split with (mid := len ls + 1 + 1).
               erewrite sublist_len_1.
               reflexivity.
               all: try setoid_rewrite LB; try  rep_omega.
               all:  try (simpl in H3;
                      subst;
                      erewrite loop_len_req_size;
                      erewrite Z2Nat_id';
                      erewrite Zmax0r;
                      repeat rep_omega).
               all: try setoid_rewrite LB;
                 try (simpl in H3;
                      subst;
                      erewrite loop_len_req_size;
                      erewrite Z2Nat_id';
                      erewrite Zmax0r;
                      repeat rep_omega).
               all: repeat ptrofs_compute_add_mul. 
               replace (Ptrofs.unsigned 1%ptrofs) with 1%Z by auto with ptrofs.
               all: subst; rep_omega_setup; auto with ints; 
                 autorewrite with norm; try rep_omega; try nia.
               f_equal.
               lia.
             *** subst. rep_omega.
Admitted.

