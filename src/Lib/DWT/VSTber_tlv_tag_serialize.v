Require Import Core.Core Core.VstTactics Core.StructNormalizer VstLib
        ErrorWithWriter.
Require Import Core.Tactics.
               
Require Import VST.floyd.proofauto.
Require Import Clight.ber_tlv_tag ExecBer_tlv_tag_serialize.
Require Import Core.Notations Core.SepLemmas.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Open Scope Z.

Definition ber_tlv_tag_serialize_spec : ident * funspec :=
  DECLARE _ber_tlv_tag_serialize
  WITH tag : int, buf_b : block, buf_ofs : ptrofs, size : Z, buf_size : Z
  PRE[tuint, tptr tvoid, tuint]
    PROP(0 <= size < Int.modulus;
         0 <= buf_size < Int.modulus;
         Ptrofs.unsigned buf_ofs + size < Ptrofs.modulus;
         Ptrofs.unsigned buf_ofs + buf_size < Ptrofs.modulus)
    PARAMS(Vint tag; (Vptr buf_b buf_ofs); Vint (Int.repr size))
    GLOBALS()
    SEP(data_at Tsh (tarray tuchar buf_size)
                    (default_val (tarray tuchar buf_size)) 
                    (Vptr buf_b buf_ofs))
  POST[tuint]
    PROP()
    LOCAL(temp ret_temp
               (Vint (Int.repr (snd (tag_serialize tag
                                                           (Int.repr size))))))
    SEP(let ls := (fst (tag_serialize tag (Int.repr size))) in
        if eq_dec ls [] 
        then data_at Tsh (tarray tuchar buf_size)
                         (default_val (tarray tuchar buf_size))
                         (Vptr buf_b buf_ofs) 
        else data_at Tsh (tarray tuchar buf_size)
                         (map Vint ls 
                              ++ sublist (len ls) buf_size 
                             (default_val (tarray tuchar buf_size)))
                         (Vptr buf_b buf_ofs)).
(* Definition Gprog := ltac:(with_library prog [ber_tlv_tag_serialize_spec]).

Open Scope IntScope.

Theorem ber_tlv_tag_serialize_correct : 
  semax_body Vprog Gprog (normalize_function f_ber_tlv_tag_serialize composites)
             ber_tlv_tag_serialize_spec.
Proof.
  start_function.
  remember (Int.shru tag (Int.repr 2)) as tval.
  remember (Int.zero_ext 8 (((tag & Int.repr 3) << Int.repr 6) or tval)) as e0. 
  remember (default_val (tarray tuchar size)) as default_list.
  remember (Int.zero_ext 8 (((tag & Int.repr 3) << Int.repr 6) or Int.repr 31)) as e1.
  assert (len default_list = size) as LB.
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
       SEP(if eq_dec (Int.repr size) 0 
           then data_at_ Tsh (tarray tuchar size) (Vptr buf_b buf_ofs) 
           else data_at Tsh (tarray tuchar size)
                        (upd_Znth 0 (default_val (tarray tuchar size))
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
     break_if; unfold ber_tlv_tag_serialize in *;
     repeat rewrite_if_b;
     eapply Z.ge_le in H1;
     eapply Z.geb_le in H1;
     rewrite H1 in *.
      * rewrite_if_b.
        entailer!.           
      * unfold snd.
        unfold fst.
        rewrite if_false by congruence.
        erewrite upd_Znth_unfold.
        setoid_rewrite LB.
        entailer!.
        setoid_rewrite LB.
        assert (size <> 0%Z) by admit.
        nia.
  - (* 30 < tag *) 
    forward_if (
       PROP()
       LOCAL(if eq_dec (Int.repr size) 0 
             then temp _buf__1 (Vptr buf_b buf_ofs)
             else temp _buf__1 (offset_val 1 (Vptr buf_b buf_ofs));
             if eq_dec (Int.repr size) 0 
             then temp _size (Vint (Int.repr size))
             else temp _size (Vint (Int.repr (size - 1)));
            temp _tval (Vint tval))
       SEP(if eq_dec (Int.repr size) 0 
           then data_at Tsh (tarray tuchar size)
                     (default_val (tarray tuchar size)) (Vptr buf_b buf_ofs)  
           else data_at Tsh (tarray tuchar size)
                        (upd_Znth 0 (default_val (tarray tuchar size))
                                  (Vint e1)) (Vptr buf_b buf_ofs))).
    + rewrite <- LB.     
      erewrite split_data_at_sublist_tuchar with (j := 1%Z).
      erewrite sublist_one.
      erewrite data_at_tuchar_singleton_array_eq.
      Intros.
      repeat forward.
      repeat rewrite_if_b.
      entailer!.
      setoid_rewrite LB.
      auto.
      erewrite upd_Znth_unfold.
      erewrite sublist_nil.
      erewrite app_nil_l.
      remember (default_val (tarray tuchar size)) as default_list.
      remember (Int.zero_ext 8 (((tag & Int.repr 3) << Int.repr 6) or Int.repr 31)) as e1.     
      erewrite <- split_non_empty_list with
          (j1 := size)
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
      assert (size = 0%Z) as S by admit.
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
                 temp _size (Vint (Int.repr size));
                 temp _buf__1 (Vptr buf_b buf_ofs))
          SEP (data_at Tsh (tarray tuchar size)
                       (default_val (tarray tuchar size))
                       (Vptr buf_b buf_ofs)))
      break: (let r := required_size (tag >>u(Int.repr 2)) in
              PROP ()
              LOCAL (temp _required_size (Vint (Int.repr r));
                     temp _tval (Vint (tag >>u Int.repr 2));
                     temp _i (Vint (Int.repr (r * 7)));
                     temp _size (Vint (Int.repr size));
                     temp _buf__1 (Vptr buf_b buf_ofs))
                 SEP (data_at Tsh (tarray tuchar size)
                              default_list
                              (Vptr buf_b buf_ofs))).
         * Exists 1%Z.
           entailer!.
           intros. 
           replace x with 0%Z by nia.
           erewrite Int.shru_zero.
           destruct  (Int.shru tag (Int.repr 2) == 0) eqn : T.
           eapply int_eq_e in T.
           rewrite T in H1.
           cbv in H1.
           congruence.
           auto.
         * Intro i.
           forward_if; repeat forward.
           forward_if;
            repeat forward.
           rewrite Int.unsigned_repr_eq in H2.
           rewrite Zmod_small in H2.
           entailer!.
           rep_omega.
           Exists (i + 1)%Z.
           rewrite Int.unsigned_repr_eq in H2.
           rewrite Zmod_small in H2; try rep_omega.
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
           rewrite Int.unsigned_repr_eq in H2.
           rewrite Zmod_small in H2; try rep_omega.
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
           unfold ber_tlv_tag_serialize in *.
           rewrite C in *.
           repeat rewrite_if_b.          
           entailer!.
           rewrite Int.unsigned_repr_eq in H2.
           rewrite Zmod_small in H2; try rep_omega.           
           assert (size = 0)%Z.
           erewrite Int.int_to_unsigned_eq in e.
           erewrite Int.unsigned_repr in e.
           replace (Int.unsigned 0) with 0%Z in * by auto with ints.
           auto.
           rep_omega.
           admit.
           rewrite Zmod_small in H2; try rep_omega.
           subst.
           rep_omega.
           unfold Int.modulus.
           unfold two_power_nat.
           simpl.
           subst. nia.
           ++
              assert (size <> 0%Z) as S by admit.
              repeat forward. 
         forward_loop (EX i: Z, 
          PROP (i = 1%Z \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5; 
                forall j, 0 <= j < i ->
                     (Int.shru tval (Int.repr j * Int.repr 7) == 0)%int = false)
          LOCAL (temp _tval (Vint (tag >>u (Int.repr 2)));
                 temp _i (Vint (Int.repr (i * 7)));
                 temp _required_size (Vint (Int.repr i));
                 temp _size (Vint (Int.repr (size - 1)));
                 temp _buf__1 (offset_val 1 (Vptr buf_b buf_ofs)))
          SEP ((data_at Tsh (tarray tuchar size)
                        (upd_Znth 0 (default_val (tarray tuchar size))
                                  (Vint e1)) (Vptr buf_b buf_ofs))))
      break: (let r := required_size (tag >>u (Int.repr 2)) in
              PROP ()
              LOCAL (temp _required_size (Vint (Int.repr r));
                     temp _tval (Vint (tag >>u Int.repr 2));
                     temp _i (Vint (Int.repr (r * 7)));
                     temp _size (Vint (Int.repr (size - 1)));
                     temp _buf__1 (offset_val 1 (Vptr buf_b buf_ofs)))
                 SEP ((data_at Tsh (tarray tuchar size)
                               (upd_Znth 0 (default_val (tarray tuchar size)) 
                                         (Vint e1)) (Vptr buf_b buf_ofs)))).
         * Exists 1%Z.
           entailer!.
           intros. 
           replace x with 0%Z by nia.
           erewrite Int.shru_zero.
           destruct  (Int.shru tag (Int.repr 2) == 0) eqn : T.
           eapply int_eq_e in T.
           rewrite T in H1.
           cbv in H1.
           congruence.
           auto.
         * Intro i.
           forward_if; repeat forward.
           forward_if;
             repeat forward.
           rewrite Int.unsigned_repr_eq in H2.
           rewrite Zmod_small in H2.
           entailer!.
           rep_omega.
           Exists (i + 1)%Z.
           rewrite Int.unsigned_repr_eq in H2.
           rewrite Zmod_small in H2; try rep_omega.
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
           rewrite Int.unsigned_repr_eq in H2.
           rewrite Zmod_small in H2; try rep_omega.
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
           unfold ber_tlv_tag_serialize in *.
           rewrite C in *.          
           rewrite Int.unsigned_repr_eq.
           rewrite Zmod_small; try rep_omega.
           rewrite Int.unsigned_repr_eq in H2.
           rewrite Zmod_small in H2; try rep_omega.
           repeat rewrite_if_b.  
           repeat rewrite_if_b. 
           replace (size - 1 <? required_size (tag >>u Int.repr 2)) with true by admit.
           rewrite_if_b.
           unfold fst.
           rewrite_if_b.
           entailer!.
           admit.
           forward.
           forward.
           normalize.
           autorewrite with norm.
           Ltac unsig_repr := rewrite Int.unsigned_repr_eq;
           rewrite Zmod_small; try rep_omega.
           unsig_repr. 
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
                      temp _size (Vint (Int.repr (size - 1)));
                      temp _buf__1 (offset_val (v + 1) (Vptr buf_b buf_ofs));
                      temp _end
                      (Vptr buf_b
                            (buf_ofs +
                             Ptrofs.repr (1 + required_size (tag >>u Int.repr 2))
                             - Ptrofs.repr 1)%ptrofs))
               SEP (data_at Tsh (tarray tuchar 1) [Vint e1] (Vptr buf_b buf_ofs);
                    data_at Tsh (tarray tuchar v) (map Vint ls)
                            (offset_val 1 (Vptr buf_b buf_ofs));
                    data_at Tsh (tarray tuchar (size - v - 1)) 
                                    (sublist (v + 1) size default_list) 
                                    (offset_val (v + 1) (Vptr buf_b buf_ofs))))
          break: (EX ls : list int, EX j: int, 
                 PROP (let n := (Z.to_nat r) in
                       ls = serialize_tag_loop 0 n tval)
                 LOCAL (temp _tval (Vint (tag >>u Int.repr 2));
                        temp _i (Vint j);
                        temp _required_size (Vint (Int.repr r));
                        temp _size (Vint (Int.repr (size - 1)));
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
                      data_at Tsh (tarray tuchar (size - len ls - 1)) 
                                    (sublist (len ls + 1) size default_list) 
                                    (offset_val ((len ls) + 1) (Vptr buf_b buf_ofs)))).
          *** Exists 0%Z.
              Exists (@nil int).
              erewrite data_at_tuchar_zero_array_eq.
              entailer!.
              erewrite <- data_at_app.
              erewrite upd_Znth_unfold.
              erewrite sublist_nil.
              erewrite app_nil_l.
              replace (len (default_val (tarray tuchar size))) with size.
              entailer!.
              replace (1 + (size - 1))%Z with size by nia.
              entailer!.
              all: try setoid_rewrite LB;
                autorewrite with sublist norm; cbn; auto;
                  try rep_omega.
          ***
            Intros v ls.
            forward_if.
           +++
             assert (0 <= v + 1 <= (required_size (tag >>u Int.repr 2))) as VR by admit.
             unfold test_order_ptrs.
             unfold sameblock.
             subst.
             destruct peq; [simpl  |contradiction].
             apply andp_right.
             { apply derives_trans 
                 with (Q := valid_pointer 
                              (Vptr buf_b (buf_ofs + Ptrofs.repr (v + 1))%ptrofs)).
               entailer!.
                rewrite Int.unsigned_repr_eq in H2.
                rewrite Zmod_small in H2; try rep_omega.
                entailer!.
               apply valid_pointer_weak. }
             {  rewrite Int.unsigned_repr_eq in H2.
                rewrite Zmod_small in H2; try rep_omega.
               assert (0 < size - v - 1)%Z as LD by
                     (try erewrite LB; nia).
               assert (sizeof (tarray tuchar (size - v - 1)) > 0) by (simpl; nia).
               remember (default_val (tarray tuchar size)) as default_list.
               remember (required_size (tag >>u Int.repr 2)) as r.
               assert (data_at Tsh (tarray tuchar (size - v - 1))
                               (sublist (v + 1) size (default_val (tarray tuchar size)))
                               (Vptr buf_b (buf_ofs + Ptrofs.repr (v + 1))%ptrofs)
                               |-- weak_valid_pointer
                               (Vptr buf_b
                                     (buf_ofs +  Ptrofs.repr (1 + r) - Ptrofs.repr 1)%ptrofs)).
               { apply derives_trans 
                   with (Q := valid_pointer 
                                (Vptr buf_b (buf_ofs
                                             + Ptrofs.repr
                                                 (1 + r) - Ptrofs.repr 1)%ptrofs)). 
                 assert (sizeof (tarray tuchar (size - v - 1)) > 0) by (simpl; nia).
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
                    rep_omega. }
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
             unfold offset_val.
             erewrite split_non_empty_list with 
                 (j2 := (len default_list - (v + 1) - 1)%Z)
                 (ls' := (sublist (v + 1 + 1) size default_list))
                 (ls := (sublist (v + 1) size default_list)).
             eapply typed_true_ptr_lt in H6.
             assert (v < required_size tval)%Z.
             { replace (Int.unsigned 0%int) with 0 in * by auto with ints.
               generalize H6.
               unfold Ptrofs.sub.
               ptrofs_compute_add_mul. 
               all: subst; rep_omega_setup; auto with ints; 
                 autorewrite with norm; try rep_omega; try nia.  }
             Intros.
             assert (len default_list - (v + 1) - 1 =
                     len (sublist (v + 1 + 1) (len default_list) default_list)) as LEN.
             { erewrite Zlength_sublist_correct.
               nia.
               rewrite LB.
               replace (Int.unsigned 0%int) with 0%Z in * by auto with ints.
               all: nia. }
             forward.
             entailer!.
             unfold Int.iwordsize.
             ints_compute_add_mul.
             cbn - [required_size].
             replace (Int.unsigned 0%int) with 0%Z in H4 by (autorewrite with norm; auto).   
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
               replace (Int.unsigned 0%int) with 0%Z in * by (autorewrite with norm; auto).   
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
             remember (default_val (tarray tuchar size)) as default_list.
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
           +++
             eapply typed_false_ptr_lt in H6.
             assert (required_size tval < size) by nia.
             assert (v + 1 >= required_size tval)%Z. 
             { replace (Int.unsigned 0%int) with 0 in * by auto with ints.
               generalize H6.
               unfold Ptrofs.sub.
               ptrofs_compute_add_mul. 
                all: subst; rep_omega_setup; auto with ints; 
                 autorewrite with norm; try rep_omega; try nia. }
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
            { 
              Exists ls (Int.repr ((r * 7) - r * 7)%Z).
              admit. }
             *** 
               Intros ls j.
               unfold offset_val.
               erewrite split_non_empty_list
                 with (ls' := sublist (len ls + 1 + 1) size default_list)
                      (j2 := (size - (len ls + 1 + 1))%Z)
                      (ofs := (buf_ofs + Ptrofs.repr (len ls + 1))%ptrofs).
               Intros.
               forward.
               unfold POSTCONDITION.
               unfold abbreviate.
               break_let.
               pose proof (req_size_32 tval).
               assert (required_size tval < size) by nia.
               forward.
               unfold ber_tlv_tag_serialize in *.
               rewrite C in *.
               rewrite Int.unsigned_repr_eq in *.
               rewrite Zmod_small in *.
               rewrite_if_b.
                assert ((size - 1 <? required_size (tag >>u Int.repr 2)) = false) as S.
                { Zbool_to_Prop.
                  nia. }
               rewrite S in *.
               inversion Heqp.
               unfold serialize_tag.
               rewrite if_false by congruence.
               unfold offset_val.                   
               erewrite <- data_at_tuchar_singleton_array_eq.
               erewrite <- data_at_app.
               replace (1 + len ls)%Z with (len ls + 1)%Z by nia.
               erewrite <- data_at_app.
               setoid_rewrite <- H3.
               remember (Int.zero_ext 8 (((tag & Int.repr 3)
                                            << Int.repr 6) or Int.repr 31)%int) as e0.
               remember (Int.zero_ext 8 ((tag >>u Int.repr 2) & Int.repr 127)%int) as e_n.
               replace (buf_ofs + Ptrofs.repr (len ls + 1) + 1)%ptrofs with 
                   (buf_ofs + Ptrofs.repr (len ls + 1 + 1))%ptrofs.
               erewrite <- data_at_app.
               replace (len ls + 1 + 1 + (size - (len ls + 1 + 1))) with size by nia.
               autorewrite with sublist list norm.
               erewrite map_app.
               entailer!.
               all: (autorewrite with sublist list norm;
                     try nia; auto).
               all: try erewrite Zlength_sublist_correct;
                 try nia.
               Focus 6.
               instantiate (1 := Znth (len ls + 1) default_list).
               erewrite sublist_split with (mid := len ls + 1 + 1).
               erewrite sublist_len_1.
               reflexivity.
               all: try setoid_rewrite LB; try  rep_omega.
               all: try setoid_rewrite LB;
                 try (simpl in H3;
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
               f_equal.
               nia.
               all: subst; rep_omega_setup; auto with ints; 
                 autorewrite with norm; try rep_omega; try nia.
             *** subst. rep_omega.
Admitted.
*)
