Require Import Core.Core Core.VstTactics Core.StructNormalizer VstLib
        ErrorWithWriter.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_tlv_length.
Require Import Core.Notations Core.SepLemmas Core.Tactics 
Exec.Ber_tlv_length_serialize. 

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Open Scope Z.

Definition der_tlv_length_serialize_spec : ident * funspec :=
  DECLARE _der_tlv_length_serialize
  WITH l : int, buf_b : block, buf_ofs : ptrofs, buf_size : Z
  PRE[tint, tptr tvoid, tuint]
    PROP(0 <= buf_size <= 32;
         Ptrofs.unsigned buf_ofs + buf_size < Ptrofs.modulus)
    PARAMS(Vint l; (Vptr buf_b buf_ofs); Vint (Int.repr buf_size))
    GLOBALS()
    SEP(data_at Tsh (tarray tuchar buf_size)
                    (default_val (tarray tuchar buf_size)) 
                    (Vptr buf_b buf_ofs))
  POST[tuint]
   
    PROP()
    LOCAL(temp ret_temp 
               (Vint (Int.repr (snd (length_serialize l (Int.repr buf_size))))))
    SEP(let (ls, z) := length_serialize l (Int.repr buf_size) in
        data_at Tsh (tarray tuchar buf_size)
                (map Vint ls ++ sublist (len ls) buf_size 
                     (default_val (tarray tuchar buf_size)))
                (Vptr buf_b buf_ofs)).

Definition Gprog := ltac:(with_library prog [der_tlv_length_serialize_spec]).


Theorem ber_tlv_length_serialize_correct : 
  semax_body Vprog Gprog (normalize_function f_der_tlv_length_serialize composites)
             der_tlv_length_serialize_spec.
Admitted.
(*
 Proof.
  start_function.
  remember (default_val (tarray tuchar buf_size)) as default_list.
  assert (len default_list = buf_size) as LB.
  {  subst; unfold default_val;
        simpl;
        try erewrite Zlength_list_repeat;
        try nia; auto. }
  pose proof (req_size_32 l) as R.
  repeat forward.
  forward_if.
  - forward_if (
       PROP()
       LOCAL()
       SEP(if eq_dec (Int.repr buf_size) 0%int 
           then data_at_ Tsh (tarray tuchar buf_size) (Vptr buf_b buf_ofs) 
           else 
             (data_at Tsh tuchar (Vint (Int.zero_ext 8 (Int.zero_ext 8 l)))
                      (Vptr buf_b buf_ofs) *
              data_at Tsh (tarray tuchar (buf_size - 1)) 
                      (sublist 1 buf_size default_list)
                      (Vptr buf_b (buf_ofs + Ptrofs.repr 1)%ptrofs)))).
    + rewrite <- LB.   
      erewrite split_data_at_sublist_tuchar with (j := 1).
      erewrite sublist_one.
      erewrite data_at_tuchar_singleton_array_eq. 
      Intros.
      repeat forward.
      rewrite_if_b.
      entailer!.
      all: subst; try nia;
        unfold default_val;
        simpl;
        try erewrite Zlength_list_repeat;
        try nia; auto.
    + forward.
      rewrite_if_b.
      entailer!.
    + 
      unfold POSTCONDITION.
      unfold abbreviate. 
      break_let.
      forward.      
       assert ((127 >=? Int.signed l) = true) as C.
       { rewrite Z.geb_le. nia. } 
      break_if; unfold length_serialize in *; rewrite C in *; 
        rewrite_if_b;
        inversion Heqp. all: rewrite_if_b; entailer!.
        assert (buf_size = 0%Z).
        eapply repr_inj_unsigned; strip_repr.
       autorewrite with sublist.
       entailer!.
        assert (buf_size <> 0%Z).
        eapply repr_neq_e in n;
        lia.
       erewrite <- split_non_empty_list.
       entailer!.
       erewrite Int.zero_ext_idem.
       reflexivity.
       all: autorewrite with sublist;
         simpl; auto;
       try rewrite LB in *;
       try setoid_rewrite H7;
       try nia.
  -  assert (127 >=? Int.signed l = false) as C.
     { erewrite Z.geb_leb. Zbool_to_Prop. nia. }
     repeat forward.
     forward_loop 
      (EX i: Z,
          PROP (i = 1 \/ i = 2 \/ i = 3 \/ i = 4; 
                forall j, 0 <= j < i ->
                     (l >> (Int.repr j * Int.repr 8) == 0)%int = false)
          LOCAL (temp _len (Vint l);
                 temp _i (Vint (Int.repr (i * 8)));
                 temp _required_size (Vint (Int.repr i));
                 temp _size (Vint (Int.repr buf_size));
                 temp _buf (Vptr buf_b buf_ofs))
           SEP (data_at Tsh (tarray tuchar buf_size)
                         (default_val (tarray tuchar buf_size))
                         (Vptr buf_b buf_ofs)))
      break: (let r := required_size l in
              PROP ()
              LOCAL (temp _required_size (Vint (Int.repr r));
                     temp _len (Vint l);
                     temp _i (Vint ((Int.repr (r * 8))));
                     temp _size (Vint (Int.repr buf_size));
                     temp _buf (Vptr buf_b buf_ofs))
              SEP (data_at Tsh (tarray tuchar buf_size)
                           (default_val (tarray tuchar buf_size))
                           (Vptr buf_b buf_ofs))).
     + (* Pre implies Inv *)
       Exists 1%Z.
       entailer!.
       intros. replace x with 0 by nia.
       erewrite Int.shr_zero. 
       erewrite Int.signed_eq.
       destruct zeq; 
       try rewrite e in *; auto.
     + (* Inv exec fn Break *)
       Intros i.
       forward_if; repeat forward.
       forward_if;
         repeat forward.
       Exists (i + 1).
       entailer!.
       split.
       intros.
       destruct (zeq j i).
       subst.
       eapply Int.eq_false.
       autorewrite with norm.
       eassumption.
       eapply H3.
       nia.
       do 2 f_equal.
       nia.
       entailer!.
       assert (required_size l = i) as RS.
       eapply required_size_spec; auto.
       autorewrite with norm.
       eassumption.
       subst.
       intuition.
       entailer!.
       replace i with 4 in * by nia.
       assert (required_size l = 4) as RS.
       eapply required_size_spec; auto.
       autorewrite with norm.
       cbn.
       erewrite shr_lt_zero_32.
       break_if; auto.
       unfold Int.lt in Heqb.
       break_if; autorewrite with norm in *.
       replace (Int.signed 0%int) with 0 in * by auto with ints.
       nia.
       congruence.
       rewrite RS.
       intuition.     
     + Intros.
       pose proof (req_size_32 l).
       unfold POSTCONDITION.
       unfold abbreviate. 
       break_let.
       forward_if.
       forward.
       unfold length_serialize in *; rewrite C in *.
       inversion Heqp.
         rewrite_if_b.
       entailer!. 
       repeat break_if; try congruence; try
       inversion Heqp; try eassumption; auto.
       break_if.
       Zbool_to_Prop.
       generalize Heqb.
       strip_repr.
       intro. lia.
       inversion Heqp.
       autorewrite with sublist.
       erewrite sublist_same_gen; auto.
       setoid_rewrite LB. lia.
       erewrite <- Heqdefault_list.
       rewrite  <- LB.     
       erewrite split_data_at_sublist_tuchar with (j := 1%Z).
       erewrite sublist_one.
       erewrite data_at_tuchar_singleton_array_eq.
       all: try nia.
       Intros. 
        assert (buf_size <> 0) as BUF by lia. 
       repeat forward.
       normalize.
       erewrite Int.zero_ext_idem.
       remember (required_size l) as r.
       remember (Int.zero_ext 8 (Int.repr (128 or r)))%int as e0.      
       remember (Int.repr (r * 8 - 8))%int as i.     
     forward_loop 
    (EX v : Z, EX ls : list int,
    (PROP ((Int.unsigned Int.zero <= v)%Z; 
           (v <= required_size l)%Z;
           ls = 
           serialize_length_loop_app (r - v)%Z (Z.to_nat v) l)
     LOCAL (temp _buf (Vptr buf_b (buf_ofs + Ptrofs.repr 1 + Ptrofs.repr v)%ptrofs);
            temp _i (Vint (Int.repr ((r * 8) - (v + 1) * 8)%Z)); 
            temp _end (Vptr buf_b (buf_ofs
                      + Ptrofs.repr (1 + Int.unsigned (Int.repr r))))%ptrofs;
            temp _t'1 (Vptr buf_b buf_ofs); 
            temp _required_size (Vint (Int.repr r));
            temp _len (Vint l); temp _size (Vint (Int.repr buf_size)))
     SEP (data_at Tsh tuchar (Vint e0) (Vptr buf_b buf_ofs);
          data_at Tsh (tarray tuchar v) 
                  (map Vint ls)
                        (offset_val 1 (Vptr buf_b buf_ofs));
          data_at Tsh (tarray tuchar (buf_size - v - 1))
                  (sublist (v + 1) buf_size default_list) 
                  (Vptr buf_b (buf_ofs + Ptrofs.repr 1 + Ptrofs.repr v)%ptrofs))))
     break: 
    (EX ls : list int, EX j : int,          
    (PROP (let r := required_size l in
           let n :=  (Z.to_nat r) in
         ls = serialize_length_loop_app 0 n l)
     LOCAL (temp _buf (Vptr buf_b (buf_ofs + Ptrofs.repr 1
                                   + Ptrofs.repr (len ls))%ptrofs);
            temp _i (Vint j);
            temp _end (Vptr buf_b (buf_ofs + Ptrofs.repr (1 + r))%ptrofs);
            temp _t'1 (Vptr buf_b buf_ofs);
            temp _required_size (Vint (Int.repr r)); 
            temp _len (Vint l); temp _size (Vint (Int.repr buf_size)))
     SEP (data_at Tsh tuchar (Vint e0) (Vptr buf_b buf_ofs);
          data_at Tsh (tarray tuchar (len ls)) (map Vint ls)
                        (offset_val 1 (Vptr buf_b buf_ofs));
          data_at Tsh (tarray tuchar (buf_size - (len ls) - 1))
                  (sublist (len ls + 1) buf_size default_list) 
                  (Vptr buf_b (buf_ofs + Ptrofs.repr 1
                               + Ptrofs.repr (len ls))%ptrofs)))). 
      * Exists 0%Z.
        Exists (@nil int).                
        erewrite data_at_tuchar_zero_array_eq.
        entailer!.
        replace (len (default_val (tarray tuchar buf_size))) 
           with buf_size by (setoid_rewrite LB; lia).
        auto.
        replace (len (default_val (tarray tuchar buf_size))) 
           with buf_size by (setoid_rewrite LB; lia).
        entailer!.
        cbn; auto.
      * Intros v ls.
        forward_if; try nia.
        entailer!.
        
         assert (0 < (buf_size - v - 1)) as LD by admit.
        assert (sizeof (tarray tuchar (len (default_val (tarray tuchar buf_size)) - v - 1)) > 0).
        { simpl.
          erewrite Zmax0r.
          setoid_rewrite LB. 
          nia.
          setoid_rewrite LB. 
          nia. }
        unfold test_order_ptrs.
        unfold sameblock.
        subst.
        destruct peq; [  |contradiction].
        apply andp_right.
        apply derives_trans 
          with (Q := valid_pointer 
                       (Vptr buf_b (buf_ofs + Ptrofs.repr (1 + v))%ptrofs)).
        entailer!.
        apply valid_pointer_weak.
        apply derives_trans 
          with (Q := valid_pointer 
                       (Vptr buf_b (buf_ofs
                                    + Ptrofs.repr (1 + required_size l))%ptrofs)).
        eapply sepcon_valid_pointer2.
        remember (default_val (tarray tuchar buf_size)) as default_list.
        remember (required_size l) as r.
        erewrite data_at_app_gen
          with (j1 := 1 + r - (v + 1))
               (j2 := buf_size - (1 + r))
               (ls1 := sublist (v + 1) (1 + r) default_list)
               (ls2 := sublist (1 + r) buf_size default_list). 
        assert ((buf_ofs + Ptrofs.repr (1 + v) + Ptrofs.repr (1 + r - (v + 1)))%ptrofs =
        (buf_ofs + Ptrofs.repr (1 + r))%ptrofs) as PTR.
        {  ptrofs_compute_add_mul; try rep_omega.
           f_equal.
           rep_omega. }
        rewrite PTR.
        assert (0 < ((buf_size - r - 1))) as LDD by admit.
        assert (sizeof (tarray tuchar (buf_size - r - 1)) > 0).
        { simpl.
          erewrite Zmax0r; nia. }
        entailer!.
        1-5: replace (Int.unsigned 0%int) with 0%Z in * by auto with ints;
          subst; try setoid_rewrite LB; autorewrite with sublist; try list_solve. 
        auto.
        ptrofs_compute_add_mul; try rep_omega.
        apply valid_pointer_weak.
        ++
        erewrite split_non_empty_list with 
            (j2 := (len default_list - (v + 1) - 1)%Z)
            (ls' := (sublist (v + 1 + 1) buf_size default_list)).
        eapply typed_true_ptr_lt in H7.
        assert (v < required_size l)%Z.
        { replace (Int.unsigned 0%int) with 0 in * by auto with ints.
          generalize H7. ptrofs_compute_add_mul. subst. nia.
          all: subst; rep_omega_setup; auto with ints; 
            autorewrite with norm; try rep_omega; try nia. }
        Intros.
        assert (len default_list - (v + 1) - 1 =
                len (sublist (v + 1 + 1) buf_size default_list)) as LEN.
        { erewrite Zlength_sublist_correct.
          nia.
          replace (Int.unsigned 0%int) with 0%Z in * by auto with ints.
          all: lia. }
        forward.
        entailer!.
        unfold Int.iwordsize.
        ints_compute_add_mul.
        cbn - [required_size].
        all: try rep_omega.
        auto with ints.
        repeat forward.
        remember (Int.zero_ext 8 
                               (l >> (Int.repr ((required_size l - (v + 1)) * 8))))%int
          as e_v.
        normalize.
        Exists (v + 1) (ls ++ [e_v]).
        assert  (v = len ls) as VLS.
        { subst.
          erewrite loop_len_req_size.
          replace (Int.unsigned 0%int) with 0%Z in * by (autorewrite with norm; auto).        
          erewrite Z2Nat_id'.
          erewrite Zmax0r.
          nia.
          nia. }
        entailer!.
        split.
        erewrite Z.add_1_r at 3.
        erewrite Z2Nat.inj_succ.       
        simpl. f_equal. rewrite H6 at 1. 
        replace (required_size l - len ls)  with (required_size l - (len ls + 1) + 1) by nia.
        reflexivity.
        replace (Int.unsigned 0%int) with 0%Z in * by (autorewrite with norm; auto).     
        nia. auto with ints.
        split. 
        do 3 f_equal. nia.
        do 2 f_equal. nia.
        repeat erewrite Int.zero_ext_idem.
        
        replace ((required_size l - ((len ls) + 1)) * 8)%Z with 
               (required_size l * 8 - ((len ls) + 1) * 8)%Z by nia. 
        remember
          (Int.zero_ext 8
                        (l >> Int.repr (required_size l * 8 - ((len ls) + 1) * 8)))%int
                 as e_v.
        unfold offset_val.
        simpl.
        replace (1 + (len ls)) with ((len ls) + 1) by nia.
        erewrite <- data_at_tuchar_singleton_array_eq.
        remember (default_val (tarray tuchar buf_size)) as default_list.

        replace (buf_ofs + Ptrofs.repr (1 + ((len ls) + 1)))%ptrofs with
            (buf_ofs + 1 + Ptrofs.repr ((len ls) + 1))%ptrofs. 

        replace (buf_ofs + Ptrofs.repr ((len ls) + 1) + 1)%ptrofs with
            (buf_ofs + 1 + Ptrofs.repr ((len ls) + 1))%ptrofs.       
 
        replace (buf_ofs + Ptrofs.repr ((len ls) + 1))%ptrofs with (buf_ofs + 1 + Ptrofs.repr (len ls))%ptrofs.

        erewrite <- data_at_app.
        erewrite <- data_at_app.
        erewrite <- data_at_app.
        erewrite map_app.
        replace buf_size with  (len default_list). 
        
        entailer!.
        autorewrite with list sublist.
        nia.
        setoid_rewrite <- LEN.
        lia.
        
        all: try setoid_rewrite <- LEN.
        all: replace (Int.unsigned 0%int) with 0%Z in * by (autorewrite with norm; auto);
          autorewrite with  sublist;
          try rep_omega.
        all: try setoid_rewrite LB.
         all: ptrofs_compute_add_mul;
          replace (Ptrofs.unsigned 1%ptrofs) with 1 by auto with ptrofs;
          autorewrite with norm;
          try nia; try rep_omega; f_equal; try nia.
         instantiate (1 := Znth (v + 1) default_list).
         erewrite sublist_split with (mid := v + 1 + 1).
         erewrite sublist_len_1.
         reflexivity.
         all: try setoid_rewrite LB; try lia.
          eapply typed_true_ptr_lt in H7.
        assert (v < required_size l)%Z.
        { replace (Int.unsigned 0%int) with 0 in * by auto with ints.
          generalize H7. ptrofs_compute_add_mul. subst. nia.
          all: subst; rep_omega_setup; auto with ints; 
            autorewrite with norm; try rep_omega; try nia. }
        lia.
        
         eapply typed_true_ptr_lt in H7.
        assert (v < required_size l)%Z.
        { replace (Int.unsigned 0%int) with 0 in * by auto with ints.
          generalize H7. ptrofs_compute_add_mul. subst. nia.
          all: subst; rep_omega_setup; auto with ints; 
            autorewrite with norm; try rep_omega; try nia. } 
        lia.
         eapply typed_true_ptr_lt in H7.
        assert (v < required_size l)%Z.
        { replace (Int.unsigned 0%int) with 0 in * by auto with ints.
          generalize H7. ptrofs_compute_add_mul. subst. nia.
          all: subst; rep_omega_setup; auto with ints; 
            autorewrite with norm; try rep_omega; try nia. }
         erewrite Zlength_sublist_correct. lia.
        all: try lia.
        setoid_rewrite LB. lia.
         ++ 
        eapply typed_false_ptr_lt in H7.
         assert (required_size l < buf_size) by nia.
        assert (v >= required_size l)%Z. 
        { replace (Int.unsigned 0%int) with 0%Z in * by auto with ints.
          generalize H7.
          ptrofs_compute_add_mul.
          subst.
         
          all: subst; rep_omega_setup;
            auto with ints; autorewrite with norm; try rep_omega; try nia.
        }
        repeat forward.
        assert (v = required_size l) as V.
        subst. nia.
        rewrite V.
        rewrite Heqr.  
        Exists ls (Int.repr ((r * 8) - (r + 1) * 8)%Z).
        replace (required_size l - required_size l)%Z with 0%Z by nia.
        entailer!.
        split.
         replace (required_size l - required_size l)%Z with 0%Z by nia.
        reflexivity.
        erewrite Zlength_map in H13.
        setoid_rewrite H13.
        reflexivity.
        replace (required_size l - required_size l)%Z with 0%Z in * by nia.
        remember (serialize_length_loop_app 0 
                  (Z.to_nat (required_size l)) l) as ls.
        assert (required_size l = len ls) as L.
        {  erewrite Zlength_map in H13.
           subst.
           rewrite <- H13 at 1.
            replace (required_size l - required_size l)%Z with 0 by nia.
           reflexivity. }
         replace (required_size l - required_size l)%Z with 0 by nia.
         erewrite Zlength_map in H13.
         rewrite L.
         entailer!.
      * Intros ls j.
        unfold POSTCONDITION.
        unfold abbreviate.
        pose proof (req_size_32 l).
        assert (required_size l < buf_size) by nia.
        forward.
        unfold length_serialize in *.
        rewrite C in *.
        rewrite Int.unsigned_repr_eq in Heqp.
        rewrite Zmod_small in Heqp.
        erewrite <- Z.ltb_lt in H3.
        rewrite H3 in Heqp.
        inversion Heqp.
        unfold serialize_length_app.
        unfold offset_val.
        erewrite <- data_at_tuchar_singleton_array_eq.
        erewrite <- data_at_app.
        replace (1 + len ls)%Z with (len ls + 1)%Z by nia.
        erewrite <- data_at_app.
        setoid_rewrite <- H4.
        replace (len ls + 1 +
                 (buf_size
                  - len ls - 1))%Z
          with buf_size.
        replace (len (Int.zero_ext 8 (Int.repr 128 or Int.repr (required_size l))%int :: ls)) with 
            (len ls + 1)%Z by
            (autorewrite with sublist list norm;
             nia).
        autorewrite with sublist.
        normalize.
        entailer!.
         all: (autorewrite with sublist list norm;
                     try nia; auto).
         erewrite Zlength_sublist_correct.
        nia.
        all: try (subst;
        erewrite loop_len_req_size;
        erewrite Z2Nat_id';
        erewrite Zmax0r;
        rep_omega).
        setoid_rewrite LB. lia.
        autorewrite with sublist.
        erewrite Zlength_sublist_correct; try  lia.
        subst.
        erewrite loop_len_req_size.
        erewrite Z2Nat_id'.
        erewrite Zmax0r.
        all: rep_omega.
       * lia.
Admitted.
        
*)
