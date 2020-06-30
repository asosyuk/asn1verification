Require Import Core.Core Core.VstTactics Core.StructNormalizer VstLib DWT.Exec 
        ErrorWithWriter.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_tlv_length.
Require Import Core.Notations Core.SepLemmas Core.Tactics ExecBer_tlv_length_serialize. 

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Open Scope IntScope.

Definition der_tlv_length_serialize_spec : ident * funspec :=
  DECLARE _der_tlv_length_serialize
  WITH length : int, buf_b : block, buf_ofs : ptrofs, size : int, buf_size : Z
  PRE[tint, tptr tvoid, tuint]
    PROP((32 < buf_size)%Z;
          buf_size = Int.unsigned size;
         (Ptrofs.unsigned buf_ofs + buf_size < Ptrofs.modulus)%Z)
    PARAMS(Vint length; (Vptr buf_b buf_ofs); Vint size)
    GLOBALS()
    SEP(data_at Tsh (tarray tuchar buf_size)
                    (default_val (tarray tuchar buf_size)) 
                    (Vptr buf_b buf_ofs))
  POST[tuint]
    let (ls, z) := ber_tlv_length_serialize length size in
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr z)))
    SEP(if eq_dec ls [] 
        then data_at Tsh (tarray tuchar buf_size)
                         (default_val (tarray tuchar buf_size))
                         (Vptr buf_b buf_ofs) 
        else data_at Tsh (tarray tuchar buf_size)
                         (map Vint ls ++ sublist (len ls) buf_size 
                             (default_val (tarray tuchar buf_size)))
                         (Vptr buf_b buf_ofs)).

Definition Gprog := ltac:(with_library prog [der_tlv_length_serialize_spec]).

Theorem ber_tlv_length_serialize_correct' : 
  semax_body Vprog Gprog (normalize_function f_der_tlv_length_serialize composites)
             der_tlv_length_serialize_spec.
Proof.
  start_function.
  remember (default_val (tarray tuchar buf_size)) as default_list.
  assert (len default_list = buf_size) as LB.
  {  subst; unfold default_val;
        simpl;
        try erewrite Zlength_list_repeat;
        try nia; auto. }
  repeat forward.
  forward_if.
  - forward_if (
       PROP()
       LOCAL()
       SEP(if eq_dec size 0 
           then data_at_ Tsh (tarray tuchar buf_size) (Vptr buf_b buf_ofs) 
           else 
             (data_at Tsh tuchar (Vint (Int.zero_ext 8 (Int.zero_ext 8 length)))
                      (Vptr buf_b buf_ofs) *
              data_at Tsh (tarray tuchar (len default_list - 1)) 
                      (sublist 1 (len default_list) default_list)
                      (Vptr buf_b (buf_ofs + Ptrofs.repr 1)%ptrofs)))).
    + rewrite <- LB.     
      erewrite split_data_at_sublist_tuchar with (j := 1%Z).
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
    + unfold POSTCONDITION.
      unfold abbreviate. 
      break_let.
      forward.      
       assert ((127 >=? Int.signed length)%Z = true) as C.
       { rewrite Z.geb_le. nia. } (* need a generic tactic to deal with such rewrites *)
      break_if; unfold ber_tlv_length_serialize in *; rewrite C in *; 
        rewrite_if_b.
       inversion Heqp.
       rewrite if_true by congruence.
       entailer!.
       inversion Heqp.
       rewrite if_false by congruence.
       entailer!.
       erewrite <- split_non_empty_list.
       entailer!.
       rewrite LB.
        erewrite Int.zero_ext_idem.
       reflexivity.
       all: autorewrite with sublist;
         simpl; auto;
       try rewrite LB in H7;
       try setoid_rewrite H7;
       try nia.
  -  assert ((127 >=? Int.signed length)%Z = false) as C.
     { erewrite Z.geb_leb.
       
       Zbool_to_Prop.
       nia. }
     repeat forward.
     forward_loop 
      (EX i: Z,
          PROP ((0 <= i)%Z;
              forall j, 0 <= j < i 
                     -> length >> (Int.repr j * Int.repr 8)%int == 0 = false)
          LOCAL (temp _len (Vint length);
                 temp _i (Vint (Int.repr (i * 8)));
                 temp _required_size (Vint (Int.repr i));
                 temp _size (Vint size);
                 temp _buf (Vptr buf_b buf_ofs))
           SEP (data_at Tsh (tarray tuchar buf_size)
                         (default_val (tarray tuchar buf_size))
                         (Vptr buf_b buf_ofs)))
      break: (PROP ()
              LOCAL (temp _required_size (Vint (Int.repr (required_size length)));
                     temp _len (Vint length);
                     temp _i  (Vint ((Int.repr ((required_size length) * 8))));
                     temp _size (Vint size);
                     temp _buf  (Vptr buf_b buf_ofs))
              SEP (data_at Tsh (tarray tuchar buf_size)
                           (default_val (tarray tuchar buf_size))
                           (Vptr buf_b buf_ofs))).
     + (* Pre implies Inv *)
       Exists 1%Z.
       entailer!.
       intros.
       autorewrite with norm in *.
       assert (x = 0)%Z by nia.
       subst.
       replace (0 * Int.repr 8) with 0 by auto with ints.
       erewrite Int.shr_zero.
       erewrite Int.signed_eq.
       destruct zeq.
       rewrite e in *.
       replace (Int.signed 0) with 0%Z in * by auto with ints.
       nia.
       auto.
     + (* Inv exec fn Break *)
       Intros i.
       assert ((i * 8) < 8 * 4)%Z by admit.
       forward_if; repeat forward.
       forward_if;
         repeat forward.
       Exists (i + 1)%Z.
       entailer!.
       split.
       intros.
       destruct (zeq j i).
       subst.
       eapply Int.eq_false.
       autorewrite with norm.
       eassumption.
       eapply H4.
       nia.
       f_equal.
       f_equal.
       nia.
       entailer!.
       assert (required_size length = i) as R.
       eapply required_size_spec.
       admit. (* from unsigned i < 32 *)
       eassumption.
       autorewrite with norm.
       eassumption.
       subst.
       intuition.
       entailer!.
     + Intros.
       forward_if.
       unfold POSTCONDITION.
       unfold abbreviate. 
       break_let.
       forward.
       unfold ber_tlv_length_serialize in *; rewrite C in *.
       inversion Heqp.
         rewrite_if_b.
       entailer!. 
       repeat break_if; try congruence; try
       inversion Heqp; try eassumption; auto.
       break_if; try
       entailer!.
       break_if.
       admit.
       inversion Heqp.
       congruence.
       erewrite <- Heqdefault_list.
       rewrite  <- LB.     
       erewrite split_data_at_sublist_tuchar with (j := 1%Z).
       erewrite sublist_one.
       erewrite data_at_tuchar_singleton_array_eq.
       all: try nia.
       Intros.
       repeat forward.
       entailer!.
       admit. (* add lemmas *)
       normalize.
       erewrite Int.zero_ext_idem.
       remember ((Int.zero_ext 8 (Int.repr 128 or Int.repr (required_size length)))) as e0.
       remember ((required_size length)) as r.
       remember length as l.
       remember (Int.repr (r * 8) - Int.repr 8) as i.
       pose proof (req_size_32 length).
     forward_loop 
    (EX v : Z, EX ls : list int,
    (PROP ((Int.unsigned Int.zero <= v)%Z; 
           (v <= required_size l)%Z;
           ls = 
           serialize_length_loop_app (r - v)%Z (Z.to_nat v) l)
     LOCAL (temp _buf (Vptr buf_b (buf_ofs + Ptrofs.repr 1 + Ptrofs.repr v)%ptrofs);
            temp _i (Vint (Int.repr ((r * 8) - (v + 1) * 8)%Z)); 
            temp _end (Vptr buf_b (buf_ofs + Ptrofs.repr (1 + Int.unsigned (Int.repr r))))%ptrofs;
            temp _t'1 (Vptr buf_b buf_ofs); temp _required_size (Vint (Int.repr r));
            temp _len (Vint length); temp _size (Vint size))
     SEP (data_at Tsh tuchar (Vint e0) (Vptr buf_b buf_ofs);
          data_at Tsh (tarray tuchar v) 
                  (map Vint ls)
                        (offset_val 1 (Vptr buf_b buf_ofs));
          data_at Tsh (tarray tuchar (len default_list - v - 1))
                  (sublist (v + 1) (len default_list) default_list) 
                  (Vptr buf_b (buf_ofs + Ptrofs.repr 1 + Ptrofs.repr v)%ptrofs))))
     break: 
    (EX ls : list int, EX j : int,          
    (PROP (let r := required_size l in
           let n :=  (Z.to_nat r) in
         ls = serialize_length_loop_app 0  n length)
     LOCAL (temp _buf (Vptr buf_b (buf_ofs + Ptrofs.repr 1 + Ptrofs.repr (len ls))%ptrofs);
            temp _i (Vint j);
            temp _end (Vptr buf_b (buf_ofs + Ptrofs.repr (1 + r))%ptrofs);
            temp _t'1 (Vptr buf_b buf_ofs);
            temp _required_size (Vint (Int.repr r)); 
            temp _len (Vint length); temp _size (Vint size))
     SEP (data_at Tsh tuchar (Vint e0) (Vptr buf_b buf_ofs);
          data_at Tsh (tarray tuchar (len ls)) (map Vint ls)
                        (offset_val 1 (Vptr buf_b buf_ofs));
          data_at Tsh (tarray tuchar (len default_list - (len ls) - 1))
                  (sublist (len ls + 1) (len default_list) default_list) 
                  (Vptr buf_b (buf_ofs + Ptrofs.repr 1 + Ptrofs.repr (len ls))%ptrofs)))). 
      * Exists 0%Z.
        Exists (@nil int).
        erewrite data_at_tuchar_zero_array_eq.
        entailer!.
        entailer!.
        cbn; auto.
      * Intros v ls.
        forward_if.
        entailer!.
        admit.
        ++
        erewrite split_non_empty_list with 
            (j2 := (len default_list - (v + 1) - 1)%Z)
            (ls' := (sublist (v + 1 + 1) (len default_list) default_list)).
        eapply typed_true_ptr_lt in H8.
        assert (required_size length < Int.unsigned size)%Z.
        { generalize H3.
          rewrite Int.unsigned_repr;
          subst; auto; try nia. cbn - [required_size]. nia. }
          assert (v < required_size length)%Z. 
        { replace (Int.unsigned 0) with 0%Z in * by auto with ints.
          generalize H8.
          ptrofs_compute_add_mul.
          subst.
          nia.
          all:
            subst;
            rep_omega_setup;
            auto with ints; autorewrite with norm; try rep_omega; try nia. }
        Intros.
        forward.
        entailer!.
        unfold Int.iwordsize.
        ints_compute_add_mul.
        cbn - [required_size].
        subst.
        replace (Int.unsigned 0) with 0%Z in H5.
        all: try rep_omega.
        auto with ints.
        repeat forward.
        remember (Int.zero_ext 8
                               (length >> 
                                       (Int.repr ((required_size length - (v + 1)) * 8))))
          as e_v.
        normalize.
        Exists (v + 1)%Z (ls ++ [e_v]).
        entailer!.
        split.
        erewrite Z.add_1_r at 3.
        erewrite Z2Nat.inj_succ.       
        simpl.        
        f_equal.
        f_equal.
        nia.
        replace (Int.unsigned 0) with 0%Z in H5.
        nia.
        auto with ints.
        split.
        do 3 f_equal.
        nia.
        do 2 f_equal.
        nia.
        remember (serialize_length_loop_app
                    (required_size length - v) (Z.to_nat v) length) as ls.
        repeat erewrite Int.zero_ext_idem.
        replace ((required_size length - (v + 1)) * 8)%Z with 
               (required_size length * 8 - (v + 1) * 8)%Z by nia. 
        remember (Int.zero_ext 8 (length >> Int.repr (required_size length * 8 - (v + 1) * 8)))
                 as e_v.
        unfold offset_val.
        simpl.
        replace (1 + v)%Z with (v + 1)%Z by nia.
        erewrite <- data_at_tuchar_singleton_array_eq.
        remember (default_val (tarray tuchar (Int.unsigned size))) as default_list.
        replace (buf_ofs + Ptrofs.repr (1 + (v + 1)))%ptrofs with
            (buf_ofs + 1 + Ptrofs.repr (v + 1))%ptrofs.      

        replace (buf_ofs + Ptrofs.repr (v + 1) + 1)%ptrofs with
            (buf_ofs + 1 + Ptrofs.repr (v + 1))%ptrofs.        
        replace (buf_ofs + Ptrofs.repr (v + 1))%ptrofs with (buf_ofs + 1 + Ptrofs.repr v)%ptrofs.
        erewrite <- data_at_app.
        erewrite <- data_at_app.
        erewrite <- data_at_app.
        erewrite map_app.
        entailer!.
        autorewrite with list sublist.
        subst.
        erewrite  loop_len_req_size.
        replace (Int.unsigned 0) with 0%Z in H5.
        erewrite Z2Nat_id'.
        erewrite Zmax0r.
        nia.
        nia.
        auto with ints.
         all : (autorewrite with sublist list norm;
                     try nia; auto).
         erewrite Zlength_sublist_correct.
         nia.
         all: try setoid_rewrite LB.
         all:  replace (Int.unsigned 0) with 0%Z in H5 by auto with ints.
         all: try nia.
         erewrite Zlength_sublist_correct.
         subst.
         erewrite   loop_len_req_size.
         all: admit.
        ++
        eapply typed_false_ptr_lt in H8.
         assert (required_size length < Int.unsigned size)%Z.
        { generalize H3.
          rewrite Int.unsigned_repr;
          subst; auto; try nia. cbn - [required_size]. nia. }
        assert (v >= required_size length)%Z. 
        { replace (Int.unsigned 0) with 0%Z in * by auto with ints.
          generalize H8.
          ptrofs_compute_add_mul.
          subst.
          nia.
          all: subst; rep_omega_setup;
            auto with ints; autorewrite with norm; try rep_omega; try nia.
 }
        repeat forward.
        assert (v = required_size length) as V.
        subst. nia.
        rewrite V.
        rewrite Heqr.  
        Exists ls (Int.repr ((r * 8) - (r + 1) * 8)%Z).
        replace (required_size length - required_size length)%Z with 0%Z by nia.
       (* assert (required_size length - Int.repr (Int.unsigned (required_size length)) = 0) as R.
        {  erewrite Int.repr_unsigned.
           autorewrite with norm.
           auto. } *)
        entailer!.
        split.
         replace (required_size length - required_size length)%Z with 0%Z by nia.
        reflexivity.
        erewrite Zlength_map in H14.
        setoid_rewrite H14.
        reflexivity.
        remember (serialize_length_loop_app 0 
                  (Z.to_nat (required_size length)) length) as ls.
        assert (required_size length = len ls) as L.
        {  erewrite Zlength_map in H14.
           subst.
           rewrite <- H14 at 1.
            replace (required_size length - required_size length)%Z with 0%Z by nia.
           reflexivity. }
         replace (required_size length - required_size length)%Z with 0%Z by nia.
         erewrite Zlength_map in H14.
         admit.
      * Intros ls j.
        pose proof (req_size_32 length).
        assert (required_size length < Int.unsigned size)%Z.
        { generalize H3.
          ints_compute_add_mul.
          subst; auto. subst; admit. }
        unfold POSTCONDITION.
        unfold abbreviate. 
        break_let.
        forward.
        unfold ber_tlv_length_serialize in *.
        rewrite C in *.
        rewrite H3 in Heqp.
        inversion Heqp.
        unfold serialize_length_app.
        rewrite if_false by congruence.
        unfold offset_val.
        simpl.
        erewrite <- data_at_tuchar_singleton_array_eq.
        erewrite <- data_at_app.
        replace (1 + len ls)%Z with (len ls + 1)%Z by nia.
        erewrite <- data_at_app.
        setoid_rewrite <- H4.
        replace (len ls + 1 + (len (default_val (tarray tuchar (Int.unsigned size))) - len ls - 1))%Z
          with  (Int.unsigned size).
        replace (len ((Int.repr 128 or required_size length) :: ls)) with 
            (len ls + 1)%Z by
            (autorewrite with sublist list norm;
             nia).
        replace (len (default_val (tarray tuchar  (Int.unsigned size)))) with  (Int.unsigned size).
        entailer!.
         all : (autorewrite with sublist list norm;
                     try nia; auto).
         erewrite Zlength_sublist_correct.
        nia.
        setoid_rewrite LB; try nia. 
        all: try (subst;
        erewrite loop_len_req_size;
        erewrite Z2Nat_id';
        erewrite Zmax0r;
        rep_omega).
        cbn.
        nia.
        erewrite Zmax0r in H13.
        setoid_rewrite H13.
        nia.
        rewrite LB.
        subst.
        erewrite loop_len_req_size.
        erewrite Z2Nat_id'.
        erewrite Zmax0r.
        nia.
        rep_omega.
Admitted.
         
        
