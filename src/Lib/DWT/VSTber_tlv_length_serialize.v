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
    PROP((32 <= buf_size)%Z;
         (Ptrofs.unsigned buf_ofs + buf_size < Ptrofs.modulus)%Z)
    PARAMS(Vint length; (Vptr buf_b buf_ofs); Vint size)
    GLOBALS()
    SEP(data_at Tsh (tarray tuchar buf_size)
                    (default_val (tarray tuchar buf_size)) 
                    (Vptr buf_b buf_ofs))
  POST[tuint]
    let (ls, z) := ber_tlv_length_serialize length size in
    PROP()
    LOCAL(temp ret_temp (Vint z))
    SEP(if eq_dec ls [] 
        then data_at Tsh (tarray tuchar buf_size)
                         (default_val (tarray tuchar buf_size))
                         (Vptr buf_b buf_ofs) 
        else data_at Tsh (tarray tuchar buf_size)
                         (map (fun x => Vint (Int.zero_ext 8 (Int.zero_ext 8 x))) ls
                              ++ sublist (len ls) buf_size 
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
      (EX i: int,
          PROP ((0 <= Int.unsigned i)%Z;
              forall j, 0 <= Int.unsigned j < Int.unsigned i 
                     -> length >> (j * Int.repr 8)%int == 0 = false)
          LOCAL (temp _len (Vint length);
                 temp _i (Vint (i* Int.repr 8)%int);
                 temp _required_size (Vint i);
                 temp _size (Vint size);
                 temp _buf (Vptr buf_b buf_ofs))
           SEP (data_at Tsh (tarray tuchar buf_size)
                         (default_val (tarray tuchar buf_size))
                         (Vptr buf_b buf_ofs)))
      break: (PROP ()
              LOCAL (temp _required_size (Vint (required_size length));
                     temp _len (Vint length);
                     temp _i  (Vint ((required_size length) * Int.repr 8)%int);
                     temp _size (Vint size);
                     temp _buf  (Vptr buf_b buf_ofs))
              SEP (data_at Tsh (tarray tuchar buf_size)
                           (default_val (tarray tuchar buf_size))
                           (Vptr buf_b buf_ofs))).
     + (* Pre implies Inv *)
       Exists (Int.repr 1).
       entailer!.
       intros.
       autorewrite with norm in *.
       assert (Int.unsigned j = 0%Z) as J by nia.
       assert (j = 0).
       eapply unsigned_eq_eq.
       normalize.
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
       assert (Int.unsigned (i * Int.repr 8)%int < 8 * 4)%Z by admit.
       forward_if; repeat forward.
       forward_if;
         repeat forward.
       Exists (i + 1).
       entailer!.
       split.
       intros.
       destruct (zeq (Int.unsigned j) (Int.unsigned i)).
       assert (i = j).
       eapply unsigned_eq_eq. nia.
       subst.
       eapply Int.eq_false.
       eassumption.
       eapply H3.
       replace (Int.unsigned (i + 1)) with (Int.unsigned i + 1)%Z in *.
       nia.
       admit. (* need unsigned i < 32 *)
       f_equal.
       erewrite Int.mul_add_distr_l.
       auto with ints.
       entailer!.
       assert (required_size length = i) as R.
       eapply required_size_spec.
       admit. (* from unsigned i < 32 *)
       eassumption.
       eassumption.
       subst.
       intuition.
       entailer!.
       assert (required_size length = i) as R.
       assert (i = Int.repr 4) by admit.
       subst.
       eapply required_size_spec.
       auto.
       eassumption.
       admit. (* add lemma forall l, l >> 32 = 0 *)
       subst. intuition.
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
       congruence.
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
       remember (Int.zero_ext 8
                              (Int.zero_ext 8
                                            (Int.repr 128 or required_size length))) as e0.
       remember (required_size length) as r.
       remember length as l.
      forward_loop 
    (EX v : Z, EX ls : list int,
    (PROP (ls = 
           serialize_length_loop
             ((r * Int.repr 8)%int - Int.repr 8)
             (Z.to_nat v) l)
     LOCAL (temp _buf (Vptr buf_b (buf_ofs + Ptrofs.repr 1 + Ptrofs.repr v)%ptrofs);
            temp _i (Vint ((r * Int.repr 8)%int - Int.repr ((v + 1) * 8)%Z)); 
            temp _end (Vptr buf_b (buf_ofs + Ptrofs.repr (1 + Int.unsigned r))%ptrofs);
            temp _t'1 (Vptr buf_b buf_ofs); temp _required_size (Vint r);
            temp _len (Vint length); temp _size (Vint size))
     SEP (data_at Tsh tuchar (Vint e0) (Vptr buf_b buf_ofs);
          data_at Tsh (tarray tuchar v) 
                  (map (fun x : int => Vint (Int.zero_ext 8 (Int.zero_ext 8 x))) ls)
                        (offset_val 1 (Vptr buf_b buf_ofs));
          data_at Tsh (tarray tuchar (len default_list - v - 1))
                  (sublist (v + 1) (len default_list) default_list) 
                  (Vptr buf_b (buf_ofs + Ptrofs.repr 1 + Ptrofs.repr v)%ptrofs))))
     break: 
    (EX ls : list int, EX j : int,          
    (PROP (let r := required_size l in
           let n :=  (Z.to_nat (Int.unsigned r)) in
         ls = serialize_length_loop ((r - 1) * Int.repr 8)%int n  length)
     LOCAL (temp _buf (Vptr buf_b (buf_ofs + Ptrofs.repr 1 + Ptrofs.repr (len ls))%ptrofs);
            temp _i (Vint j);
            temp _end (Vptr buf_b (buf_ofs + Ptrofs.repr (1 + Int.unsigned r))%ptrofs);
            temp _t'1 (Vptr buf_b buf_ofs);
            temp _required_size (Vint r); 
            temp _len (Vint length); temp _size (Vint size))
     SEP (data_at Tsh tuchar (Vint e0) (Vptr buf_b buf_ofs);
          data_at Tsh (tarray tuchar (len ls)) (map (fun x : int => 
                           Vint (Int.zero_ext 8 (Int.zero_ext 8 x))) ls)
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
        Intros.
        forward.
        entailer!.
        admit.
        repeat forward.
        entailer!.
        admit.
        remember (Int.zero_ext 8
                               (Int.zero_ext 8 
                                             (Int.shr length
                                                      ((r * Int.repr 8)%int 
                                                       - Int.repr ((v + 1) * 8)))))
          as e_v.
        Exists (v + 1)%Z (ls ++ [e_v]).
        entailer!.
        split.
        replace (Z.to_nat (v + 1)) with (S (Z.to_nat (v)))%nat.
        simpl.
        admit. (* true, need lemma *)
        erewrite <- Z2Nat.inj_succ.
        nia.
        admit.
        admit.
        remember (serialize_length_loop ((required_size length * Int.repr 8)%int - Int.repr 8) (Z.to_nat v) length) as ls.
        remember (Int.zero_ext 8 (Int.zero_ext 8 (Int.shr length ((required_size length * Int.repr 8)%int  - Int.repr ((v + 1) * 8)))))
                 as e_v.
        unfold offset_val.
        simpl.
        replace (1 + v)%Z with (v + 1)%Z by nia.
        erewrite <- data_at_tuchar_singleton_array_eq.
        normalize.
        replace (buf_ofs + Ptrofs.repr (v + 1) + 1)%ptrofs with
            (buf_ofs + 1 + Ptrofs.repr (v + 1))%ptrofs.
        replace (buf_ofs + Ptrofs.repr (v + 1))%ptrofs with (buf_ofs + 1 + Ptrofs.repr v)%ptrofs.
        replace (buf_ofs + Ptrofs.repr (1 + (v + 1)))%ptrofs with
            (buf_ofs + 1 + Ptrofs.repr (v + 1))%ptrofs.          
        erewrite <- data_at_app.
        erewrite <- data_at_app.
        erewrite <- data_at_app.
        assert ((map Vint ls ++ [Vint e_v]) = (map Vint (ls ++ [e_v]))) by admit.
        admit.
        1-16: admit.
        ++
        repeat forward.
        Exists ls (((required_size length) * Int.repr 8) - Int.repr ((v + 1) * 8)).
        entailer!.
        split.
        assert (Z.to_nat v = (Z.to_nat (Int.unsigned (required_size length)))) by admit.
        setoid_rewrite H3.
        admit.
        normalize.
        admit.
        remember (serialize_length_loop ((required_size length) * Int.repr 8 - Int.repr 8) (Z.to_nat v) length) as ls.
        replace v with (len ls).
        entailer!.
        admit.
      * Intros ls j.
        unfold POSTCONDITION.
        unfold abbreviate. 
        break_let.
        forward.
        unfold ber_tlv_length_serialize in *.
        rewrite C in *.
        rewrite H2 in Heqp.
        inversion Heqp.
        unfold serialize_length.
        rewrite if_false by congruence.
        unfold offset_val.
        simpl.
        erewrite <- data_at_tuchar_singleton_array_eq.
        erewrite <- data_at_app.
        replace (1 + len ls)%Z with (len ls + 1)%Z by nia.
        erewrite <- data_at_app.
        setoid_rewrite <- H3.
        replace (len ls + 1 + (len (default_val (tarray tuchar buf_size)) - len ls - 1))%Z
          with buf_size.
        replace (len ((Int.repr 128 or required_size length) :: ls)) with 
            (len ls + 1)%Z by
            (autorewrite with sublist list norm;
             nia).
        replace  (len (default_val (tarray tuchar buf_size))) with buf_size.
        entailer!.
         all : (autorewrite with sublist list norm;
                     try nia; auto).
                erewrite Zlength_sublist_correct.
        nia.
        setoid_rewrite LB; try nia. 
        admit.
        setoid_rewrite LB; try nia. 
        admit.
        admit. 
     Admitted.
         
        
