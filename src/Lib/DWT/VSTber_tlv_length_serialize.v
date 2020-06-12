Require Import Core.Core  Core.VstTactics Core.StructNormalizer VstLib DWT.Exec 
        ErrorWithWriter.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_tlv_length.
Require Import Core.Notations Core.SepLemmas ExecBer_tlv_length_serialize. 

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
       Require Import Core.Tactics.
       Zbool_to_Prop.
       nia. }
     repeat forward.
     forward_loop 
      (EX i: int, 
          PROP ()
          LOCAL (temp _len (Vint length);
                 temp _i (Vint i);
                 temp _required_size (Vint (required_size_loop length (Int.repr 40 - i) 1));
                 temp _size (Vint size);
                 temp _buf (Vptr buf_b buf_ofs))
           SEP (data_at Tsh (tarray tuchar buf_size)
                         (default_val (tarray tuchar buf_size))
                         (Vptr buf_b buf_ofs)))
      break: (EX i: int, 
                 PROP ()
                 LOCAL (temp _required_size (Vint (required_size length));
                       temp _len (Vint length);
                       temp _i (Vint i);
                       temp _size (Vint size);
                       temp _buf  (Vptr buf_b buf_ofs))
                  SEP (data_at Tsh (tarray tuchar buf_size)
                         (default_val (tarray tuchar buf_size))
                         (Vptr buf_b buf_ofs))).
     + (* Pre implies Inv *)
       Exists (Int.repr 8).
       entailer!.
     + (* Inv exec fn Break *)
       Intros i.
       forward_if; repeat forward.
       forward_if;
         repeat forward.
       admit.
       Exists (i + Int.repr 8).
       entailer!.
       admit.
       Exists i.
       entailer!.
       admit. (* need to replace j *)
       Exists i.
       entailer!.
       unfold required_size.
       admit.
     + Intro i.
       forward_if.
       unfold POSTCONDITION.
       unfold abbreviate. 
       break_let.
       forward.
       unfold ber_tlv_length_serialize in *; rewrite C in *.
       inversion Heqp.
         rewrite_if_b.
       entailer!. (* fix spec *)

       rewrite H2 in *.
       inversion Heqp.
       reflexivity.
       rewrite H2 in *.
       simpl in Heqp.
       inversion Heqp.
       rewrite if_true by congruence.
       entailer!.
       erewrite <- Heqdefault_list.
       rewrite  <- LB.     
       erewrite split_data_at_sublist_tuchar with (j := 1%Z).
       erewrite sublist_one.
       erewrite data_at_tuchar_singleton_array_eq. 
       Intros.
       repeat forward.
       entailer!.
       admit.
       normalize.
       remember (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr 128 or required_size length))) as e0.
      forward_loop (EX v : Z, EX ls : list int,
    (PROP ( )
     LOCAL (temp _buf (Vptr buf_b (buf_ofs + Ptrofs.repr 1 + Ptrofs.repr v)%ptrofs);
            temp _i (Vint (i - Int.repr 8)); temp _end (Vptr buf_b (buf_ofs + Ptrofs.repr (1 + Int.unsigned (required_size length)))%ptrofs);
            temp _t'1 (Vptr buf_b buf_ofs); temp _required_size (Vint (required_size length)); temp _len (Vint length); temp _size (Vint size))
     SEP (data_at Tsh tuchar (Vint e0) (Vptr buf_b buf_ofs);
          data_at Tsh (tarray tuchar v) (map Vint ls)
                        (offset_val 1 (Vptr buf_b buf_ofs));
          data_at Tsh (tarray tuchar (len default_list - v - 1))
                  (sublist (v + 1) (len default_list) default_list) 
                  (Vptr buf_b (buf_ofs + Ptrofs.repr 1 + Ptrofs.repr v)%ptrofs))))
          break: 
     (EX ls : list int,
    (PROP ( )
     LOCAL (temp _buf (Vptr buf_b (buf_ofs + Ptrofs.repr 1 + Ptrofs.repr v)%ptrofs);
            temp _i (Vint (i - Int.repr 8)); temp _end (Vptr buf_b (buf_ofs + Ptrofs.repr (1 + Int.unsigned (required_size length)))%ptrofs);
            temp _t'1 (Vptr buf_b buf_ofs); temp _required_size (Vint (required_size length)); temp _len (Vint length); temp _size (Vint size))
     SEP (data_at Tsh tuchar (Vint e0) (Vptr buf_b buf_ofs);
          data_at Tsh (tarray tuchar (len ls)) (map Vint ls)
                        (offset_val 1 (Vptr buf_b buf_ofs));
          data_at Tsh (tarray tuchar (len default_list - (len ls) - 1))
                  (sublist (len ls + 1) (len default_list) default_list) 
                  (Vptr buf_b (buf_ofs + Ptrofs.repr 1 + Ptrofs.repr (len ls))%ptrofs)))).

       
       
       forward.
       forward.
       forward.
       
