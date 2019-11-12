Require Import Core.Tactics Core.PtrLemmas.
Require Import StructTact.StructTactics Psatz.
Require Import SepLemmas.
Require Import VstSpec AbstractSpec.
Require Import VST.floyd.proofauto Psatz.
Require Import Clight.INTEGER.
Arguments valid_pointer p : simpl never.

Lemma body_asn_strtoimax_lim : semax_body Vprog Gprog f_asn_strtoimax_lim
                                          asn_strtoimax_lim_vst_spec.
Proof.
  start_function.
  pose (upper_boundary := (
         (Int64.divs
            (Int64.shru (Int64.not (Int64.repr (Int.signed (Int.repr 0))))
                        (Int64.repr (Int.unsigned (Int.repr 1))))
            (Int64.repr (Int.signed (Int.repr 10)))))).
  pose (last_digit_max := ((Int64.mods
                                    (Int64.shru
                                       (Int64.not (Int64.repr 0))
                                       (Int64.repr 1))
                                    (Int64.repr 10)))).
  rename H into EQB.
  rename H0 into LEN.
  all: repeat forward; try entailer!.         
  1-2: break_and; inversion H7.
  destruct Z.ltb eqn:IFCON.
  - (* str < end' = true *)
    all: Intros.
    forward_if; apply Z.ltb_lt in IFCON.
    + (* Valid pointer proof *)
      { unfold test_order_ptrs; simpl.
        destruct peq; [simpl|contradiction].
        apply andp_right.
        apply derives_trans with (Q := valid_pointer (Vptr end'_b str_ofs)).
        entailer!.
        apply valid_pointer_weak.
        apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
        entailer!.
        apply valid_pointer_weak. }
    + (*  srt >= end' from forward_if : contradiction *)
      forward.
      apply typed_true_ptr_ge in H.
      rewrite Z.geb_le in H; Lia.lia.
    + (*  str < end' = true from forward_if, go further in the branch *)
      rewrite EQB in H; apply typed_false_ptr_ge in H.
      rewrite Z.gtb_lt in H.
      assert (0 < Ptrofs.unsigned end'_ofs - Ptrofs.unsigned str_ofs)
        by Lia.lia.
      destruct ls.
      replace (Zlength []) with (0) in LEN by reflexivity.
      Lia.lia.
      erewrite split_non_empty_list with (ls' := ls) (i := i) (ofs := str_ofs).
      Intros.
      repeat forward.
      normalize.
      pose (sep_precondition :=
              SEP  (
                   valid_pointer (Vptr end'_b end'_ofs);
                   valid_pointer (Vptr str_b str_ofs);
                   data_at sh_str tschar (Vbyte i) (Vptr str_b str_ofs);
                   data_at sh_str (tarray tschar (Zlength ls)) (map Vbyte ls)
                           (Vptr str_b (Ptrofs.add str_ofs Ptrofs.one));
                   data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs)
                           (Vptr end_b end_ofs);
                   data_at sh_intp tlong v (Vptr intp_b intp_ofs))).
      normalize.
      forward_if (
          if Byte.signed i =? 45
          then PROP(1 < Zlength ls)
               LOCAL(temp _sign (Vint (Int.repr (-1)));
                     temp _str (Vptr end'_b
                                     (Ptrofs.add str_ofs (Ptrofs.repr 1)));
                     temp _end (Vptr end_b end_ofs); 
                     temp _intp (Vptr intp_b intp_ofs);
                     temp _last_digit_max
                          (Vlong (Int64.add last_digit_max Int64.one));
                     temp _upper_boundary (Vlong upper_boundary))
               sep_precondition
          else if Byte.signed i =? 43
               then PROP(1 < Zlength ls)
                    LOCAL(temp _str (Vptr end'_b 
                                          (Ptrofs.add str_ofs (Ptrofs.repr 1)));
                         temp _end (Vptr end_b end_ofs); 
                     temp _intp (Vptr intp_b intp_ofs))
                    sep_precondition
               else !!(Byte.signed i =? 43 = false /\
                       Byte.signed i =? 45 = false)).
      * (* if *str = '-' = Int.repr 45 *)
        admit.
      * (* if *str = '+' *)
        admit.
      * (* default case *) 
        admit.
      * (* Loop *)
        repeat break_if;
          unfold sep_precondition.
        ** forward.
           remember (Ptrofs.add str_ofs Ptrofs.one) as str_ofs'.

           Definition value_until j l := 
             (value (Z_of_string (sublist 0 j l))).

           remember (Int64.unsigned upper_boundary) as ub.
           remember (i :: ls) as ls'.
           forward_loop (
               EX j : Z, EX vl : Z, 
                 let i' := Ptrofs.add str_ofs (Ptrofs.repr (j + 1)) in
                 PROP(0 <= j <= Zlength ls;
                      Ptrofs.unsigned str_ofs + j + 1 < Ptrofs.modulus)
                 LOCAL(temp _end (Vptr end_b end_ofs); 
                       temp _intp (Vptr intp_b intp_ofs);
                       temp _str (Vptr end'_b i');
                       temp _value (Vlong (Int64.repr (value_until j ls))) ;
                       temp _sign (Vint (Int.repr (-1)));
                       temp _upper_boundary (Vlong upper_boundary);
                       temp _last_digit_max
                            (Vlong (Int64.add last_digit_max Int64.one)))
                 SEP(
                   valid_pointer (Vptr end'_b str_ofs) ;
                   valid_pointer (Vptr end'_b end'_ofs) ;

                   (* str |-> i *)                  
                   data_at sh_str tschar (Vbyte i)
                           (Vptr end'_b str_ofs);
                   
                   (* str + 1 |-> sublist 1 (j + 1) ls *)
                   data_at sh_str (tarray tschar j)
                           (map Vbyte (sublist 0 j ls))
                            (Vptr end'_b str_ofs');
                   
                   (* str + j + 1 |-> sublist (j + 1) |ls'| ls'  *)
                   data_at sh_str (tarray tschar (Zlength ls - j))
                           (map Vbyte (sublist j (Zlength ls) ls))
                           (Vptr end'_b i') ; 

                   data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs)
                           (Vptr end_b end_ofs) ;
                   
                   data_at sh_intp tlong v (Vptr intp_b intp_ofs)))
               
           (* FIX break condition *)         
           break: (EX j : Z, 
                   PROP()
                   LOCAL(
                   if (Ptrofs.unsigned str_ofs' + j >=? Zlength ls)
                   then  temp _value (Vlong (Int64.repr ((value (Z_of_string ls)))))
                   else  if (value (Z_of_string ls)) <? ub
                         then temp _value (Vlong (Int64.repr ((value (Z_of_string ls)))))
                         else temp _value (Vlong (Int64.repr (-(value (Z_of_string ls)))));
                   
                   if (Ptrofs.unsigned str_ofs' + j >=? Zlength ls)
                   then temp _sign (Vint (Int.repr (-1)))
                   else if (value (Z_of_string ls)) <? ub
                   then temp _sign (Vint (Int.repr (-1)))
                   else temp _sign (Vint (Int.repr 1));


                   temp _end (Vptr end_b end_ofs); 
                   temp _intp (Vptr intp_b intp_ofs);
                   temp _str (Vptr end'_b 
                              (Ptrofs.add str_ofs 
                                          (Ptrofs.repr (Zlength ls)))))

                   SEP(
                     
                    valid_pointer (Vptr end'_b end'_ofs);
                    valid_pointer (Vptr end'_b str_ofs);
                    data_at sh_str (tarray tschar (Zlength ls)) 
                            (map Vbyte ls) (Vptr end'_b str_ofs); 
                    data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs) 
                            (Vptr end_b end_ofs);
                    data_at sh_intp (tlong) v (Vptr intp_b intp_ofs))).
           ***
             Exists 0 0.
             entailer!.
             autorewrite with sublist.
             auto with zarith.
             entailer!.
             erewrite data_at_zero_array_eq.
             replace (Zlength (i :: ls) - 0 - 1) with (Zlength (ls)).
             replace (sublist 1 (Zlength (i :: ls)) (i :: ls)) with ls.
             entailer!.
             all: try (erewrite sublist_1_cons || autorewrite with sublist);
               autorewrite with sublist; (reflexivity || auto with zarith || auto).
         *** Intros j vl.
             forward.
             forward_if.
             { unfold test_order_ptrs; simpl.
               destruct peq; [simpl|contradiction].
               apply andp_right.
               destruct (Z_lt_le_dec j (Zlength ls)).
               * apply derives_trans with (Q := valid_pointer
                                        (Vptr end'_b (Ptrofs.add str_ofs 
                                                        (Ptrofs.repr (j + 1))))).
                 entailer!.
                 apply valid_pointer_weak.
               * apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
                 entailer!.
                 replace end'_ofs with (Ptrofs.add str_ofs (Ptrofs.repr (j + 1))).
                 apply valid_pointer_weak.
                 {
                   autorewrite with sublist in LEN.
                   replace (Zlength ls) with j in LEN by nia.
                   assert (Ptrofs.unsigned str_ofs + 1 + j = Ptrofs.unsigned end'_ofs) by nia.
                   unfold Ptrofs.add.
                   replace end'_ofs with (Ptrofs.repr (Ptrofs.unsigned end'_ofs))
                     by auto with ints.
                   f_equal.
                   rewrite Ptrofs.unsigned_repr_eq.
                   rewrite Zmod_small.
                   nia.
                   assert (0 <= Ptrofs.unsigned str_ofs).
                   destruct str_ofs.
                   unfold Ptrofs.unsigned.
                   simpl.
                   all: nia. }
               * apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
                 entailer!.
                 apply valid_pointer_weak.
             }

             Proposition read_char_sublist : forall (A : Type) j (ls : list A),
                 0 <= j <= Zlength ls ->
                 0 < Zlength (sublist j (Zlength ls) ls) ->
                 exists i : A, (sublist j (Zlength ls) ls) = 
                      i :: (sublist (j + 1) (Zlength ls) ls). 
               Admitted.
                 
            
             assert (0 < Zlength (sublist j (Zlength ls) ls)).
             { subst.
               rewrite_comparison.
               autorewrite with sublist in *|-.
               autorewrite with sublist.
               unfold Ptrofs.add in *.
               rewrite Ptrofs.unsigned_repr in *.
               rewrite Ptrofs.unsigned_repr in *.
               all: replace (Ptrofs.unsigned Ptrofs.one) with 1 in * by reflexivity.
               lia.
               all: rewrite <-initialize.max_unsigned_modulus in *.
               all: pose proof Ptrofs.unsigned_range str_ofs. 
               all: try lia.
               rewrite Ptrofs.unsigned_repr.
               all: nia.
               }
             edestruct read_char_sublist with (j := j) (ls := ls) as [i0 Sub];
               try nia.
             erewrite Sub.

             replace (Zlength ls - j) with (Zlength
                                              ((i0::(sublist (j + 1) (Zlength ls) ls)))).
             
             (* reading a char i0 *)
             erewrite split_non_empty_list with (i := i0) (ls' :=
                                                          (sublist (j + 1) (Zlength ls) ls))
             (ofs := (Ptrofs.add str_ofs (Ptrofs.repr (j + 1)))).
             
             Intros.
             forward.
             forward_if (temp _t'2
                              (if Byte.signed i0 >=? 48
                               then (Val.of_bool (Byte.signed i0 <=? 57))
                               else  Vfalse)).
             forward.
             forward.
             entailer!.

             { destruct (Byte.signed i0 >=? 48) eqn : I48.
               destruct (Byte.signed i0 <=? 57) eqn : I57.
               destruct (negb (Int.lt (Int.repr 57)
                                      (Int.repr (Byte.signed i0)))) eqn : LT.
               reflexivity.
               unfold Int.lt in *.
               destruct zlt.
               eapply Zle_bool_imp_le in I57.
               autorewrite with norm in *.
               nia.
               easy.
               destruct (negb (Int.lt (Int.repr 57) 
                                      (Int.repr (Byte.signed i0)))) eqn : LT.
               unfold Int.lt in *.
               destruct zlt.
               easy.
               eapply Z.leb_gt in I57.
               autorewrite with norm in *.
               nia.
               reflexivity.
               eapply Z.ge_le in H7.
               rewrite Z.geb_leb in *.
               eapply Zle_imp_le_bool in H7.
               rewrite H7 in I48. 
               easy.
             }
             forward.
             entailer!.
             { break_if.
               rewrite Z.geb_leb in *.
               try rewrite <- Zle_is_le_bool in *.
               nia.
               reflexivity. }
             forward_if.
             forward.
             forward.
             forward_if.
            (* Case:  vl < ub *)
           { forward.
             entailer!.
             (* use lemma  lt_ub_bounded *)
             {
               all: unfold typed_true, strict_bool_val in H7.
               break_if; simpl in H7;[|discriminate].
               unfold Val.of_bool in H7.
               destruct (Byte.signed i0 <=? 57) eqn:I057; simpl in H7; [|discriminate].
               unfold value_until, Z_of_string.
               destruct (sublist 0 j ls) eqn:SB.
               cbn.
               replace (Int64.signed (Int64.repr 0)) with 0 by reflexivity.
               rewrite Z.geb_le, Z.leb_le in *.
               lia.
               admit.
             }
             forward.
             
             (* show that loop invariant holds after the loop *)
             Exists (j + 1) (value_until (j + 1) ls).
             entailer!.
             repeat split; try nia.
             (* true *)
             (* follows from H5 *)
             admit.
             (* true, since j + 1 <= Zlength ls and H1 *)
             admit.
             (* true, use next_value lemma *)
             admit.
             (*true *)
             admit. }

             forward_if.
           (* vl == ub *)
           { forward_if.
             (* d <= last_digit_max *)
             { forward_if 
                 (PROP ( )
     LOCAL (
       temp _value (Vlong (Int64.repr (- (value_until j ls) * 10 - (Byte.signed i0 - 48))));
       temp _sign (Vint (Int.repr 1));

       temp _d (Vint (Int.sub (Int.repr (Byte.signed i0)) (Int.repr 48)));
       temp _t'6 (Vbyte i0);
       temp _t'2 (if Byte.signed i0 >=? 48 
                  then Val.of_bool (Byte.signed i0 <=? 57) 
                  else Vfalse);
       temp _t'7 (Vbyte i0); temp _t'9 (Vptr end'_b end'_ofs); 
       temp _end (Vptr end_b end_ofs);
       temp _intp (Vptr intp_b intp_ofs);
       temp _str (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr (j + 1))));
       
       temp _upper_boundary (Vlong upper_boundary);
       temp _last_digit_max (Vlong (Int64.add last_digit_max Int64.one)))
     SEP (
       valid_pointer (Vptr end'_b str_ofs);
       valid_pointer (Vptr end'_b end'_ofs);
       data_at sh_str tschar (Vbyte i) (Vptr end'_b str_ofs);
       data_at sh_str (tarray tschar j) (map Vbyte (sublist 1 (j + 1) ls')) (Vptr end'_b str_ofs');
       data_at sh_str tschar (Vbyte i0) (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr (j + 1))));
       data_at sh_str (tarray tschar (Zlength (sublist (j + 1) (Zlength ls) ls))) 
               (map Vbyte (sublist (j + 1) (Zlength ls) ls))
               (Vptr end'_b (Ptrofs.add (Ptrofs.add str_ofs (Ptrofs.repr (j + 1))) Ptrofs.one));
       data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs);
       data_at sh_intp tlong v (Vptr intp_b intp_ofs))).
             
               (* 0 < s *)
              easy. 
               (* s = -1 *)
             forward.
             forward.
             entailer!.
             (* typecheck error: DEBUG THIS *)
             admit.
             entailer!.
             admit.
             (* true, data_at_succ_sublist lemma *)
          
             
             repeat forward.
             forward_if.
             (* compare pointers *)
             {  autorewrite with sublist.
               replace (Zlength (sublist (j + 1) (Zlength ls) ls)) with (Zlength ls - j - 1).
               
               unfold test_order_ptrs; simpl.
               destruct peq; [simpl|contradiction].
               apply andp_right.
                destruct (Z_lt_le_dec (j + 1) (Zlength ls)).
               * apply derives_trans with (Q := valid_pointer
                                                  (Vptr end'_b
                                                        (Ptrofs.add
                                                           (Ptrofs.add
                                                              str_ofs Ptrofs.one)
                                                           (Ptrofs.repr (j + 1))))).
                 entailer!.
                 replace (Ptrofs.add (Ptrofs.add str_ofs (Ptrofs.repr (j + 1))) Ptrofs.one)
                   with
                     (Ptrofs.add (Ptrofs.add str_ofs Ptrofs.one) (Ptrofs.repr (j + 1))).
                 entailer!.
                 rewrite Ptrofs.add_assoc.
                 rewrite Ptrofs.add_assoc.
                 f_equal.
                 rewrite Ptrofs.add_commut.
                 reflexivity.
                 replace (Ptrofs.add (Ptrofs.add str_ofs Ptrofs.one) (Ptrofs.repr (j + 1)))
                   with
                     (Ptrofs.add str_ofs (Ptrofs.repr (j + 1 + 1))).
                 apply valid_pointer_weak.
                 admit. (* maybe change back LI for str_ofs' + j *)
               * apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
                 entailer!.
                 replace end'_ofs with (Ptrofs.add str_ofs (Ptrofs.repr (j + 1 + 1))).
                 apply valid_pointer_weak.
                 { assert (j < Zlength ls) by admit. (* Clt lemma *)
                   autorewrite with sublist in LEN.
                   replace (Zlength ls) with (j + 1) in LEN by nia.
                   assert (Ptrofs.unsigned str_ofs + j + 1 + 1 = Ptrofs.unsigned end'_ofs)
                     by nia.
                   unfold Ptrofs.add.
                   replace end'_ofs with (Ptrofs.repr (Ptrofs.unsigned end'_ofs))
                     by auto with ints.
                   f_equal.
                   rewrite Ptrofs.unsigned_repr_eq.
                   rewrite Zmod_small.
                   nia.
                   assert (0 <= Ptrofs.unsigned str_ofs).
                   destruct str_ofs.
                   unfold Ptrofs.unsigned.
                   simpl.
                   all: try nia.
                   assert (Zlength ls = j + 1) by nia.
                   autorewrite with sublist in H1.
                   replace (Zlength ls) with (j + 1) in H1 by nia.
                   rep_omega_setup.
                   nia.
                 }
               * apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
                 entailer!.
                 apply valid_pointer_weak.
               * erewrite Zlength_sublist.
                 all: try nia.
                 assert (j < Zlength ls) by admit. (* Clt lemma *)
                 nia. }
             }
             admit.
             (* str + j + 1 < end *)
             admit. (* break list to read as before
                       + see VC for tactics *)

             (* BREAK: str + j + 1 >= end *)
             forward.
            
             (* post-if implies break condition *)
             { Exists j.
               replace (Ptrofs.unsigned str_ofs' + (j) >=? Zlength ls)
                       with false by admit. (* H5 *)
               replace (value (Z_of_string ls) <? ub) with false by admit.
               (* H9 and H10 *)
               entailer!.
               split.
               (* lemma *)
               admit. 
               (* since we are in the upper limit case *)
               admit.
               admit.
             }

             } (* end of vl = ub && d <= last_digit *)

             (* vl = ub && d > ld, out of range *)
             { 
             forward.
             forward.
             entailer!.
             (* from H9 and H10, lemma ub_last_digit_error_range *)
             admit.
             (* true : from H9 and H10,  ub_last_digit_error_range_index *)
             admit. }
             } (* end of case vl = ub && d > last_digit *)

             (* case vl > ub *) 
             {
             repeat forward.
             entailer!.
             (* true, from H8 and H9, ub_last_digit_error_range *)
             admit.
             (*  ub_last_digit_error_range_index *)
             admit. }

             (* i0 non-digit: extra data *)
           { repeat forward.
             entailer!.
             (* lemma value_always_bounded *)
             admit.
             entailer!.
             (* from H7 *)
             admit.
             (* true extra_data_index *)
             admit. }

             reflexivity.
             (* true, from Heqls'' and H! *)
             admit.
             (* true, from Heqls'' *)
             admit.
  
             (* BREAK : str + 1 + j >= end *)
             forward.
             
             (* post entails break : check TODO *)
             { Exists j.
               replace (Ptrofs.unsigned str_ofs' + j >=? Zlength ls)
                       with true by admit. (* H5 *)
               entailer!.
               split.
               repeat f_equal.
               unfold value_until.
               autorewrite with sublist.
               (* since str + 1 + j >= end, ls = sublist 0 j ls *)
              admit.
              admit.
              admit.
             }
           *** (* BREAK IMPLIES THE REST OF THE FUNCTION *)
             admit.
        ** admit.
        ** admit.
        * reflexivity.
        * eassumption.
  - (* str >= end *)
    all: try apply Z.ltb_ge in IFCON.
    forward_if.
    (* Valid pointer proof *)
    { unfold test_order_ptrs; simpl.
      destruct peq; [simpl|contradiction].
      apply andp_right.
      * apply derives_trans with (Q := valid_pointer (Vptr end'_b str_ofs)).
        entailer!.
        apply valid_pointer_weak.
      * apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
        entailer!.
        apply valid_pointer_weak. }

    + (* str >= end, return INVAL *)
      forward.
      try apply Z.ltb_ge in IFCON.
      autorewrite with sublist in *|-.
      try apply Z.ltb_ge in IFCON.
      assert ((Ptrofs.unsigned end'_ofs - Ptrofs.unsigned str_ofs) <= 0)
             by nia.
      assert (Zlength ls = 0) as L by admit.
      subst.
      pose proof Zlength_nil_inv ls L as NIL.
      rewrite NIL; simpl; entailer!.
    +  (* end' <= str = true || str < end' = true (from forward_if) *)
      try apply Z.ltb_lt in IFCON.
      rewrite EQB in H; apply typed_false_ptr_ge in H.
      rewrite Z.gtb_lt in H. lia.
Admitted.
