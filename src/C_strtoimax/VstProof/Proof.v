Require Import Core.Tactics Core.PtrLemmas.
Require Import StructTact.StructTactics Psatz.
Require Import SepLemmas.
Require Import VstSpec AbstractSpec AbstractSpecLemmas.
Require Import VST.floyd.proofauto Psatz.
Require Import Clight.INTEGER.
Arguments valid_pointer p : simpl never.

Ltac test_order_ptrs_tac p1 p2 :=
          unfold test_order_ptrs; simpl;
          destruct peq; [simpl|contradiction];
          apply andp_right;
          [try (apply derives_trans with (Q := valid_pointer p1);
          entailer!;
          apply valid_pointer_weak) | try (
          apply derives_trans with (Q := valid_pointer p2);
          entailer!;
          apply valid_pointer_weak)]. 

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
     test_order_ptrs_tac (Vptr end'_b str_ofs) (Vptr end'_b end'_ofs).
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
      autorewrite with sublist in LEN.
      assert (Zlength ls = (Ptrofs.unsigned end'_ofs - 
                                 Ptrofs.unsigned str_ofs) - 1) as LS_len by nia.
      Intros.
      repeat forward.
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
           remember (Int64.unsigned upper_boundary) as ub.
           remember (i :: ls) as ls'.
           forward_loop (
               EX j : Z, EX vl : Z, 
                 let i' := Ptrofs.add str_ofs (Ptrofs.repr (j + 1)) in
                 PROP(0 <= j <= Zlength ls;
                      Ptrofs.unsigned str_ofs + j + 1 < Ptrofs.modulus;
                      forall i : Z, 0 <= i < j -> is_digit (Znth i ls) = true;
                        bounded (value_until j ls) = true)
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
               
           break: ( EX j : Z,
                   PROP(0 <= j <= Zlength ls;
                       forall i, 0 <= i < Zlength ls -> 
                            is_digit (Znth i ls) = true;
                        bounded (value (Z_of_string_loop ls 0 1)) = true)
                   LOCAL(
                     temp _value 
                          (Vlong (Int64.repr 
                                    (if Ptrofs.unsigned str_ofs + j + 1 >=? 
                                        Ptrofs.unsigned end'_ofs  
                                    then value (Z_of_string_loop ls 0 1)
                                    else -1 * (value (Z_of_string_loop ls 0 1)))));
                      temp _sign 
                          (Vint (Int.repr 
                                    (if Ptrofs.unsigned str_ofs + j + 1 >=? 
                                        Ptrofs.unsigned end'_ofs
                                    then -1
                                    else 1)));

                   temp _end (Vptr end_b end_ofs); 
                   temp _intp (Vptr intp_b intp_ofs);
                   temp _str (Vptr end'_b 
                              (Ptrofs.add str_ofs 
                                          (Ptrofs.repr (Zlength ls + 1)))))

                   SEP(
                     
                    valid_pointer (Vptr end'_b end'_ofs);
                    valid_pointer (Vptr end'_b str_ofs);
                    data_at sh_str (tarray tschar (Zlength ls + 1)) 
                            (map Vbyte (i::ls)) (Vptr end'_b str_ofs); 
                    data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs) 
                            (Vptr end_b end_ofs);
                    data_at sh_intp (tlong) v (Vptr intp_b intp_ofs))).
           (* BREAK IMPLIES THE REST OF THE FUNCTION *)
           3: 
             { Intro j.
               forward.
               forward.
               entailer!.
               unfold bounded in *.
               rewrite andb_true_iff in *.
               repeat rewrite Z.leb_le in *.
               break_if.
               1-2: repeat rewrite Int64.signed_repr;
               repeat rewrite Int.signed_repr;
               rep_omega_setup;
               assert (0 <= value (Z_of_string_loop ls 0 1)) by 
               (eapply loop_non_neg; nia);
               try nia;
               try rep_omega.
               forward.
               assert (res (Z_of_string (i :: ls)) = OK) as OK.
               { erewrite app_char_to_OK_loop. 
                 reflexivity.
                 nia.
                 unfold is_sign, minus_char.
                 bool_rewrite.
                 intuition.               
                 eapply bounded_to_OK_loop; try (nia || eassumption). }
                assert (index (Z_of_string (i :: ls)) = Zlength (i::ls))
                 as I.
               eapply OK_index.
               eassumption.
               assert (((-1) * value (Z_of_string_loop ls 0 1))%Z = 
                       (value (Z_of_string (i :: ls)))) as V.
               { simpl.
                 unfold is_sign, minus_char.
                 bool_rewrite.
                 break_match.
                 autorewrite with sublist in *.
                 nia.
                 replace (Byte.signed i =? plus_char) 
                         with false.
                 reflexivity.
                 symmetry.
                 Zbool_to_Prop.
                 rewrite Z.eqb_eq in *.
                 unfold plus_char.
                 nia.
               }
                 erewrite OK, I, V.  
                 all: 
               break_if; entailer;
                    try erewrite V;
                   autorewrite with sublist; entailer!. }
           ***
             Exists 0 0.
             entailer!.
             { intros. nia.
                }
             autorewrite with sublist.
             erewrite data_at_zero_array_eq.
             entailer!.
             all: try (erewrite sublist_1_cons || autorewrite with sublist);
               autorewrite with sublist; (reflexivity || auto with zarith || auto).
           ***
             assert (is_sign i = true) as SGN by admit.
             assert (Byte.signed i =? minus_char = true) as MCH by admit.
             assert (Byte.signed i =? plus_char = false) as PCH by admit.
             Intros j vl.
             assert (0 <= value_until j ls) as NN by (eapply loop_non_neg; nia).
             forward.
             forward_if.
           3:
             { (* BREAK: str + j + 1 >= end *)
             forward.
             rewrite_comparison.
             replace (Ptrofs.unsigned (Ptrofs.add str_ofs (Ptrofs.repr (j + 1))))
                     with (Ptrofs.unsigned str_ofs + j + 1) in *
               by (autorewrite with norm;
                   ptrofs_compute_add_mul;
                   rep_omega_setup;
                   nia).
             (* post-if implies break condition *)
             { Exists j.
               replace (Ptrofs.unsigned str_ofs + j + 1 >=?
                                                        Ptrofs.unsigned end'_ofs)
                       with true.
               replace j with (Zlength ls) in * by nia.
               replace (Zlength ls + 1) with
                   (Zlength (i::ls)) by (autorewrite with sublist; nia).
               erewrite  split_data_at_sublist_tschar with 
                   (ls := i :: ls) (j := 1).
               autorewrite with sublist.
               replace (Z.succ (Zlength ls) - 1)
                           with (Zlength ls) by nia.     
               unfold value_until in *.
               autorewrite with  sublist in *.
               entailer!.
               erewrite data_at_zero_array_eq.
               entailer!.
               replace (sublist 1 (Z.succ (Zlength ls)) (i :: ls)) with
                   ls.
               erewrite data_at_singleton_array_eq.
               entailer!.
               auto.
               replace (Z.succ (Zlength ls) - 1)
                 with (Zlength ls) by nia.
               all: try (erewrite sublist_1_cons || autorewrite with sublist);
                 autorewrite with sublist; (reflexivity || auto with zarith || auto).
               symmetry.
               erewrite Z.geb_le.
               nia. }
             }
              (* pointer comparison *)
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
                 { autorewrite with sublist in LEN.
                   replace (Zlength ls) with j in LEN by nia.
                   assert (Ptrofs.unsigned str_ofs + 1 + j = Ptrofs.unsigned end'_ofs) by nia.
                   ptrofs_compute_add_mul.
                   replace end'_ofs with (Ptrofs.repr (Ptrofs.unsigned end'_ofs))
                     by auto with ints.
                   f_equal.
                   all: rep_omega_setup; try nia. }
               * apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
                 entailer!.
                 apply valid_pointer_weak.
             }
             (* str + j + 1 <  end *)
           { rewrite_comparison.
             replace (Ptrofs.unsigned (Ptrofs.add str_ofs (Ptrofs.repr (j + 1)))) 
                           with (Ptrofs.unsigned str_ofs + (j + 1)) in * by
                 (ptrofs_compute_add_mul;
                  rep_omega_setup;
                  nia).
             assert (j < Zlength ls) as jLS by nia.
             assert (0 < Zlength (sublist j (Zlength ls) ls)) by
                  (autorewrite with sublist; nia).
             (* reading a char i0 *)
             edestruct sublist_first with (j := j) (ls := ls) as [i0 Sub];
               try nia.
             econstructor.
             instantiate (1 := 0).
             cbv; easy.
              assert (Znth j ls = i0) as ZN.
             { replace (i0 :: sublist (j + 1) (Zlength ls) ls)
                       with (app [i0] (sublist (j + 1) (Zlength ls) ls))
                            in Sub.
               erewrite <- sublist_rejoin' 
                        with (mid := j + 1)
                             (mid' := j + 1) in Sub.
               eapply app_inv_tail in Sub.
               erewrite  sublist_len_1 in Sub.
               inversion Sub.
               all: auto.
               all: try nia. }                   
             assert (data_at sh_str (tarray tschar (Zlength ls - j))
                             (map Vbyte (sublist j (Zlength ls) ls))
                             (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr (j + 1)))) = 
                             data_at sh_str tschar (Vbyte i0)
                                     (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr (j + 1)))) *
                             data_at sh_str (tarray tschar
                                                    (Zlength (sublist (j + 1) (Zlength ls) ls)))
                                     (map Vbyte (sublist (j + 1) (Zlength ls) ls))
                                     (Vptr end'_b (Ptrofs.add (Ptrofs.add str_ofs
                                            (Ptrofs.repr (j + 1))) Ptrofs.one))) as DATA_AT1.
             { erewrite Sub.
               replace (Zlength ls - j) with
                   (Zlength ((i0::(sublist (j + 1) (Zlength ls) ls)))).               
            
               erewrite split_non_empty_list with 
                   (i := i0) 
                   (ls' := (sublist (j + 1) (Zlength ls) ls))
                   (ofs := (Ptrofs.add str_ofs (Ptrofs.repr (j + 1)))); 
                 try reflexivity.
               1-2: autorewrite with sublist;
                 ptrofs_compute_add_mul;
                 rep_omega_setup; try nia. }   
              assert (data_at sh_str (tarray tschar (Zlength ls)) (map Vbyte ls)
                             (Vptr end'_b (Ptrofs.add str_ofs Ptrofs.one)) =
                     data_at sh_str (tarray tschar j) (map Vbyte (sublist 0 j ls))
                             (Vptr end'_b (Ptrofs.add str_ofs Ptrofs.one)) *
                     data_at sh_str (tarray tschar (Zlength ls - j))
                             (map Vbyte (sublist j (Zlength ls) ls))
          (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr (j + 1))))) as DATA_AT2.
             { replace (Ptrofs.add str_ofs (Ptrofs.repr (j + 1))) with
                 (Ptrofs.add (Ptrofs.add str_ofs Ptrofs.one) (Ptrofs.repr j)).
               erewrite <- split_data_at_sublist_tschar; try
               reflexivity. 
               all: 
                ptrofs_compute_add_mul;
                replace (Ptrofs.unsigned Ptrofs.one)
                           with 1 by auto with ptrofs;
                rep_omega_setup; try (nia || f_equal); try nia. }

             assert (
               data_at sh_str (tarray tschar (Zlength ls)) (map Vbyte ls)
                             (Vptr end'_b (Ptrofs.add str_ofs Ptrofs.one)) =
               data_at sh_str (tarray tschar (j + 1)) (map Vbyte (sublist 0 (j + 1) ls))
                             (Vptr end'_b (Ptrofs.add str_ofs Ptrofs.one)) *
                     data_at sh_str (tarray tschar (Zlength ls - (j + 1)))
                             (map Vbyte (sublist (j + 1) (Zlength ls) ls))
                             (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr (j + 1 + 1)))))
             as DATA_AT3.
             { replace (Ptrofs.add str_ofs (Ptrofs.repr (j + 1 + 1))) 
                 with (Ptrofs.add (Ptrofs.add str_ofs Ptrofs.one) (Ptrofs.repr (j + 1))).
               erewrite <- split_data_at_sublist_tschar.
               reflexivity.
               all: 
                 ptrofs_compute_add_mul;
                 replace (Ptrofs.unsigned Ptrofs.one)
                   with 1 by auto with ptrofs;
                 rep_omega_setup; try (nia || f_equal); try nia. }
             erewrite DATA_AT1.
             Intros.
             forward.
             forward_if (temp _t'2
                              (if 48 <=? Byte.signed i0 
                               then (Val.of_bool (Byte.signed i0 <=? 57))
                               else  Vfalse)).
             forward.
             forward.
             entailer!.
             { erewrite Z.ge_le_iff in *.
               erewrite <- Z.leb_le in *.
               break_if.
               replace (negb (Int.lt (Int.repr 57) (Int.repr (Byte.signed (Znth j ls)))))
                 with (Byte.signed (Znth j ls) <=? 57).
               destruct (Byte.signed (Znth j ls) <=? 57); easy.
               eapply Zge_bool_Intge.
               easy. }
             forward.
             entailer!.
             { break_if.
               try rewrite <- Zle_is_le_bool in *.
               nia.
               reflexivity. }
             forward_if.
             eapply typed_true_to_digit in H9.
             forward.
             forward.
             forward_if.
            (* Case:  vl < ub *)
           { pose proof (bounded_bool_to_Prop _ H6).
             pose proof (is_digit_to_Z i0 H9).
              lt_ub_to_Z  H10; try nia.
             assert (0 <= value_until j ls < AbstractSpecLemmas.upper_boundary).
             unfold Z_of_char in *.
             nia.
             forward.
             entailer!.
             { repeat rewrite Int64.signed_repr.
                eapply lt_ub_to_next_bounded_Prop.
                 try eassumption; try nia.
                 all: try nia.
                  eapply lt_ub_to_next_bounded_Prop.
                 try eassumption; try nia.
                 all: try nia. }
             forward.
             (* show that loop invariant holds after normal  loop body execution *)
             Exists (j + 1) (value_until (j + 1) ls).
             entailer!.
             erewrite next_value_lt_ub with (i := Znth j ls).
             repeat split; try nia.
             Lemma app_is_digit : forall ls j,
                 0 <= j < Zlength ls ->
               (forall i : Z, 0 <= i < j -> is_digit (Znth i ls) = true) ->
                        is_digit (Znth j ls) = true ->
                        forall i0 : Z, 0 <= i0 < j + 1 -> is_digit (Znth i0 ls) = true.
             Proof.
               intros.
               destruct (zle j i0).
               - replace i0 with j by nia.
                 eassumption.
               - eapply H0. nia.
             Qed.
             eapply app_is_digit; try nia; try eassumption.
             apply lt_ub_to_next_bounded_bool.
             all: try eassumption; try nia; auto.
             entailer!.
             erewrite sepcon_assoc.
             erewrite <- DATA_AT1.
             rewrite <- DATA_AT2, <- DATA_AT3.
             entailer!.
           }
             forward_if.
           (* vl == ub *)
           { forward_if.
             (* d <= last_digit_max *)
             { forward_if 
                 (PROP ( )
     LOCAL (
       temp _value (Vlong (Int64.repr 
(- value (Z_of_string_loop (sublist 0 j ls) 0 1) * 10 - (Byte.signed i0 - 48))));
       temp _sign (Vint (Int.repr 1));

       temp _d (Vint (Int.sub (Int.repr (Byte.signed i0)) (Int.repr 48)));
       temp _t'6 (Vbyte i0);
       temp _t'2 (if 48 <=? Byte.signed i0 
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
       data_at sh_str (tarray tschar j) (map Vbyte (sublist 0 j ls)) (Vptr end'_b str_ofs');
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
             (*
               (Eunop Oneg (Etempvar _value tlong) tlong)
               going through typechecking functions I found where FF comes from:
               look at isUnOpResultType or just do Compute below to see it.
              *)
             Compute (isUnOpResultType Oneg (Etempvar _value tlong) tlong).
             (* typecheck error: DEBUG THIS *)
             admit.
             entailer.
             forward.
             forward.
             
             
             
             forward_if.
        
             3: { 

               (* BREAK: str + j + 1 + 1 >= end *)
             forward.
             rewrite_comparison.
             replace (Ptrofs.unsigned
          (Ptrofs.add (Ptrofs.add str_ofs (Ptrofs.repr (j + 1)))
             (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1)))))
                     with (Ptrofs.unsigned str_ofs + j + 1 + 1) in *
               by (autorewrite with norm;
                   ptrofs_compute_add_mul;
                   rep_omega_setup;
                   nia).
             (* post-if implies break condition *)
             { Exists j.
               lt_ub_to_Z H10.
               lt_ub_to_Z H11.
               lt_ub_to_Z H12.
               Locate  lt_inv.
               cleanup_repr H12.
               assert (Byte.signed i0 - 48 <= last_digit_max_minus)
                 by admit. clear H12.
               (* replace Int64 with Int and use vst tactic: *)                   
               replace (Ptrofs.unsigned str_ofs + j + 1 >=?
                                                        Ptrofs.unsigned end'_ofs)
                       with false.
                entailer!.
                 repeat split; try easy.
                 replace (Zlength ls) with (j + 1) by nia.
                eapply app_is_digit; try easy.
                replace ls with (sublist 0 (j + 1) ls).
                replace (value (Z_of_string_loop (sublist 0 (j + 1) ls) 0 1)) with
                    (value_until (j + 1) ls).
                erewrite  next_value_lt_ub.
                eapply eq_ub_bounded_minus;
                  try eassumption.
                eapply is_digit_to_Z in H9.
                                          
                  all: try nia; try
                eassumption; auto.
                replace (j + 1) with (Zlength ls) by nia.
                autorewrite with sublist; auto.

                f_equal.
                f_equal.

                  replace ls with (sublist 0 (j + 1) ls) at 1.
                replace (value (Z_of_string_loop (sublist 0 (j + 1) ls) 0 1)) with
                    (value_until (j + 1) ls).
                erewrite  next_value_lt_ub.
                unfold value_until.
                instantiate (1 := (Znth j ls)).
                unfold Z_of_char.
                nia.
                 all: try eassumption; try nia; auto.
                  replace (j + 1) with (Zlength ls) by nia.
                autorewrite with sublist; auto.
              
               replace (Zlength ls) with (j + 1) by nia; auto. 
               replace (sublist 1 (j + 1) (i :: ls)) with
                   (sublist 0 j ls).
               
               erewrite sepcon_assoc.
               replace (Zlength ls - (j + 1))
                 with (Zlength (sublist (j + 1) (Zlength ls) ls)).
               erewrite <- DATA_AT1.
                erewrite sepcon_assoc.
               erewrite <- DATA_AT2.

           assert (data_at sh_str tschar (Vbyte i) (Vptr end'_b str_ofs) *
                    data_at sh_str (tarray tschar (Zlength ls)) (map Vbyte ls)
                       (Vptr end'_b (Ptrofs.add str_ofs Ptrofs.one)) =
                       data_at sh_str (tarray tschar (Zlength ls + 1)) (Vbyte i :: map Vbyte ls)
                       (Vptr end'_b str_ofs)) as DATA_AT4.
           { erewrite <- split_non_empty_list with (ls := i::ls);
               autorewrite with sublist in H1;
               autorewrite with sublist;
               try reflexivity; try nia.
           }
               
           erewrite DATA_AT4.
           entailer!.
               all:  try eapply bounded_bool_to_Prop in H6; auto;
                 autorewrite with sublist; auto.
               replace (i :: ls) with (app [i] ls)
                 by reflexivity.
               erewrite sublist_app2.
               all: autorewrite with sublist; try nia; auto.
               symmetry.
               rewrite Z.geb_leb.
               rewrite Z.leb_gt.
               nia.
               admit.
             }
             } 
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
                 replace (Ptrofs.unsigned Ptrofs.one) with 1
                   by auto with ptrofs.
                 ptrofs_compute_add_mul;
                   rep_omega_setup; try nia;
                      replace (Ptrofs.unsigned Ptrofs.one) with 1
                   by auto with ptrofs.
                 f_equal.
                 all: nia.
               *  apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
                 entailer!.
                 replace end'_ofs with (Ptrofs.add str_ofs (Ptrofs.repr (j + 1 + 1))).
                 apply valid_pointer_weak.
                
                 autorewrite with sublist in LEN.
                 replace (Zlength ls) with (j + 1) in LEN by nia.
                 assert (Ptrofs.unsigned str_ofs + j + 1 + 1 = Ptrofs.unsigned end'_ofs)
                   by nia.
                 ptrofs_compute_add_mul.
                 replace end'_ofs with (Ptrofs.repr (Ptrofs.unsigned end'_ofs))
                   by auto with ints.
                 f_equal.
                 all: try (rep_omega_setup; nia).
               * apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
                 entailer!.
                 apply valid_pointer_weak.
               * erewrite Zlength_sublist.
                 all: try nia. }

             assert (data_at sh_str tschar (Vbyte i) (Vptr end'_b str_ofs) *
                          data_at sh_str (tarray tschar (Zlength ls)) (map Vbyte ls)
                                  (Vptr end'_b (Ptrofs.add str_ofs Ptrofs.one)) =
                          data_at sh_str (tarray tschar (Zlength ls + 1))
                                  (Vbyte i :: map Vbyte ls)
                                  (Vptr end'_b str_ofs)) as DATA_AT4.
                  { erewrite <- split_non_empty_list with (ls := i::ls);
                      subst; autorewrite with sublist in H1;
                      autorewrite with sublist;
                      try reflexivity; try nia. }

                  

              forward.
             rewrite_comparison.
             replace  (Ptrofs.unsigned
          (Ptrofs.add (Ptrofs.add str_ofs (Ptrofs.repr (j + 1)))
             (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1)))))
                                         with 
                                           (Ptrofs.unsigned str_ofs + j + 1 + 1) in *
               by (normalize;ptrofs_compute_add_mul;
                rep_omega_setup;
               nia).
             assert (0 < Zlength (sublist (j + 1) (Zlength ls) ls)).

             { subst.               
               destruct (Z_lt_le_dec (Ptrofs.unsigned str_ofs + j + 1 + 1) Ptrofs.modulus).                       *
               erewrite Zlength_sublist.
               all: try nia.
               *
                autorewrite with norm in H11.
                ptrofs_compute_add_mul.
                all: try (rep_omega_setup;
               nia).
               }
             edestruct sublist_first with (j := j + 1) (ls := ls) as [i1 Sub2];
               try nia.
             econstructor.
             instantiate (1 := 0); cbv; auto.

            assert (data_at sh_str (tarray tschar (Zlength ls - (j + 1)))
       (map Vbyte (sublist (j + 1) (Zlength ls) ls))
       (Vptr end'_b (Ptrofs.add (Ptrofs.add str_ofs (Ptrofs.repr (j + 1))) Ptrofs.one)) =
        data_at sh_str tschar (Vbyte i1)
       (Vptr end'_b (Ptrofs.add (Ptrofs.add str_ofs (Ptrofs.repr (j + 1))) Ptrofs.one)) *
     data_at sh_str (tarray tschar (Zlength (sublist (j + 1 + 1) (Zlength ls) ls)))
       (map Vbyte (sublist (j + 1 + 1) (Zlength ls) ls))
       (Vptr end'_b
          (Ptrofs.add (Ptrofs.add (Ptrofs.add str_ofs (Ptrofs.repr (j + 1))) Ptrofs.one)
             Ptrofs.one))) as DATA_AT5.
            {         
            erewrite Sub2.
             (* reading a char i1 *)
            replace (Zlength ls - (j + 1)) with 
                (Zlength (i1::(sublist (j + 1 + 1) (Zlength ls) ls))).
            erewrite split_non_empty_list with
                 (i := i1) (ls' := (sublist (j + 1 + 1) (Zlength ls) ls))
                 (ofs :=  (Ptrofs.add (Ptrofs.add str_ofs 
                                                  (Ptrofs.repr (j + 1))) Ptrofs.one));
             auto.
            all:      
              autorewrite with sublist;  
              ptrofs_compute_add_mul; 
              replace (Ptrofs.unsigned Ptrofs.one)  with 1 by normalize;
                try (rep_omega_setup;
               nia). }

            autorewrite with sublist.
            erewrite  DATA_AT5.
              (* str + j + 1 < end *)
             Intros.
             forward.
             forward_if  
               (temp _t'1 (if 48 <=? Byte.signed i1
                           then Val.of_bool (Byte.signed i1 <=?  57) 
                           else Vfalse)).
             forward.
             forward.
             entailer!.
             
             { erewrite Z.ge_le_iff in *.
               erewrite <- Z.leb_le in *.
               break_if.
               replace (negb (Int.lt (Int.repr 57) (Int.repr (Byte.signed i1))))
                 with (Byte.signed i1 <=? 57).
               destruct (Byte.signed i1 <=? 57); easy.
               eapply Zge_bool_Intge.
               easy. }
             forward.
             entailer!.
               { break_if.
               try rewrite <- Zle_is_le_bool in *.
               nia.
               reflexivity. }
               assert (Znth (j + 1) ls = i1) as ZN1.
               { replace (i1 :: sublist (j + 1 + 1) (Zlength ls) ls)
                   with (app [i1] (sublist (j + 1 + 1) (Zlength ls) ls))
                   in Sub2.
                 erewrite <- sublist_rejoin' 
                   with (mid := (j + 1) + 1)
                        (mid' := (j + 1) + 1)
                   in Sub2.
                 eapply app_inv_tail in Sub2.
                 erewrite  sublist_len_1 in Sub2.
                 inversion Sub2.
                 all: auto.
                 all: try nia.
               }

               assert ( 0 <= value_until (j + 1) ls) as NN1 by (eapply loop_non_neg; nia).
               forward_if.

                (* ERROR RANGE spec *)
               {rewrite <- ZN1 in *.
                rewrite <- ZN in *.
                 eapply typed_true_to_digit in H15.
                 lt_ub_to_Z H10.
                 lt_ub_to_Z H11.
                 lt_ub_to_Z H12.
                 assert ((Byte.signed (Znth j ls) - 48) <= last_digit_max_minus)
                     by admit. clear H12.
                 inversion H6.
                 eapply bounded_bool_to_Prop in H6.

                 assert (bounded (value_until (j + 1) ls) = true) as Bound.             
                  { erewrite next_value_lt_ub.
                    eapply eq_ub_bounded_minus with (d := Z_of_char (Znth j ls)); try nia.
                    eapply is_digit_to_Z; subst; eassumption.
                    all: unfold value_until, Z_of_char in *;
                      subst; try eassumption; try nia; auto. }

                  assert (bounded (value_until ((j + 1) + 1) ls) = false) as BoundF.
             
                  { 
                    erewrite next_value_lt_ub with (i := Znth (j + 1) ls).
                    eapply lt_ub_not_bounded.
                    eassumption.
                    eapply is_digit_to_Z;
                    eassumption.
                    erewrite next_value_lt_ub with (i := Znth j ls).
                    eapply eq_ub_next; try nia
                     eapply is_digit_to_Z.
                    all: try eassumption; try nia.
                    eapply is_digit_to_Z; eassumption; auto.
                    auto.
                    eapply app_is_digit; try eassumption; try nia;
                      auto.
                    auto. }

                  assert (j + 1 + 1 <= Zlength ls) as LS_len2 by nia.

                  assert (res (Z_of_string_loop ls 0 1) = ERROR_RANGE) as Result_loop.
                  { 
                    assert ((Zlength (sublist 0 (j + 1 + 1) ls))
                            =  (j + 1 + 1)) as SB
                          by  (erewrite Zlength_sublist;
                      subst;
                      try nia).
                    edestruct all_digits_OK_or_ERROR_RANGE_loop
                      with (ls := (sublist 0 (j + 1 + 1) ls)) (v:= 0) (i := 1); try rewrite SB.
                    eapply app_is_digit;  try rewrite SB;
                    try nia.
                    eapply app_is_digit;  try rewrite SB;
                      try nia.                  
                    intros.
                    erewrite Znth_sublist.
                    normalize.
                    all: try nia.
                    all: try erewrite Znth_sublist;
                    try nia; normalize; subst; try eassumption.
                    eapply OK_bounded_loop in H12.
                    congruence.
                    admit.
                    eapply sublist_ERROR_RANGE in H12;
                    subst; try (
                    eassumption || nia).
                  }

                  assert (res (Z_of_string (i :: ls)) = ERROR_RANGE) as Result.
                  {
                    simpl.
                    repeat bool_rewrite.
                    break_match. 
                    autorewrite with sublist in H2;
                      try nia.
                    eassumption.
                  }                 
                  assert (index (Z_of_string_loop ls 0 1) = j + 1 + 1) as Index_loop.
                  { eapply ERROR_RANGE_index; try eassumption;
                      try nia.
                    admit. (* fix index lemma *) 
                  }
                  assert (index (Z_of_string (i :: ls)) = j + 1 + 1) as Index.
                  {  simpl.
                    repeat bool_rewrite.
                    break_match. 
                    autorewrite with sublist in H2;
                      try nia.
                    eassumption. }                 
                  forward.
                  erewrite Result, Index.
                  entailer!.
                  autorewrite with sublist in DATA_AT1.
                  erewrite sepcon_assoc.
                  erewrite <- DATA_AT5.
                  erewrite sepcon_assoc.
                  erewrite <- DATA_AT1.
                  erewrite sepcon_assoc.
                  erewrite <- DATA_AT2.
                  erewrite DATA_AT4.
                  autorewrite with sublist.
                   entailer!.
                  admit.
                  admit.
                  }
               forward.
               forward.
               entailer!.
               (* Extra data case *)
               admit.
               admit. } 
             (* end of vl = ub && d <= last_digit *)

             (* vl > ub && d > ld, out of range *)
             { 

               lt_ub_to_Z H10.
               eapply lt_ub_to_Z3 in H11.
               lt_ub_to_Z H12.
               inversion H6.
               eapply bounded_bool_to_Prop in H6.
              assert (bounded (value_until (j + 1) ls) = false) as Bound.
               { erewrite next_value_lt_ub.
                 eapply  eq_ub_not_bounded_minus.
                 eapply loop_non_neg; nia.
                 eapply is_digit_to_Z; eassumption.
                 all: unfold value_until, Z_of_char in *;
                   try eassumption; try nia. } 

               assert (res (Z_of_string_loop ls 0 1) = ERROR_RANGE) as Result_loop.
               eapply  ub_last_digit_error_range;
                 try eassumption; try nia.

              assert (res (Z_of_string (i :: ls)) = ERROR_RANGE) as Result.
               {  simpl.
                    repeat bool_rewrite.
                    break_match. 
                    autorewrite with sublist in H2;
                      try nia.
                    eassumption. }  

                 assert (index (Z_of_string_loop ls 0 1) = j + 1 ) as Index_loop.
                  { eapply ERROR_RANGE_index; try eassumption;
                      try nia.
                    admit. (* fix index lemma *) 
                  }

               assert (index (Z_of_string (i :: ls)) = j + 1) as Index.
               {  simpl.
                    repeat bool_rewrite.
                    break_match. 
                    autorewrite with sublist in H2;
                      try nia.
                    eassumption.                  
               }                
               repeat forward.
               rewrite Result.
               entailer!.
               { rewrite Index.             
                 entailer!.
                 autorewrite with sublist in DATA_AT1.
                 erewrite sepcon_assoc.    
                 autorewrite with sublist.
                  (erewrite <- DATA_AT1). 
                   erewrite sepcon_assoc.    
                   erewrite <- DATA_AT2.
                  assert (data_at sh_str tschar (Vbyte i) (Vptr end'_b str_ofs) *
                          data_at sh_str (tarray tschar (Zlength ls)) (map Vbyte ls)
                                  (Vptr end'_b (Ptrofs.add str_ofs Ptrofs.one)) =
                          data_at sh_str (tarray tschar (Zlength ls + 1))
                                  (Vbyte i :: map Vbyte ls)
                                  (Vptr end'_b str_ofs)) as DATA_AT4.
                  { erewrite <- split_non_empty_list with (ls := i::ls);
                      autorewrite with sublist in H1;
                      autorewrite with sublist;
                      try reflexivity; try nia. }
                  erewrite DATA_AT4.
                 autorewrite with sublist.
                 entailer!. }
                all: try  eapply bounded_bool_to_Prop in H6; 
                 try nia; try eassumption.
                 admit. }
             } (* end of case vl = ub && d > last_digit *)
             (* case vl > ub *) 
             { 
              lt_ub_to_Z H10.
              eapply lt_ub_to_Z5 in H11.
              assert (value_until j ls > AbstractSpecLemmas.upper_boundary)
                     by nia.
              inversion H6.
              eapply bounded_bool_to_Prop in H6.

              assert (bounded (value_until (j + 1) ls) = false) as Bound.
                  { erewrite next_value_lt_ub.
                    eapply lt_ub_not_bounded.
                    eapply loop_non_neg; nia.
                    eapply is_digit_to_Z; eassumption.
                    all: unfold value_until, Z_of_char in *;
                      try eassumption; try nia. } 

               assert (res (Z_of_string_loop ls 0 1) = ERROR_RANGE) as Result_loop.
               eapply  ub_last_digit_error_range;
                 try eassumption; try nia.

              assert (res (Z_of_string (i :: ls)) = ERROR_RANGE) as Result.
               {  simpl.
                    repeat bool_rewrite.
                    break_match. 
                    autorewrite with sublist in H2;
                      try nia.
                    eassumption.  }  

                 assert (index (Z_of_string_loop ls 0 1) = j + 1 ) as Index_loop.
                  { eapply ERROR_RANGE_index; try eassumption;
                      try nia.
                    admit. (* fix index lemma *) 
                  }

               assert (index (Z_of_string (i :: ls)) = j + 1) as Index.
               { simpl.
                    repeat bool_rewrite.
                    break_match. 
                    autorewrite with sublist in H2;
                      try nia.
                    eassumption.                  
               }                
               repeat forward.
               rewrite Result.
               entailer!.
               { rewrite Index.                
                 entailer!.
                 erewrite sepcon_assoc.      
                 erewrite <- DATA_AT1.
                 erewrite sepcon_assoc.    
                 erewrite <- DATA_AT2. 
                  assert (data_at sh_str tschar (Vbyte i) (Vptr end'_b str_ofs) *
                          data_at sh_str (tarray tschar (Zlength ls)) (map Vbyte ls)
                                  (Vptr end'_b (Ptrofs.add str_ofs Ptrofs.one)) =
                          data_at sh_str (tarray tschar (Zlength ls + 1))
                                  (Vbyte i :: map Vbyte ls)
                                  (Vptr end'_b str_ofs)) as DATA_AT4.
                  { erewrite <- split_non_empty_list with (ls := i::ls);
                      autorewrite with sublist in H1;
                      autorewrite with sublist;
                      try reflexivity; try nia. }
                  erewrite DATA_AT4.
                 autorewrite with sublist.
                 entailer!. }
               all: try  eapply bounded_bool_to_Prop in H6; nia.
             }
             (* i0 non-digit: extra data *)
           { eapply typed_false_to_digit in H9.
             forward.
             forward.
             entailer!.
             rewrite Int64.signed_repr.
             eapply bounded_bool_to_Prop.
             eapply neg_bounded.
             eassumption.
             eassumption.
             eapply bounded_bool_to_Prop;
             eassumption.

             assert (res (Z_of_string_loop ls 0 1) = EXTRA_DATA) as Result_loop
                 by admit.  
            
             assert (res (Z_of_string (i :: ls)) = EXTRA_DATA) as Result.           
             { simpl.
               repeat bool_rewrite.
               break_match. 
               autorewrite with sublist in H2;
                 try nia.
               eassumption.  }
             
             assert (index (Z_of_string_loop ls 0 1) = j + 1) as Index_loop
                 by admit.  

              assert (index (Z_of_string (i :: ls)) = j + 1) as Index.  
             { simpl.
               repeat bool_rewrite.
               break_match. 
               autorewrite with sublist in H2;
                 try nia.
               eassumption. }
             assert ((value (Z_of_string (i :: ls)) =
               (-1 * value_until j ls)%Z)) as Value.
             { admit. }
             (* see above *)
             forward.
             rewrite Result, Index, Value.
             entailer!.
             { erewrite sepcon_assoc.      
               erewrite <- DATA_AT1.
               erewrite sepcon_assoc.    
               erewrite <- DATA_AT2.
               assert (data_at sh_str tschar (Vbyte i) (Vptr end'_b str_ofs) *
                       data_at sh_str (tarray tschar (Zlength ls)) (map Vbyte ls)
                               (Vptr end'_b (Ptrofs.add str_ofs Ptrofs.one)) =
                       data_at sh_str (tarray tschar (Zlength ls + 1))
                               (Vbyte i :: map Vbyte ls)
                               (Vptr end'_b str_ofs)) as DATA_AT4.
               { erewrite <- split_non_empty_list with (ls := i::ls);
                   autorewrite with sublist in H1;
                   autorewrite with sublist;
                   try reflexivity; try nia. }
               erewrite DATA_AT4.
                 autorewrite with sublist.
                 entailer!. }
               all: try  eapply bounded_bool_to_Prop in H6; nia.
             }
  }   
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