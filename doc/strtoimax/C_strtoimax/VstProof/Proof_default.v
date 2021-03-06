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
                   valid_pointer (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr (Zlength (i :: ls))))); 
                   data_at sh_str tschar (Vbyte i) (Vptr str_b str_ofs);
                   data_at sh_str (tarray tschar (Zlength ls)) (map Vbyte ls)
                           (Vptr str_b (Ptrofs.add str_ofs Ptrofs.one));
                   data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs)
                           (Vptr end_b end_ofs);
                   data_at sh_intp tlong v (Vptr intp_b intp_ofs))).
      forward_if (
          if Byte.signed i =? 45
          then PROP( 0 < Zlength ls )
               LOCAL(temp _sign (Vint (Int.repr (-1)));
                     temp _str (Vptr end'_b
                                     (Ptrofs.add str_ofs (Ptrofs.repr 1)));
                     temp _end (Vptr end_b end_ofs); 
                     temp _intp (Vptr intp_b intp_ofs);
                     temp _last_digit_max
                          (Vlong (Int64.add last_digit_max_int Int64.one));
                     temp _upper_boundary (Vlong upper_boundary_int))
               sep_precondition
          else if Byte.signed i =? 43
               then PROP( 0 < Zlength ls )
                    LOCAL(temp _str (Vptr end'_b 
                                          (Ptrofs.add str_ofs (Ptrofs.repr 1)));
                         temp _end (Vptr end_b end_ofs); 
                     temp _intp (Vptr intp_b intp_ofs))
                    sep_precondition
               else PROP( )
                    LOCAL(temp _str (Vptr end'_b str_ofs);
                         temp _end (Vptr end_b end_ofs); 
                     temp _intp (Vptr intp_b intp_ofs);
                         temp _sign (Vint (Int.repr 1));
                         temp _upper_boundary (Vlong upper_boundary_int);
                         temp _last_digit_max (Vlong last_digit_max_int))
                    SEP  (
                   valid_pointer (Vptr end'_b end'_ofs);
                   valid_pointer (Vptr str_b str_ofs);
                   valid_pointer (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr (Zlength (i::ls))))); 
                   data_at sh_str tschar (Vbyte i) (Vptr str_b str_ofs);
                   data_at sh_str (tarray tschar (Zlength ls)) (map Vbyte ls)
                           (Vptr str_b (Ptrofs.add str_ofs Ptrofs.one));
                   data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs)
                           (Vptr end_b end_ofs);
                   data_at sh_intp tlong v (Vptr intp_b intp_ofs))).
      admit.
      admit.
      admit.     
      * (* Loop *)
        repeat break_if;
          unfold sep_precondition.
        ** admit. (* minus *)
        ** admit.
        ** (* default case *)
          assert (is_sign i = false) as SGN 
              by (unfold is_sign, minus_char; bool_rewrite; intuition).
          assert (Byte.signed i =? minus_char = false) as MCH 
              by (unfold is_sign, minus_char; bool_rewrite; intuition).
          assert (Byte.signed i =? plus_char = false) as PCH by intuition.
          autorewrite with norm.
          forward.     
    
          Notation value_until_d j ls := 
            (value (Z_of_string_loop (sublist 0 j ls) 0 0 true)).
           remember (Int64.unsigned upper_boundary_int) as ub.

          remember (i :: ls) as ls'.
           forward_loop (
               EX j : Z, EX vl : Z,
                 PROP(0 <= j <= Zlength ls';
                      Ptrofs.unsigned str_ofs + j < Ptrofs.modulus;
                      forall i, 0 <= i < j -> is_digit (Znth i ls') = true;
                        bounded (value_until_d j ls') = true)
                 LOCAL(temp _end (Vptr end_b end_ofs); 
                       temp _intp (Vptr intp_b intp_ofs);
                       temp _str (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr j)));
                       temp _value (Vlong (Int64.repr (value_until_d j ls')));
                       temp _sign (Vint (Int.repr 1));
                       temp _upper_boundary (Vlong upper_boundary_int);
                       temp _last_digit_max
                            (Vlong last_digit_max_int))
                 SEP(
                    valid_pointer (Vptr end'_b (Ptrofs.add str_ofs 
                                         (Ptrofs.repr (Zlength ls'))));
                   valid_pointer (Vptr end'_b str_ofs) ;
                   valid_pointer (Vptr end'_b end'_ofs) ;

                   data_at sh_str (tarray tschar j)
                           (map Vbyte (sublist 0 j ls'))
                            (Vptr end'_b str_ofs);                   
                   (* str + j + 1 |-> sublist (j + 1) |ls'| ls'  *)
                   data_at sh_str (tarray tschar (Zlength ls' - j))
                           (map Vbyte (sublist j (Zlength ls') ls'))
                           (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr j))) ; 
                   data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs)
                           (Vptr end_b end_ofs) ;
                   data_at sh_intp tlong v (Vptr intp_b intp_ofs)))
               
           break: (PROP(forall i, 0 <= i < Zlength ls' -> 
                             is_digit (Znth i ls') = true;
                         bounded (value (Z_of_string_loop ls' 0 0 true)) = true)
                    LOCAL(
                      temp _value (Vlong (Int64.repr (value (Z_of_string_loop ls' 0 0 true))));
                      temp _sign (Vint (Int.repr 1));

                      temp _end (Vptr end_b end_ofs); 
                      temp _intp (Vptr intp_b intp_ofs);
                      temp _str (Vptr end'_b 
                                 (Ptrofs.add str_ofs 
                                             (Ptrofs.repr (Zlength ls')))))

                    SEP(
                       valid_pointer (Vptr end'_b (Ptrofs.add str_ofs 
                                                              (Ptrofs.repr (Zlength ls'))));
                      valid_pointer (Vptr end'_b end'_ofs);
                      valid_pointer (Vptr end'_b str_ofs);
                      data_at sh_str (tarray tschar (Zlength ls')) 
                              (map Vbyte ls') (Vptr end'_b str_ofs); 
                      data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs) 
                              (Vptr end_b end_ofs);
                      data_at sh_intp (tlong) v (Vptr intp_b intp_ofs))).
           (* BREAK IMPLIES THE REST OF THE FUNCTION *)
           3: 
             { Intros.
               forward.
               forward.
               forward.
               entailer!.
               all: erewrite OK_res.
               all: try bool_rewrite.
               auto.
               all: try (eassumption || nia || auto).
               pose (nil_cons).
               intuition.
               congruence.
               simpl.
               autorewrite with sublist; entailer!.
               pose (nil_cons).
               intuition.
               congruence.
           }
           ***
             Exists 0 0.
             entailer!.
             { intros. nia. }
             autorewrite with sublist.
             erewrite data_at_zero_array_eq.
             entailer!.
             all: try (erewrite sublist_1_cons || autorewrite with sublist);
               autorewrite with sublist; (reflexivity || auto with zarith || auto).
             erewrite <- split_non_empty_list with (ls := i::ls).             
             autorewrite with sublist.
             entailer!.
             auto.
             nia.
           ***
             Intros j vl.
             assert (0 <= value_until_d j ls') as NN 
                 by (eapply loop_non_neg; nia).
               assert (Int64.min_signed <= value_until_d j ls' <= Int64.max_signed)
                 as BP by
               (erewrite bounded_bool_to_Prop in H5; eassumption).
               pose proof bounded0 as B0.
             forward.
             forward_if.
           3:
             { (* BREAK: str + j + 1 >= end *)
             forward.
             rewrite_comparison.
             replace (Ptrofs.unsigned (Ptrofs.add str_ofs (Ptrofs.repr (j))))
                     with (Ptrofs.unsigned str_ofs + j ) in *
               by (autorewrite with norm;
                   ptrofs_compute_add_mul;
                   rep_omega_setup;
                   nia).
             (* post-if implies break condition *)
             { 
               replace j with (Zlength (i::ls)) in *.
               
               entailer!.
               autorewrite with sublist in *.
               intuition.
               autorewrite with sublist.
                erewrite data_at_zero_array_eq.
                entailer!.
               all: try (erewrite sublist_1_cons || autorewrite with sublist);
                 autorewrite with sublist; 
                 (reflexivity || auto with zarith || auto). 
               autorewrite with sublist in *.
                assert (0 <= Zlength ls) by (eapply Zlength_nonneg). 
                assert (Z.succ (Zlength ls) = Ptrofs.unsigned end'_ofs - Ptrofs.unsigned str_ofs)
                       by nia.
                subst.
                autorewrite with sublist in *.
                nia.
           }} 
           
            (* normal: str + j + 1 <  end *)
           (* pointer comparison *)
             { unfold test_order_ptrs; simpl.
               destruct peq; [simpl|contradiction].
               apply andp_right.
               destruct (Z_lt_le_dec j (Zlength (i::ls))).
               * apply derives_trans with (Q := valid_pointer
                                        (Vptr end'_b (Ptrofs.add str_ofs 
                                                        (Ptrofs.repr (j))))).
                 entailer!.
                 apply valid_pointer_weak.
               * apply derives_trans with 
                     (Q := valid_pointer (Vptr end'_b end'_ofs)).
                 entailer!.
                 replace end'_ofs with (Ptrofs.add str_ofs (Ptrofs.repr (j))).
                 apply valid_pointer_weak.
                 { autorewrite with sublist in LEN.
                   replace (Zlength (i::ls)) with j in LEN by nia.
                   autorewrite with sublist in *.
                   assert (Ptrofs.unsigned str_ofs + j = 
                           Ptrofs.unsigned end'_ofs) by nia.
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
             assert (Ptrofs.unsigned (Ptrofs.add str_ofs (Ptrofs.repr (j)))
                     <? Ptrofs.unsigned end'_ofs = true) as P.
             erewrite Z.ltb_lt.
             eassumption.            
             replace (Ptrofs.unsigned (Ptrofs.add str_ofs (Ptrofs.repr (j)))) 
                           with (Ptrofs.unsigned str_ofs + (j)) in * by
                 (ptrofs_compute_add_mul;
                  rep_omega_setup;
                  nia).
             assert (j < Zlength (i::ls)) as jLS by (autorewrite with sublist; nia).
             assert (0 < Zlength (sublist j (Zlength (i :: ls)) (i :: ls))) by
                  (autorewrite with sublist in *; nia).
             (* reading a char i0 *)
             edestruct sublist_first with (j := j) (ls := (i :: ls)) as [i0 Sub];
               try nia.
             econstructor.
             instantiate (1 := 0).
             cbv; easy.
              assert (Znth j (i :: ls) = i0) as ZN.
             { replace (i0 :: sublist (j + 1) (Zlength (i :: ls)) (i :: ls))
                       with (app [i0] (sublist (j + 1) (Zlength (i :: ls)) (i :: ls)))
                            in Sub.
               erewrite <- sublist_rejoin' 
                        with (mid := j + 1)
                             (mid' := j + 1) in Sub.
               eapply app_inv_tail in Sub.
               erewrite  sublist_len_1 in Sub.
               inversion Sub.
               all: auto.
               all: try nia. }    
               
             assert (data_at sh_str (tarray tschar (Zlength (i :: ls) - j))
                             (map Vbyte (sublist j (Zlength (i :: ls)) (i :: ls)))
                             (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr (j)))) = 
                             data_at sh_str tschar (Vbyte i0)
                                     (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr (j)))) *
                             data_at sh_str (tarray tschar
                                                    (Zlength (sublist (j + 1) (Zlength (i :: ls)) (i :: ls))))
                                     (map Vbyte (sublist (j + 1 ) (Zlength (i :: ls)) (i :: ls)))
                                     (Vptr end'_b (Ptrofs.add (Ptrofs.add str_ofs (Ptrofs.repr (j))) Ptrofs.one))) as DATA_AT1.
             { erewrite Sub.
               replace (Zlength (i :: ls) - j) with
                   (Zlength ((i0::(sublist (j + 1) (Zlength (i :: ls)) (i :: ls))))).
               erewrite split_non_empty_list with 
                   (i := i0) 
                   (ls' := (sublist (j + 1) (Zlength (i :: ls)) (i :: ls)))
                   (ofs := (Ptrofs.add str_ofs (Ptrofs.repr (j)))); 
                 try reflexivity.
               1-2: autorewrite with sublist;
                 ptrofs_compute_add_mul;
                 rep_omega_setup; try nia.

             }   
              assert (data_at sh_str (tarray tschar (Zlength (i :: ls))) 
                              (map Vbyte (i :: ls))
                             (Vptr end'_b str_ofs) =
                     data_at sh_str (tarray tschar j) (map Vbyte (sublist 0 j (i :: ls)))
                             (Vptr end'_b str_ofs) *
                     data_at sh_str (tarray tschar (Zlength (i :: ls) - j))
                             (map Vbyte (sublist j (Zlength (i :: ls)) (i :: ls)))
          (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr (j))))) as DATA_AT2.
             {
               erewrite <- split_data_at_sublist_tschar; try
               reflexivity. 
               all: 
                ptrofs_compute_add_mul;
                replace (Ptrofs.unsigned Ptrofs.one)
                           with 1 by auto with ptrofs;
                autorewrite with sublist;
                rep_omega_setup; try (nia || f_equal); try nia. }

             assert (
               data_at sh_str (tarray tschar (Zlength (i :: ls))) (map Vbyte (i :: ls))
                             (Vptr end'_b str_ofs) =
               data_at sh_str (tarray tschar (j + 1)) (map Vbyte (sublist 0 (j + 1) (i :: ls)))
                             (Vptr end'_b str_ofs) *
                     data_at sh_str (tarray tschar (Zlength (i :: ls) - (j + 1)))
                             (map Vbyte (sublist (j + 1) (Zlength (i :: ls)) (i :: ls)))
                             (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr (j + 1)))))
             as DATA_AT3.
             {erewrite <- split_data_at_sublist_tschar.
              reflexivity.
               all: autorewrite with sublist;
                 ptrofs_compute_add_mul;
                 replace (Ptrofs.unsigned Ptrofs.one)
                   with 1 by auto with ptrofs;
                 rep_omega_setup; try (nia || f_equal); try nia. }
             subst.
             erewrite DATA_AT1.
             Intros.
             forward.
             forward_if (temp _t'2
                              (if 48 <=? Byte.signed (Znth j (i :: ls))
                               then (Val.of_bool (Byte.signed (Znth j (i :: ls)) <=? 57))
                               else  Vfalse)).
             forward.
             forward.
             entailer!.
             { erewrite Z.ge_le_iff in *.
               erewrite <- Z.leb_le in *.
               break_if.
               replace (negb (Int.lt (Int.repr 57) 
                                     (Int.repr (Byte.signed (Znth j (i :: ls))))))
                 with (Byte.signed (Znth j (i :: ls)) <=? 57).
               destruct (Byte.signed (Znth j (i :: ls)) <=? 57); easy.
               eapply Zge_bool_Intge.
               easy. }
             forward.
             entailer!.
             { break_if.
               try rewrite <- Zle_is_le_bool in *.
               nia.
               reflexivity. }
             
             forward_if.
             eapply typed_true_to_digit in H8.
             pose proof (is_digit_to_Z (Znth j (i :: ls)) H8).
             forward.
             forward.
             forward_if.
            (* Case:  vl < ub *)
           { int64_to_Z.
             try nia.
             forward.
             entailer!.
             { repeat rewrite Int64.signed_repr;
                 try eapply lt_ub_to_next_bounded_Prop;
                 try eassumption; try nia. }
             forward.
             (* show that loop invariant holds after normal  loop body execution *)
             Exists (j + 1) (value_until_d (j + 1) (i :: ls)).
             entailer!.
          

             erewrite next_value_lt_ub with (i := Znth j (i :: ls)).
             repeat split; try nia.
             eapply app_is_digit; try nia; try eassumption.
             apply lt_ub_to_next_bounded_bool.
             all: try eassumption; try nia; auto.
             entailer!.
             erewrite sepcon_assoc.
             erewrite <- DATA_AT1.
             rewrite <- DATA_AT2, <- DATA_AT3.
             entailer!.
           } 
           int64_to_Z.
             forward_if.
             int64_to_Z.

           (* vl == ub *)
           { forward_if.
              int64_to_Z.                         
             (* d <= last_digit_max *)
             {   

           forward_if    ( PROP ( )
  LOCAL (temp _value
           (Vlong
              (Int64.add
                 (Int64.mul (Int64.repr (value_until_d j (i :: ls)))
                    (Int64.repr (Int.signed (Int.repr 10))))
                 (Int64.repr
                    (Int.signed
                       (Int.sub (Int.repr (Byte.signed (Znth j (i :: ls)))) (Int.repr 48))))));
  temp _d (Vint (Int.sub (Int.repr (Byte.signed (Znth j (i :: ls)))) (Int.repr 48)));
  temp _t'6 (Vbyte (Znth j (i :: ls)));
  temp _t'2
    (if 48 <=? Byte.signed (Znth j (i :: ls))
     then Val.of_bool (Byte.signed (Znth j (i :: ls)) <=? 57)
     else Vfalse); temp _t'7 (Vbyte (Znth j (i :: ls))); temp _t'9 (Vptr end'_b end'_ofs);
  temp _end (Vptr end_b end_ofs); temp _intp (Vptr intp_b intp_ofs);
  temp _str (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr j))); temp _sign (Vint (Int.repr 1));
  temp _upper_boundary (Vlong upper_boundary_int);
  temp _last_digit_max (Vlong last_digit_max_int))
  SEP (valid_pointer (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr (Zlength (i :: ls)))));
  valid_pointer (Vptr end'_b str_ofs); valid_pointer (Vptr end'_b end'_ofs);
  data_at sh_str (tarray tschar j) (map Vbyte (sublist 0 j (i :: ls))) (Vptr end'_b str_ofs);
  data_at sh_str tschar (Vbyte (Znth j (i :: ls)))
    (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr j)));
  data_at sh_str (tarray tschar (Zlength (sublist (j + 1) (Zlength (i :: ls)) (i :: ls))))
    (map Vbyte (sublist (j + 1) (Zlength (i :: ls)) (i :: ls)))
    (Vptr end'_b (Ptrofs.add (Ptrofs.add str_ofs (Ptrofs.repr j)) Ptrofs.one));
  data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs);
  data_at sh_intp tlong v (Vptr intp_b intp_ofs))).
          
             forward.
             entailer!.
             {
               unfold bounded in *.
               rewrite andb_true_iff in *.
               repeat rewrite Z.leb_le in *.
               repeat rewrite Int64.signed_repr;
                 repeat rewrite Int.signed_repr;
                 rep_omega_setup;
                 assert (0 <= value (Z_of_string_loop (i :: ls) 0 0 true)) by 
                     (eapply loop_non_neg; nia);
                 try nia;
                 try rep_omega; 
                 cbn in H11;
                 cbn in H12;
                 cbn in H13;
                 try nia. 
               
             }
             entailer!.
             easy.
             forward.
             forward.
             forward_if.
             3: { 
             (* BREAK: str + j + 1 + 1 >= end *)
             forward.
             rewrite_comparison.
             replace (Ptrofs.unsigned
          (Ptrofs.add (Ptrofs.add str_ofs (Ptrofs.repr (j )))
             (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1)))))
                     with (Ptrofs.unsigned str_ofs + j  + 1) in *
               by (autorewrite with norm;
                   ptrofs_compute_add_mul;
                   rep_omega_setup;
                   nia).
             (* post-if implies break condition *)
             { Arguments Z_of_string_loop s : simpl never.
               Arguments Z_of_string s : simpl never.
               entailer!.
                repeat split; try easy.
                replace (Zlength (i :: ls)) with (j + 1)
                  by (autorewrite with sublist; nia).
               eapply app_is_digit; try easy.
               replace (i :: ls) with (sublist 0 (j + 1) (i :: ls)).
               {
               rewrite next_value_lt_ub with (i := Znth j (i :: ls)).
               eapply eq_ub_bounded_plus.
               all: try (nia || eassumption || auto). 
              }
               replace (j + 1) with (Zlength (i :: ls)) by  (autorewrite with sublist; nia).
               autorewrite with sublist; auto.
               do 2 f_equal.
               replace (i :: ls) with (sublist 0 (j + 1) (i :: ls)) at 1.
               rewrite  next_value_lt_ub with (i := Znth j (i :: ls)).
               reflexivity.
               all: try eassumption; try nia; auto.
               autorewrite with sublist; auto.
               replace (j + 1) with (Zlength (i :: ls)) by (autorewrite with sublist; nia).
               autorewrite with sublist; auto.
               erewrite sepcon_assoc.
               erewrite <- DATA_AT1.
               erewrite <- DATA_AT2.
               entailer!. } } 
             (* compare pointers *)
             { autorewrite with sublist.
               unfold test_order_ptrs; simpl.
               destruct peq; [simpl|contradiction].
               apply andp_right.
               destruct (Z_lt_le_dec (j + 1) (Zlength (i :: ls))).
               * apply derives_trans with (Q := valid_pointer
                                                  (Vptr end'_b
                                                        (Ptrofs.add
                                                          
                                                              str_ofs 
                                                           (Ptrofs.repr (j + 1))))).
                 entailer!.
                 replace (Ptrofs.add str_ofs (Ptrofs.repr (j + 1)))
                   with
                     (Ptrofs.add (Ptrofs.add str_ofs (Ptrofs.repr j)) Ptrofs.one).
                 autorewrite with sublist in *.
                 entailer!.
                 rewrite Ptrofs.add_assoc.
                 f_equal.
                 replace (Ptrofs.unsigned Ptrofs.one) with 1
                   by auto with ptrofs.
                 ptrofs_compute_add_mul;
                   rep_omega_setup; try nia;
                      replace (Ptrofs.unsigned Ptrofs.one) with 1
                   by auto with ptrofs.
                 f_equal.
                
                 
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
                 replace end'_ofs with (Ptrofs.add str_ofs (Ptrofs.repr (j + 1))).
                 apply valid_pointer_weak.
                
                 replace (Zlength (ls)) with j in *.
                 assert (Ptrofs.unsigned str_ofs + j + 1 = Ptrofs.unsigned end'_ofs)
                   by nia.
                 ptrofs_compute_add_mul.
                 replace end'_ofs with (Ptrofs.repr (Ptrofs.unsigned end'_ofs))
                   by auto with ints.
                 f_equal.
                 all: try (autorewrite with sublist in *; rep_omega_setup; nia).
               * apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
                 entailer!.
                 apply valid_pointer_weak.
               }

             forward.
             rewrite_comparison.
             replace  (Ptrofs.unsigned
                         (Ptrofs.add (Ptrofs.add str_ofs (Ptrofs.repr (j)))
                                     (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1)))))
               with 
                 (Ptrofs.unsigned str_ofs + j + 1) in *
               by (normalize;ptrofs_compute_add_mul;
                   rep_omega_setup;
                   nia).
             assert (0 < Zlength (sublist (j + 1) (Zlength (i :: ls)) (i :: ls))).

             { subst.               
               destruct (Z_lt_le_dec (Ptrofs.unsigned str_ofs + j + 1) Ptrofs.modulus).                           *
               erewrite Zlength_sublist.
               all: autorewrite with sublist; try nia.
               *
                ptrofs_compute_add_mul.
                all: try (rep_omega_setup;
               nia).
               }
             edestruct sublist_first with (j := j + 1) (ls := (i :: ls)) as [i1 Sub2];
               try nia.
             econstructor.
             instantiate (1 := 0); cbv; auto.
             autorewrite with sublist; try nia.

             assert (data_at sh_str (tarray tschar
                                            (Zlength (sublist (j + 1)
                                                              (Zlength (i :: ls)) (i :: ls))))
       (map Vbyte (sublist (j + 1) (Zlength (i :: ls)) (i :: ls)))
       (Vptr end'_b (Ptrofs.add (Ptrofs.add str_ofs (Ptrofs.repr j)) Ptrofs.one)) =
        data_at sh_str tschar (Vbyte i1)
       (Vptr end'_b (Ptrofs.add (Ptrofs.add str_ofs (Ptrofs.repr j)) Ptrofs.one)) *
     data_at sh_str (tarray tschar (Zlength (sublist (j + 1 + 1) (Zlength (i :: ls)) (i :: ls))))
       (map Vbyte (sublist (j + 1 + 1) (Zlength (i :: ls)) (i :: ls)))
       (Vptr end'_b
          (Ptrofs.add (Ptrofs.add (Ptrofs.add str_ofs (Ptrofs.repr (j))) Ptrofs.one)
             Ptrofs.one))) as DATA_AT5.
            {         
            erewrite Sub2.
             (* reading a char i1 *)
            erewrite split_non_empty_list with
                 (i := i1) (ls' := (sublist (j + 1 + 1) (Zlength (i :: ls)) (i :: ls)))
                 (ofs :=  (Ptrofs.add (Ptrofs.add str_ofs 
                                                  (Ptrofs.repr (j))) Ptrofs.one));
              auto.
            all:      
              autorewrite with sublist;  
              ptrofs_compute_add_mul; 
              replace (Ptrofs.unsigned Ptrofs.one)  with 1 by normalize;
                try (rep_omega_setup;
                     nia).
            }
            
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
              
               assert (Znth (j + 1) (i :: ls) = i1) as ZN1.
               { replace (i1 :: sublist (j + 1 + 1) (Zlength (i :: ls)) (i :: ls))
                   with (app [i1] (sublist (j + 1 + 1) (Zlength (i :: ls)) (i :: ls)))
                   in Sub2.
                 erewrite <- sublist_rejoin' 
                   with (mid := (j + 1) + 1)
                        (mid' := (j + 1) + 1)
                   in Sub2.
                 eapply app_inv_tail in Sub2.
                 erewrite  sublist_len_1 in Sub2.
                 inversion Sub2.
                 all: auto.
                 all:  autorewrite with sublist; try nia.
               }
               assert ( 0 <= value_until_d (j + 1) (i :: ls) ) as NN1
                   by (eapply loop_non_neg; nia).

               forward_if.

                (* ERROR RANGE spec *)
               { rewrite <- ZN1 in *.
                 eapply typed_true_to_digit in H15.
                 assert ( 0 <= Z_of_char (Znth (j + 1) (i :: ls)) <= 9) as Dg by
                 (eapply is_digit_to_Z in H15; nia).
                 assert (forall i0 : Z, 0 <= i0 < j + 1 -> is_digit (Znth i0 (i :: ls)) = true) as D.
                 eapply app_is_digit.
                  all: try nia;
                    try eassumption; auto.
                assert (bounded (value_until_d (j + 1) (i :: ls)) = true) 
                  as Boundf.
                {  rewrite next_value_lt_ub with (i := Znth j (i :: ls)).
                   eapply eq_ub_bounded_plus.
                   all: try nia; try assumption; auto. }
                
                assert (bounded (value_until_d ((j + 1) + 1) (i :: ls) ) = false) 
                  as BoundF.
                
                { erewrite next_value_lt_ub with 
                      (j := j + 1) (i := (Znth (j + 1) (i :: ls))).                  
                  apply lt_ub_not_bounded_plus.
                  nia.
                  rewrite next_value_lt_ub with (i := Znth j (i :: ls)).
                  eapply eq_ub_next_gt_ub_plus.
                  all: autorewrite with sublist; try nia;
                    try eassumption; auto. }
                assert (j + 1 + 1 <= Zlength (i :: ls)) as LS_len2
                    by (autorewrite with sublist; nia).                 
                  forward.
                  erewrite ERROR_RANGE_res.
                  simpl.
                  entailer!.
                  erewrite sepcon_assoc.
                  erewrite <- DATA_AT5.
                  erewrite sepcon_assoc.
                  erewrite <- DATA_AT1.
                  erewrite <- DATA_AT2.
                  entailer!.
                    all: 
                      try nia;
                      try eassumption; auto.
                    intros.
                    destruct (zeq i0 (j +1)).
                    subst. eassumption.
                    eapply D.
                    nia. }                               
               forward.
               forward.
               
               erewrite EXTRA_DATA_res with (j := j + 1).
               simpl.
               erewrite next_value_lt_ub with (i := (Znth j (i :: ls))).
               entailer!.
               erewrite sepcon_assoc.
               erewrite <- DATA_AT5.
               erewrite sepcon_assoc.
               erewrite <- DATA_AT1.
               erewrite <- DATA_AT2.

               entailer!.
                all: autorewrite with sublist; try (eassumption || nia || auto).
               eapply app_is_digit.
                all: try (eassumption || nia || auto).
                 {  rewrite next_value_lt_ub with (i := Znth j (i :: ls)).
                     eapply eq_ub_bounded_plus.
                     all: try nia; try
                     assumption; auto. }
                 eapply typed_false_to_digit in H15.
                 eassumption.
                 }
             unfold Z_of_char in *.
             cbn.
             nia.
             (* end of vl = ub && d <= last_digit *)

             (* vl > ub && d > ld, out of range *)
             { int64_to_Z.
                assert (bounded (value_until_d (j + 1) (i :: ls)) = false) as Bound.
               { 
                 erewrite next_value_lt_ub.
                 eapply  eq_ub_not_bounded_plus.
                 all:  unfold Z_of_char in *;
                   try eassumption; try nia.
                 auto.
               } 
               forward.
               forward.
               erewrite ERROR_RANGE_res.
               simpl.
               entailer!.
               erewrite sepcon_assoc.    
               erewrite <- DATA_AT1. 
               erewrite <- DATA_AT2.
               entailer!.
                all: 
                 unfold Z_of_char in *; autorewrite with sublist; 
                  try nia; try eassumption.
                intros.
                destruct (zeq i0 j).
                subst. eassumption.
                eapply H4.
                nia.
                rep_omega_setup.
                nia.
             } (* end of case vl = ub && d > last_digit *)
           } all: try nia.
             (* case vl > ub *) 
             { 
               lt_ub_to_Z H11.
              assert (value_until_d j (i :: ls) > upper_boundary)
                     by nia.
              assert (bounded (value_until_d (j + 1) (i :: ls)) = false) as Bound.
              { erewrite next_value_lt_ub.
                eapply lt_ub_not_bounded_plus.
                all: unfold Z_of_char in *;
                  try eassumption; try nia. auto. }                
               repeat forward.
              erewrite ERROR_RANGE_res.
              simpl.
               entailer!.
               erewrite sepcon_assoc.      
               erewrite <- DATA_AT1.
               erewrite <- DATA_AT2. 
               entailer!. 
               all: autorewrite with sublist;
                 try eassumption; try nia.
               intros.
               destruct (zeq i0 j).
               subst. eassumption.
               eapply H4.
               nia. }                  
             (* i0 non-digit: extra data *)
           { eapply typed_false_to_digit in H8.
             forward.
             forward.
             forward.
             erewrite EXTRA_DATA_no_sign_res with (j := j).
                simpl.
             entailer!.
             erewrite sepcon_assoc.      
             erewrite <- DATA_AT1.
             erewrite <- DATA_AT2.
             entailer!.
             all: autorewrite with sublist; try (nia || eassumption); auto. }
  }   
        * reflexivity.
        * nia.
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
      assert (Zlength (i :: ls) = 0) as L by nia.
      subst.
      pose proof Zlength_nil_inv (i :: ls) L as NIL.
      rewrite NIL; simpl; entailer!.
    +  (* end' <= str = true || str < end' = true (from forward_if) *)
      try apply Z.ltb_lt in IFCON.
      rewrite EQB in H; apply typed_fa(i :: ls)e_ptr_ge in H.
      rewrite Z.gtb_lt in H. lia.
Admitted.
