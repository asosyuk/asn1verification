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
                    LOCAL(temp _sign (Vint (Int.repr (1)));
                     temp _str (Vptr end'_b
                                     (Ptrofs.add str_ofs (Ptrofs.repr 1)));
                     temp _end (Vptr end_b end_ofs); 
                     temp _intp (Vptr intp_b intp_ofs);
                     temp _last_digit_max
                          (Vlong (last_digit_max_int));
                     temp _upper_boundary (Vlong upper_boundary_int))
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
        * (* if *str = '-' = Int.repr 45 *)
        forward.
        entailer!.
        { replace (Int64.repr 0) with (Int64.zero) by reflexivity; 
            replace (Int64.repr 1) with (Int64.one) by reflexivity.
          rewrite Int64.not_zero.
          unfold Int64.mods, Int64.shru, Z.shiftr.
          rewrite Int64.unsigned_mone, Int64.unsigned_one; simpl.
          repeat rewrite Int64.signed_repr;
            unfold Int64.min_signed, Int64.max_signed;
            unfold Int64.half_modulus, Int64.modulus;
            cbn; Lia.lia. }
        repeat forward.
        forward_if.
        ** unfold test_order_ptrs; simpl.
           destruct peq; [simpl|contradiction].
           apply andp_right.
           apply derives_trans with
               (Q := valid_pointer (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr 1)))).
           destruct ls.
           -- autorewrite with sublist.
              simpl; entailer!.
           -- autorewrite with sublist.
              entailer!.
           --  apply valid_pointer_weak.
           --
           entailer!.
           apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
           entailer!.
           apply valid_pointer_weak.
           (* end_ofs <= str_ofs + 1, return EXPECT_MORE *)
        ** repeat forward.
           rename H2 into IFCON2.
           apply typed_true_ptr_ge in IFCON2.
           replace (Ptrofs.add str_ofs (Ptrofs.mul (Ptrofs.repr 1) 
                                                   (Ptrofs.of_ints (Int.repr 1))))
             with (Ptrofs.add str_ofs Ptrofs.one) in * by auto with ptrofs.
           apply Z.geb_le in IFCON2.
           replace (Ptrofs.unsigned (Ptrofs.add str_ofs Ptrofs.one)) 
             with (Ptrofs.unsigned str_ofs + 1) in *. (* follows from IFCON *)
           assert (Ptrofs.unsigned end'_ofs - Ptrofs.unsigned str_ofs - 1 = 0) as Z 
               by nia.
           assert (ls = []) as CONTENT.
           rewrite Z in LS_len.
           apply Zlength_nil_inv; assumption.
           rewrite CONTENT.
           unfold is_sign, plus_char, minus_char.
           assert ((Byte.signed i =? 45) = true) as IS.
           Zbool_to_Prop. eassumption.
           bool_rewrite.
           replace ((Byte.signed i =? 43) || true)%bool with true by intuition.
           simpl.
           entailer!.
           simpl.
           autorewrite with sublist.
           simpl.
           erewrite data_at_zero_array_eq.
           erewrite data_at_singleton_array_eq.
           entailer!.
           all: auto; try econstructor.
           ptrofs_compute_add_mul.
           auto with ptrofs.
           replace (Ptrofs.unsigned Ptrofs.one) with 1 by auto with ptrofs.
           autorewrite with sublist in *|-.
           assert (0 <= (Zlength ls)) by eapply Zlength_nonneg.
           replace (Z.succ (Zlength ls)) with (Zlength ls + 1) in *.
           assert (0 <= Ptrofs.unsigned str_ofs).
           eapply Ptrofs.unsigned_range.
           nia.
           nia.      
        ** (* str_ofs + 1 < end_ofs *)
          forward.
          rename H2 into IFCON2.
          subst.
          apply typed_false_ptr_ge in IFCON2.
          autorewrite with norm in *.
          replace (Ptrofs.unsigned
                         (Ptrofs.add str_ofs (Ptrofs.repr 1)))
            with (Ptrofs.unsigned str_ofs  + 1) in *
               by (autorewrite with norm;
                   ptrofs_compute_add_mul;
                   rep_omega_setup;
                   nia).
          rewrite E.
          unfold sep_precondition. entailer!.   
          apply Zgt_is_gt_bool in IFCON2.
          nia.          
      * (* if *str = '+' *)
        repeat forward.
        forward_if.
        unfold test_order_ptrs; simpl.
           destruct peq; [simpl|contradiction].
           apply andp_right.
           apply derives_trans with
               (Q := valid_pointer (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr 1)))).
           destruct ls.
           autorewrite with sublist.
              simpl; entailer!.
           autorewrite with sublist.
              entailer!.
            apply valid_pointer_weak.
          
           entailer!.
           apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
           entailer!.
           apply valid_pointer_weak.
           subst.
           rewrite_comparison.
           autorewrite with norm in H2.
           replace (Ptrofs.unsigned
                         (Ptrofs.add str_ofs (Ptrofs.repr 1)))
            with (Ptrofs.unsigned str_ofs  + 1) in *
               by (autorewrite with norm;
                   ptrofs_compute_add_mul;
                   rep_omega_setup;
                   nia).
           apply Z.geb_le in H2.
        forward.
        forward.       
        assert (ls = []) as N.
        autorewrite with sublist in *|-.
        apply Zlength_nil_inv.
        nia.
        rewrite N.
        unfold is_sign, plus_char, minus_char.
        assert ((Byte.signed i =? 43) = true) as IS.
        Zbool_to_Prop.
        nia.
        bool_rewrite.
        auto.
        simpl.
        entailer!.
        erewrite data_at_singleton_array_eq.
        instantiate (1 :=  (Vbyte i)).
        entailer!.
        rewrite data_at_zero_array_eq.
        entailer!.
        all: try auto.
        subst.
        rewrite_comparison.
          autorewrite with norm in *.
          replace (Ptrofs.unsigned
                         (Ptrofs.add str_ofs (Ptrofs.repr 1)))
            with (Ptrofs.unsigned str_ofs  + 1) in *
               by (autorewrite with norm;
                   ptrofs_compute_add_mul;
                   rep_omega_setup;
                   nia).
          apply Zgt_is_gt_bool in H2.
        forward.
        rewrite E.
        subst.
         unfold sep_precondition.
         entailer!.
      * (* default case *) 
        forward.
        replace (Byte.signed i =? 45) with false.
        replace (Byte.signed i =? 43) with false.
        unfold sep_precondition. entailer!.
        assert ((Int.repr (Byte.signed i)) <> (Int.repr 43)) as K.
        unfold not; intro L.
        rewrite L in *.
        intuition.
        eapply repr_neq_e in K.
        symmetry.
        Zbool_to_Prop.
        nia.
         assert ((Int.repr (Byte.signed i)) <> (Int.repr 45)).
        intuition.
        rewrite H2 in *.
        intuition.
         eapply repr_neq_e in H2.
         symmetry.
         Zbool_to_Prop.
         nia.
      * (* Loop *)
        repeat break_if;
          unfold sep_precondition.
        (* minus *)
       **
         assert (is_sign i = true) as SGN 
              by (unfold is_sign, minus_char; bool_rewrite; intuition).
          assert (Byte.signed i =? minus_char = true) as MCH 
              by (unfold is_sign, minus_char; bool_rewrite; intuition).
          assert (Byte.signed i =? plus_char = false) as PCH 
              by (rewrite Z.eqb_eq in Heqb; rewrite Heqb; intuition).
          forward.
          remember (Ptrofs.add str_ofs Ptrofs.one) as str_ofs'.
           remember (Int64.unsigned upper_boundary) as ub.
           remember (i :: ls) as ls'.
           forward_loop (
               EX j : Z, EX vl : Z,
                 let i' := Ptrofs.add str_ofs (Ptrofs.repr (j + 1)) in
                (* let b := if Ptrofs.unsigned str_ofs + j + 1 >=?
                             Ptrofs.unsigned end'_ofs then false else true in *)
                 PROP(0 <= j <= Zlength ls;
                      Ptrofs.unsigned str_ofs + j + 1 < Ptrofs.modulus;
                      forall (i : Z), 0 <= i < j -> is_digit (Znth i ls) = true;
                        bounded (value_until j ls true 0 1) = true)
                 LOCAL(temp _end (Vptr end_b end_ofs); 
                       temp _intp (Vptr intp_b intp_ofs);
                       temp _str (Vptr end'_b i');
                       temp _value (Vlong (Int64.repr (value_until j ls true 0 1)));
                       temp _sign (Vint (Int.repr ((*(if b then 1 else *) -1)));
                       temp _upper_boundary (Vlong upper_boundary);
                       temp _last_digit_max
                            (Vlong (Int64.add last_digit_max Int64.one)))
                 SEP(
                    valid_pointer (Vptr end'_b (Ptrofs.add str_ofs 
                                                              (Ptrofs.repr (Zlength (i :: ls)))));
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
               
           break: (EX j : Z, 
                    let b := if Ptrofs.unsigned str_ofs + j + 1 >=? 
                                Ptrofs.unsigned end'_ofs then true else false in
                    PROP(0 <= j <= Zlength ls;
                        forall i, 0 <= i < Zlength ls -> 
                             is_digit (Znth i ls) = true;
                         bounded (value (Z_of_string_loop ls 0 1 b)) = true)
                    LOCAL(
                      temp _value (Vlong (Int64.repr (value (Z_of_string_loop ls 0 1 b))));
                      temp _sign (Vint (Int.repr (if b then -1 else 1)));

                      temp _end (Vptr end_b end_ofs); 
                      temp _intp (Vptr intp_b intp_ofs);
                      temp _str (Vptr end'_b 
                                 (Ptrofs.add str_ofs 
                                             (Ptrofs.repr (Zlength ls + 1)))))

                    SEP(
                       valid_pointer (Vptr end'_b (Ptrofs.add str_ofs 
                                                              (Ptrofs.repr (Zlength (i :: ls)))));
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
               assert (0 <= value (Z_of_string_loop ls 0 1 true)) by 
               (eapply loop_non_neg; nia);
               try nia;
               try rep_omega.
               forward.
               erewrite OK_sign_res.
               all: unfold sign_to_bool.
               all: try bool_rewrite.
               simpl.
               break_if;
                 autorewrite with sublist; try entailer!;
               replace (-1 * value (Z_of_string_loop ls 0 1 true))%Z with
                   (- value (Z_of_string_loop ls 0 1 true)) by nia.
               try erewrite value_false_eq_neg_value_true0.
               try entailer!.
               all: try (eassumption || nia || auto).
               break_if; try eassumption.
               eapply bounded_true_to_false; eassumption. }
           ***
             Exists 0 0.
             entailer!.
             { intros. nia. }
             autorewrite with sublist.
             erewrite data_at_zero_array_eq.
             entailer!.
             all: try (erewrite sublist_1_cons || autorewrite with sublist);
               autorewrite with sublist; (reflexivity || auto with zarith || auto).
           ***
             Intros j vl.
             assert (0 <= value_until j ls true 0 1) as NN 
                 by (eapply loop_non_neg; nia).
              assert (bounded (value_until j ls false 0 1) = true) as BF
                      by (eapply bounded_true_to_false;
                 eassumption) .
               assert (value_until j ls false 0 1 <= 0) as NNF 
                 by (eapply loop_neg; nia).
               assert (bounded 0 = true) as B0.
               { unfold bounded.
                 rewrite andb_true_iff in *.
                 repeat Zbool_to_Prop.
                 cbn.
                 nia. }
               assert (Int64.min_signed <= value_until j ls true 0 1 <= Int64.max_signed)
                 as BP by
               (erewrite bounded_bool_to_Prop in H6; eassumption).
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
                 autorewrite with sublist; 
                 (reflexivity || auto with zarith || auto).
               symmetry.
               erewrite Z.geb_le.
               nia. }
             }
           
            (* normal: str + j + 1 <  end *)
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
               * apply derives_trans with 
                     (Q := valid_pointer (Vptr end'_b end'_ofs)).
                 entailer!.
                 replace end'_ofs with (Ptrofs.add str_ofs (Ptrofs.repr (j + 1))).
                 apply valid_pointer_weak.
                 { autorewrite with sublist in LEN.
                   replace (Zlength ls) with j in LEN by nia.
                   assert (Ptrofs.unsigned str_ofs + 1 + j = 
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
             assert (Ptrofs.unsigned (Ptrofs.add str_ofs (Ptrofs.repr (j + 1)))
                     <? Ptrofs.unsigned end'_ofs = true) as P.
             erewrite Z.ltb_lt.
             eassumption.            
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
               replace (negb (Int.lt (Int.repr 57) 
                                     (Int.repr (Byte.signed (Znth j ls)))))
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
             pose proof (is_digit_to_Z i0 H9).
             forward.
             forward.
             forward_if.
            (* Case:  vl < ub *)
           { lt_ub_to_Z H10; 
             lt_ub_to_Z H11; 
             try nia.
             forward.
             entailer!.
             { repeat rewrite Int64.signed_repr;
                 try eapply lt_ub_to_next_bounded_Prop;
                 try eassumption; try nia. }
             forward.
             (* show that loop invariant holds after normal  loop body execution *)
             Exists (j + 1) (value_until (j + 1) ls true 0 1).
             entailer!.
             erewrite next_value_lt_ub with (i := Znth j ls).
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
           lt_ub_to_Z H11.
             forward_if.
             lt_ub_to_Z H12.

           (* vl == ub *)
           { forward_if.
             lt_ub_to_Z H13.                          
             (* d <= last_digit_max *)
             { forward_if 
                 (PROP ( )
     LOCAL (
       temp _value (Vlong (Int64.repr 
(- value (Z_of_string_loop (sublist 0 j ls) 0 1 true) * 10 - (Byte.signed i0 - 48))));
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
       valid_pointer (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr (Zlength (i :: ls)))));
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
               replace (Ptrofs.unsigned str_ofs + j + 1 >=?
                                                        Ptrofs.unsigned end'_ofs)
                 with false.
               entailer!.
                repeat split; try easy.
                replace (Zlength ls) with (j + 1) by nia.
               eapply app_is_digit; try easy.
               replace ls with (sublist 0 (j + 1) ls).
               {
               rewrite next_value_lt_ub with (i := Znth j ls).
               eapply eq_ub_bounded_minus.
               eapply loop_neg; nia.
               apply is_digit_to_Z in H9; assumption.
               erewrite value_false_eq_neg_value_true0.
               all: try (nia || eassumption || auto). }
               replace (j + 1) with (Zlength ls) by nia.
               autorewrite with sublist; auto.

               do 2 f_equal.

               replace ls with (sublist 0 (j + 1) ls) at 1.
               rewrite  next_value_lt_ub with (i := Znth j ls).
               unfold Z_of_char.
               replace (0) with (-0) by lia.
               rewrite value_false_eq_neg_value_true.
               reflexivity.
               all: try eassumption; try nia; auto.
               autorewrite with sublist; auto.
               replace (j + 1) with (Zlength ls) by nia.
               autorewrite with sublist; auto.
               erewrite sepcon_assoc.
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
           rewrite Z.geb_leb; symmetry; rewrite Z.leb_gt; lia. } } 
             (* compare pointers *)
             { autorewrite with sublist.
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
               }

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
               assert ( 0 <= value_until (j + 1) ls true 0 1) as NN1 by (eapply loop_non_neg; nia).

               forward_if.

                (* ERROR RANGE spec *)
               {rewrite <- ZN1 in *.
                rewrite <- ZN in *.
                eapply typed_true_to_digit in H16.
                assert (bounded (value_until (j + 1) ls false 0 1) = true) 
                  as Boundf.
                {  rewrite next_value_lt_ub with (i := Znth j ls).
                   eapply eq_ub_bounded_minus.
                   eapply loop_neg; nia.
                   apply is_digit_to_Z in H9; assumption.
                   erewrite value_false_eq_neg_value_true0.
                   all: try nia; try
                                   assumption; auto. }
                
                assert (bounded (value_until ((j + 1) + 1) ls false 0 1) = false) 
                  as BoundF.
                
                { 
                  erewrite next_value_lt_ub with 
                      (j := j + 1) (i := (Znth (j + 1) ls)).
                  
                  apply lt_ub_not_bounded_minus.
                  eapply is_digit_to_Z in H16.
                  nia.
                  rewrite next_value_lt_ub with (i := Znth j ls).
                  eapply eq_ub_next_gt_ub_minus.
                  eapply loop_neg; nia.
                  eapply is_digit_to_Z in H9.
                  nia.
                  erewrite value_false_eq_neg_value_true0.
                  all: try nia;
                    try eassumption; auto.
                  eapply app_is_digit.
                  all: try nia;
                    try eassumption; auto. }

                  assert (j + 1 + 1 <= Zlength ls) as LS_len2 by nia.

                  assert (res (Z_of_string_loop ls 0 1 false) = ERROR_RANGE) as Result_loop.
                  { 
                    assert ((Zlength (sublist 0 (j + 1 + 1) ls))
                            =  (j + 1 + 1)) as SB
                        by  (erewrite Zlength_sublist;
                             subst;
                             try nia).
                    edestruct all_digits_OK_or_ERROR_RANGE_loop
                      with (ls := (sublist 0 (j + 1 + 1) ls)) (v:= 0) (i := 1)
                    (b := false); try rewrite SB.
                    eapply app_is_digit;  try rewrite SB;
                      try nia.
                    eapply app_is_digit;  try rewrite SB;
                      try nia.                  
                    intros.
                    erewrite Znth_sublist.
                    normalize.
                    all: try nia; try eassumption.
                    all: try erewrite Znth_sublist;
                      try nia; normalize; subst; try eassumption.
                    assert (res (Z_of_string_loop (sublist 0 (j + 1 + 1) ls) 0 1 false) = OK).
                    erewrite H17.
                    auto.
                    eapply OK_bounded_loop
                      with (ls := sublist 0 (j + 1 + 1) ls) (b := false) in H18.
                    congruence.
                    eassumption.
                    eapply sublist_ERROR_RANGE with (j := j + 1 + 1) in H17.
                    rewrite H17.
                    auto.
                    nia. }

                  assert (res (Z_of_string (i :: ls)) = ERROR_RANGE) as Result.
                  {
                    simpl.
                    repeat bool_rewrite.
                    break_match. 
                    autorewrite with sublist in H2;
                      try nia.
                    eassumption.
                  }                 
                  assert (index (Z_of_string_loop ls 0 1 false) = j + 1 + 1) as Index_loop.
                  { eapply ERROR_RANGE_index; try eassumption;
                      try nia.
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
                  replace (Zlength (i :: ls)) with (Z.succ (Zlength ls)).
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
                  autorewrite with sublist; reflexivity.  }                               
               forward.
               forward.

               erewrite EXTRA_DATA_sign_res with (j := j + 1).
               unfold sign_to_bool.
               bool_rewrite.
               simpl.
                erewrite next_value_lt_ub with (i := (Znth j ls)).
                erewrite value_false_eq_neg_value_true0.
               replace (Zlength (i :: ls)) with (Z.succ (Zlength ls))
                                               by (autorewrite with sublist; nia).
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
                all: try (eassumption || nia|| auto).
               eapply app_is_digit.
                all: try (eassumption || nia || auto).
                unfold sign_to_bool. bool_rewrite.
                 {  rewrite next_value_lt_ub with (i := Znth j ls).
                     eapply eq_ub_bounded_minus.
                     eapply loop_neg; nia.
                     
                     apply is_digit_to_Z in H9; assumption.
                     erewrite value_false_eq_neg_value_true0.
                     all: try nia; try
                     assumption; auto. }
                 eapply typed_false_to_digit in H16.
                 eassumption.
                 }
             apply is_digit_to_Z in H9.
             unfold Z_of_char in *.
             cbn.
             nia.  
             (* end of vl = ub && d <= last_digit *)

             (* vl > ub && d > ld, out of range *)
             { lt_ub_to_Z H13.
               
              assert (bounded (value_until (j + 1) ls false 0 1) = false) as Bound.
               { 
                 erewrite next_value_lt_ub.
                 eapply  eq_ub_not_bounded_minus.
                 eapply loop_neg; nia.
                 eapply is_digit_to_Z; eassumption.
                 erewrite value_false_eq_neg_value_true0.

                 all:  unfold Z_of_char in *;
                   try eassumption; try nia. 
               } 
               repeat forward.
               erewrite ERROR_RANGE_sign_res.
               simpl.
               entailer!.
               { autorewrite with sublist in DATA_AT1.
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
                 unfold sign_to_bool; try bool_rewrite;
                 try nia; try eassumption.
               eapply is_digit_to_Z in H9.
               unfold Z_of_char in *.
               cbn.
               nia. }
             } (* end of case vl = ub && d > last_digit *)
           nia.
           
             (* case vl > ub *) 
             { 
              lt_ub_to_Z H12.
              assert (value_until j ls true 0 1 > AbstractSpec.upper_boundary)
                     by nia.
              assert (bounded (value_until (j + 1) ls false 0 1) = false) as Bound.
              { erewrite next_value_lt_ub.
                eapply lt_ub_not_bounded_minus.
                eapply is_digit_to_Z; eassumption.
                erewrite value_false_eq_neg_value_true0.
                all: unfold Z_of_char in *;
                  try eassumption; try nia. }                
               repeat forward.
              erewrite ERROR_RANGE_sign_res.
              simpl.
               entailer!.
               { 
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
               all: try unfold sign_to_bool; try bool_rewrite; 
                 try eassumption; try nia. }                         
             nia.
             (* i0 non-digit: extra data *)
           { eapply typed_false_to_digit in H9.
             forward.
             forward.
             forward.
             erewrite EXTRA_DATA_sign_res with (j := j).
                simpl.
                unfold sign_to_bool.
                bool_rewrite.
                 erewrite value_false_eq_neg_value_true0.
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
               all: try (nia || eassumption); auto.
             destruct ((sign_to_bool i)); try eassumption. } } 
       (* plus *)   
       **
          assert (is_sign i = true) as SGN 
              by (unfold is_sign, minus_char; bool_rewrite; intuition).
          assert (Byte.signed i =? minus_char = false) as MCH 
              by (unfold is_sign, minus_char; bool_rewrite; intuition).
          assert (Byte.signed i =? plus_char = true) as PCH by intuition. 
          forward.
          remember (Ptrofs.add str_ofs Ptrofs.one) as str_ofs'.
           remember (Int64.unsigned upper_boundary) as ub.
           remember (i :: ls) as ls'.
           forward_loop (
               EX j : Z, EX vl : Z,
                 let i' := Ptrofs.add str_ofs (Ptrofs.repr (j + 1)) in
                 PROP(0 <= j <= Zlength ls;
                      Ptrofs.unsigned str_ofs + j + 1 < Ptrofs.modulus;
                      forall (i : Z), 0 <= i < j -> is_digit (Znth i ls) = true;
                        bounded (value_until j ls true 0 1) = true)
                 LOCAL(temp _end (Vptr end_b end_ofs); 
                       temp _intp (Vptr intp_b intp_ofs);
                       temp _str (Vptr end'_b i');
                       temp _value (Vlong (Int64.repr (value_until j ls true 0 1)));
                       temp _sign (Vint (Int.repr 1));
                       temp _upper_boundary (Vlong upper_boundary);
                       temp _last_digit_max
                            (Vlong last_digit_max_int))
                 SEP(
                    valid_pointer (Vptr end'_b (Ptrofs.add str_ofs 
                                                              (Ptrofs.repr (Zlength (i :: ls)))));
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
               
           break: (EX j : Z, 
                    PROP(0 <= j <= Zlength ls;
                        forall i, 0 <= i < Zlength ls -> 
                             is_digit (Znth i ls) = true;
                         bounded (value (Z_of_string_loop ls 0 1 true)) = true)
                    LOCAL(
                      temp _value (Vlong (Int64.repr (value (Z_of_string_loop ls 0 1 true))));
                      temp _sign (Vint (Int.repr 1));

                      temp _end (Vptr end_b end_ofs); 
                      temp _intp (Vptr intp_b intp_ofs);
                      temp _str (Vptr end'_b 
                                 (Ptrofs.add str_ofs 
                                             (Ptrofs.repr (Zlength ls + 1)))))

                    SEP(
                       valid_pointer (Vptr end'_b (Ptrofs.add str_ofs 
                                                              (Ptrofs.repr (Zlength (i :: ls)))));
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
               forward.
               entailer!.
               all: erewrite OK_sign_res.
               all: unfold sign_to_bool.
               all: try bool_rewrite.
               auto.
               all: try (eassumption || nia || auto).
               simpl.
               autorewrite with sublist; entailer!.
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
           ***
             Intros j vl.
             assert (0 <= value_until j ls true 0 1) as NN 
                 by (eapply loop_non_neg; nia).
               assert (Int64.min_signed <= value_until j ls true 0 1 <= Int64.max_signed)
                 as BP by
               (erewrite bounded_bool_to_Prop in H6; eassumption).
               pose proof bounded0 as B0.
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
                 autorewrite with sublist; 
                 (reflexivity || auto with zarith || auto).
               symmetry.
               erewrite Z.geb_le.
               nia. }
             }
           
            (* normal: str + j + 1 <  end *)
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
               * apply derives_trans with 
                     (Q := valid_pointer (Vptr end'_b end'_ofs)).
                 entailer!.
                 replace end'_ofs with (Ptrofs.add str_ofs (Ptrofs.repr (j + 1))).
                 apply valid_pointer_weak.
                 { autorewrite with sublist in LEN.
                   replace (Zlength ls) with j in LEN by nia.
                   assert (Ptrofs.unsigned str_ofs + 1 + j = 
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
             assert (Ptrofs.unsigned (Ptrofs.add str_ofs (Ptrofs.repr (j + 1)))
                     <? Ptrofs.unsigned end'_ofs = true) as P.
             erewrite Z.ltb_lt.
             eassumption.            
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
               replace (negb (Int.lt (Int.repr 57) 
                                     (Int.repr (Byte.signed (Znth j ls)))))
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
             pose proof (is_digit_to_Z i0 H9).
             forward.
             forward.
             forward_if.
            (* Case:  vl < ub *)
           { lt_ub_to_Z H10; 
             lt_ub_to_Z H11; 
             try nia.
             forward.
             entailer!.
             { repeat rewrite Int64.signed_repr;
                 try eapply lt_ub_to_next_bounded_Prop;
                 try eassumption; try nia. }
             forward.
             (* show that loop invariant holds after normal  loop body execution *)
             Exists (j + 1) (value_until (j + 1) ls true 0 1).
             entailer!.
             erewrite next_value_lt_ub with (i := Znth j ls).
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
           lt_ub_to_Z H11.
             forward_if.
             lt_ub_to_Z H12.

           (* vl == ub *)
           { forward_if.
              int64_to_Z.                         
             (* d <= last_digit_max *)
             { forward_if 
                 (PROP ( )
     LOCAL (
       temp _value (Vlong (Int64.repr 
( value (Z_of_string_loop (sublist 0 j ls) 0 1 true) * 10 + (Byte.signed i0 - 48))));
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
       temp _last_digit_max (Vlong last_digit_max_int))
     SEP (
       valid_pointer (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr (Zlength (i :: ls)))));
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
             forward.
             entailer!.
             {
               unfold bounded in *.
               rewrite andb_true_iff in *.
               repeat rewrite Z.leb_le in *.
                repeat rewrite Int64.signed_repr;
                 repeat rewrite Int.signed_repr;
                 rep_omega_setup;
                 assert (0 <= value (Z_of_string_loop ls 0 1 true)) by 
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
          (Ptrofs.add (Ptrofs.add str_ofs (Ptrofs.repr (j + 1)))
             (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1)))))
                     with (Ptrofs.unsigned str_ofs + j + 1 + 1) in *
               by (autorewrite with norm;
                   ptrofs_compute_add_mul;
                   rep_omega_setup;
                   nia).
             (* post-if implies break condition *)
             { Exists j.
               replace (Ptrofs.unsigned str_ofs + j + 1 >=?
                                                        Ptrofs.unsigned end'_ofs)
                 with false.
               entailer!.
                repeat split; try easy.
                replace (Zlength ls) with (j + 1) by nia.
               eapply app_is_digit; try easy.
               replace ls with (sublist 0 (j + 1) ls).
               {
               rewrite next_value_lt_ub with (i := Znth j ls).
               eapply eq_ub_bounded_plus.
               all: try (nia || eassumption || auto). 
              }
               replace (j + 1) with (Zlength ls) by nia.
               autorewrite with sublist; auto.
               do 2 f_equal.
               replace ls with (sublist 0 (j + 1) ls) at 1.
               rewrite  next_value_lt_ub with (i := Znth j ls).
               reflexivity.
               all: try eassumption; try nia; auto.
               autorewrite with sublist; auto.
               replace (j + 1) with (Zlength ls) by nia.
               autorewrite with sublist; auto.
               erewrite sepcon_assoc.
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
           rewrite Z.geb_leb; symmetry; rewrite Z.leb_gt; lia. } } 
             (* compare pointers *)
             { autorewrite with sublist.
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
               }

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
               assert ( 0 <= value_until (j + 1) ls true 0 1) as NN1 by (eapply loop_non_neg; nia).

               forward_if.

                (* ERROR RANGE spec *)
               {rewrite <- ZN1 in *.
                rewrite <- ZN in *.
                eapply typed_true_to_digit in H16.
                assert (forall i0 : Z, 0 <= i0 < j + 1 -> is_digit (Znth i0 ls) = true) as D.
                eapply app_is_digit.
                  all: try nia;
                    try eassumption; auto.
                assert (bounded (value_until (j + 1) ls true 0 1) = true) 
                  as Boundf.
                {  rewrite next_value_lt_ub with (i := Znth j ls).
                   eapply eq_ub_bounded_plus.
                   all: try nia; try
                                   assumption; auto. }
                
                assert (bounded (value_until ((j + 1) + 1) ls true 0 1) = false) 
                  as BoundF.
                
                { 
                  erewrite next_value_lt_ub with 
                      (j := j + 1) (i := (Znth (j + 1) ls)).
                  
                  apply lt_ub_not_bounded_plus.
                   eapply is_digit_to_Z in H16.
                  nia.
                  rewrite next_value_lt_ub with (i := Znth j ls).
                  eapply eq_ub_next_gt_ub_plus.
                  all: try nia;
                    try eassumption; auto. }

                  assert (j + 1 + 1 <= Zlength ls) as LS_len2 by nia.

                 
                  forward.
                  erewrite ERROR_RANGE_sign_res.
                  replace (Zlength (i :: ls)) with (Z.succ (Zlength ls)).
                  simpl.
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
                  autorewrite with sublist; reflexivity.
                    all: unfold sign_to_bool; try bool_rewrite;
                      try nia;
                    try eassumption; auto.
               }                               
               forward.
               forward.

               erewrite EXTRA_DATA_sign_res with (j := j + 1).
               unfold sign_to_bool.
               bool_rewrite.
               simpl.
                erewrite next_value_lt_ub with (i := (Znth j ls)).
               replace (Zlength (i :: ls)) with (Z.succ (Zlength ls))
                                               by (autorewrite with sublist; nia).
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
                all: try (eassumption || nia || auto).
               eapply app_is_digit.
                all: try (eassumption || nia || auto).
                unfold sign_to_bool. bool_rewrite.
                 {  rewrite next_value_lt_ub with (i := Znth j ls).
                     eapply eq_ub_bounded_plus.
                     all: try nia; try
                     assumption; auto. }
                 eapply typed_false_to_digit in H16.
                 eassumption.
                 }
             unfold Z_of_char in *.
             cbn.
             nia.
             (* end of vl = ub && d <= last_digit *)

             (* vl > ub && d > ld, out of range *)
             {  int64_to_Z.
                assert (bounded (value_until (j + 1) ls true 0 1) = false) as Bound.
               { 
                 erewrite next_value_lt_ub.
                 eapply  eq_ub_not_bounded_plus.
                 all:  unfold Z_of_char in *;
                   try eassumption; try nia.
               } 
               repeat forward.
               erewrite ERROR_RANGE_sign_res.
               simpl.
               entailer!.
               { autorewrite with sublist in DATA_AT1.
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
                all: 
                 unfold sign_to_bool; try bool_rewrite;
                 unfold Z_of_char in *; cbn; 
                 try nia; try eassumption.
               
             } (* end of case vl = ub && d > last_digit *)
           } all: try nia.
             (* case vl > ub *) 
             { 
              lt_ub_to_Z H12.
              assert (value_until j ls true 0 1 > AbstractSpec.upper_boundary)
                     by nia.
              assert (bounded (value_until (j + 1) ls true 0 1) = false) as Bound.
              { erewrite next_value_lt_ub.
                eapply lt_ub_not_bounded_plus.
                all: unfold Z_of_char in *;
                  try eassumption; try nia. }                
               repeat forward.
              erewrite ERROR_RANGE_sign_res.
              simpl.
               entailer!.
               { 
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
               all: try unfold sign_to_bool; try bool_rewrite; 
                 try eassumption; try nia. }                         
             (* i0 non-digit: extra data *)
           { eapply typed_false_to_digit in H9.
             forward.
             forward.
             forward.
             erewrite EXTRA_DATA_sign_res with (j := j).
                simpl.
                unfold sign_to_bool.
                bool_rewrite.
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
               all: unfold sign_to_bool; try bool_rewrite; try (nia || eassumption); auto.
             }
           }
          (* default case *)
       ** 
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
      assert (Zlength ls = 0) as L by nia.
      subst.
      pose proof Zlength_nil_inv ls L as NIL.
      rewrite NIL; simpl; entailer!.
    +  (* end' <= str = true || str < end' = true (from forward_if) *)
      try apply Z.ltb_lt in IFCON.
      rewrite EQB in H; apply typed_false_ptr_ge in H.
      rewrite Z.gtb_lt in H. lia.
Admitted.
