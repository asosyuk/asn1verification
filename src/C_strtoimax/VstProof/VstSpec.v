(* VST specification of asn_strtoimax_lim *)
Require Import Clight.INTEGER.
Require Import Core.Core Core.Tactics Core.PtrLemmas.
Require Import StructTact.StructTactics Psatz.
Require Import VST.floyd.proofauto.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Require Import AbstractSpec.

Section VstSpec.

Definition asn_strtoimax_lim_vst_spec : ident * funspec :=
  DECLARE _asn_strtoimax_lim
    (* WITH: binds variables in Pre- and Postconditions *)
    WITH (* start of the string str *)
         str_b : block, str_ofs : ptrofs,
         (* end of the string *end *)
         end'_b : block, end'_ofs : ptrofs,
         (* stores address of the end of the string end *)
         end_b : block, end_ofs : ptrofs,
         (* stores result intp *)
         intp_b : block, intp_ofs : ptrofs,
         (* permission shares, cf. Verifiable C book (p.73) *)
         sh_str : share, sh_end : share, sh_intp : share,
         (* input string *)
         ls : list byte,
         (* ls of intp *)
         v : val
    (* Preconditions *)
    (* Type declaration for parameters of the function *)
    PRE [ _str OF (tptr tschar),
          _end OF (tptr (tptr tschar)),
          _intp OF (tptr tlong) ]
    (* PROP: Propositions (of type Prop) that should hold
       before executing the function. ; is conjuction *)
      PROP ( (* Permissions for memory access *)
          readable_share sh_str;  (* str points to readable memory *)
          writable_share sh_end;  (* end points to writable memory *)
          writable_share sh_intp; (* intp points to writable memory *)

          (* str and end' should point to the same object, 
           otherwise incomparable by C standard *)
          str_b = end'_b;

          (* length of ls = distance between str and end' *)
          Zlength ls =
          Z.max 0 (Ptrofs.unsigned end'_ofs - Ptrofs.unsigned str_ofs);

         (* No pointer overflow occurs *)
         Ptrofs.unsigned str_ofs + Zlength ls < Ptrofs.modulus        
                
      )
      (* LOCAL: connects C light prameter identifiers and declared variables *)
      LOCAL (temp _str (Vptr str_b str_ofs);
             temp _end (Vptr end_b end_ofs); 
             temp _intp (Vptr intp_b intp_ofs))
      (* SEP: Propositions about memory (of type mem -> Prop (mpred)) that 
         should hold before executing the function. 
         ; (and * ) is separating conjunction, && is ordinary conjuction *)
      SEP ((* str and end' are comparable, i.e. point within the same object *)
           valid_pointer (Vptr end'_b end'_ofs) ;
           valid_pointer (Vptr str_b str_ofs) ;
           (* str points to ls with readable permission *)
           data_at sh_str (tarray tschar (Zlength ls)) 
                   (map Vbyte ls) (Vptr str_b str_ofs) ; 
           (* end points to end' with writable permission *)
           data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs) 
                   (Vptr end_b end_ofs);
           (* intp points to some value v  *)
           data_at sh_intp (tlong) v (Vptr intp_b intp_ofs))     
    (* Postconditions *)
    (* Type declaration for return value of the function *)
    POST [tint]
      (* No new propositions hold after executing the function *)
      PROP()
      (* Return value of the function corresponds to the result 
         of abstract spec on ls *)
      LOCAL (temp ret_temp (Vint (asn_strtox_result_e_to_int 
                                   (res 
                                      (Z_of_string ls)))))
      (* Propositions about memory that hold after executing the function *)
      SEP( (* this part didn't change after execution *) 
           
           valid_pointer (Vptr end'_b end'_ofs) ;
           valid_pointer (Vptr str_b str_ofs) ;
           data_at sh_str (tarray tschar (Zlength ls)) 
                   (map Vbyte ls) (Vptr str_b str_ofs) ;
           let r := res (Z_of_string ls) in
            (* in 3 cases intp stays unchanged,
              otherwise store the end value of Z_of_string *)
            match r with 
              | ASN_STRTOX_ERROR_RANGE 
              | ASN_STRTOX_ERROR_INVAL 
              | ASN_STRTOX_EXPECT_MORE => 
                data_at sh_intp (tlong) v (Vptr intp_b intp_ofs)
              | _ => data_at sh_intp (tlong) 
                         (Vlong (Int64.repr (value (Z_of_string ls))))
                         (Vptr intp_b intp_ofs) 
            end ;
           (* if str >= end, end doesn't change, 
              otherwise store the address of the last char read 
              (before going out of range, reading extra data 
              or successfully terminating) *)
            let i := index (Z_of_string ls) in
            if (Ptrofs.unsigned str_ofs <? Ptrofs.unsigned end'_ofs)
            then data_at sh_end (tptr tschar) 
                         (Vptr str_b (Ptrofs.add str_ofs (Ptrofs.repr i))) 
                         (Vptr end_b end_ofs)
            else data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs) 
                         (Vptr end_b end_ofs)).

End VstSpec.

(* Proof *)

Lemma typed_true_ptr_ge : forall b ptr1 ptr2, 
    typed_true tint (force_val (sem_cmp_pp Cge (Vptr b ptr1) (Vptr b ptr2))) ->
    Ptrofs.unsigned ptr1 >=? Ptrofs.unsigned ptr2 = true.
Proof.
  intros.
  unfold typed_true, force_val, sem_cmp_pp in H; simpl in H.
  destruct eq_block in H; [simpl in H|discriminate].
  unfold Ptrofs.ltu in H.
  destruct zlt in H; [discriminate|simpl in H].
  rewrite Z.geb_le.
  Lia.lia.
Qed.

Lemma typed_false_ptr_ge : forall b ptr1 ptr2,
    typed_false tint (force_val (sem_cmp_pp Cge (Vptr b ptr1) (Vptr b ptr2))) ->
    Ptrofs.unsigned ptr2 >? Ptrofs.unsigned ptr1 = true.
Proof.
  intros.
  unfold typed_false, force_val, sem_cmp_pp in H; simpl in H.
  destruct eq_block in H; [simpl in H|discriminate].
  unfold Ptrofs.ltu in H.
  destruct zlt in H; [simpl in H|discriminate].
  rewrite Z.gtb_lt.
  Lia.lia.
Qed.

(* Proposition data_at_array_valid_pointer *)

Arguments valid_pointer p : simpl never.

Lemma extend_weak_valid_pointer : forall b ofs P, 
    valid_pointer (Vptr b ofs) * P |-- weak_valid_pointer (Vptr b ofs).
Proof.
  intros.
  pose proof valid_pointer_weak (Vptr b ofs).
  apply derives_trans with (Q := valid_pointer (Vptr b ofs)).
  entailer!.
  eassumption.
Qed.


Proposition split_non_empty_list i ls' ls sh b ofs:
      ls = i::ls'  -> Ptrofs.unsigned ofs + Zlength ls < Ptrofs.modulus -> 
      data_at sh (tarray tschar (Zlength ls)) (map Vbyte ls) (Vptr b ofs) =
      data_at sh tschar (Vbyte i) (Vptr b ofs) *
      data_at sh (tarray tschar (Zlength ls')) (map Vbyte ls')
              (Vptr b (Ptrofs.add ofs Ptrofs.one)).
Proof.
  intros LEN MOD.
  rewrite LEN.
  rewrite semax_lemmas.cons_app with (x := i).
  rewrite map_app. 
  rewrite split2_data_at_Tarray_app with (mid := 1).
  assert (map Vbyte [i] = [Vbyte i]) as T by reflexivity.
  pose proof data_at_singleton_array_eq sh tschar (Vbyte i) 
       (map Vbyte [i]) (Vptr b ofs) T as T1; rewrite T1; clear T T1.

  assert (Vptr b (Ptrofs.add ofs Ptrofs.one) =
          field_address0 (tarray tschar (Zlength (app [i] ls'))) [ArraySubsc 1]
                         (Vptr b ofs))
    as J.
  { 
    rewrite field_address0_offset.
    reflexivity.
    econstructor.
    easy.
    repeat split.
    simpl; autorewrite with norm.
    rewrite <- LEN.
    eassumption.
    constructor.
    intros.
    repeat econstructor.
    simpl; autorewrite with norm.
    reflexivity.
    all: try nia || auto with zarith.
    autorewrite with sublist.
    simpl.
    pose proof (Zlength_nonneg ls').
    nia.
  }
  rewrite J.
  replace (Zlength (app [i] ls') - 1) with (Zlength ls').
  reflexivity.
  all: try autorewrite with sublist; auto.
Qed.

Definition Gprog := ltac:(with_library prog [asn_strtoimax_lim_vst_spec]).

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
              SEP (valid_pointer (Vptr end'_b end'_ofs);
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
                 let i' := Ptrofs.add str_ofs' (Ptrofs.repr j) in
                 PROP(0 <= j <= Zlength ls;
                      Ptrofs.unsigned str_ofs' + j < Ptrofs.modulus)
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
                  (* valid_pointer (Vptr end'_b i') ; *)

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
             replace (Zlength (i :: ls) - 0- 1) with (Zlength (ls)).
             replace (sublist 1 (Zlength (i :: ls)) (i :: ls)) with ls.
             entailer!.
             all: try (erewrite sublist_1_cons || autorewrite with sublist);
             autorewrite with sublist; (reflexivity || auto with zarith || auto).
         *** Intros j vl.
             forward.
             forward_if.
             (* move to a tactic *)
             { unfold test_order_ptrs; simpl.
               destruct peq; [simpl|contradiction].
               apply andp_right.
               * apply derives_trans with (Q := valid_pointer
                                        (Vptr end'_b (Ptrofs.add
                                                        (Ptrofs.add str_ofs Ptrofs.one) 
                                                        (Ptrofs.repr j)))).
                 entailer!.
                 admit.
                 apply valid_pointer_weak.
               * apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
                 entailer!.
                 apply valid_pointer_weak. }
             remember (sublist j (Zlength ls) ls) as ls''.
             assert (0 < Zlength ls'').
             { subst.
               autorewrite with sublist in *|-.
               autorewrite with sublist.
               (* follows from H5 *)
               admit. }
             destruct ls''.
             try erewrite (Zlength_nil byte) in *.
             nia.
             replace (Zlength ls - j) with (Zlength ((i0::ls''))).
             
             (* reading a char i0 *)
             erewrite split_non_empty_list with (i := i0) (ls' := ls'')
             (ofs := (Ptrofs.add str_ofs' (Ptrofs.repr j))).
             
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
             admit.
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
       temp _str (Vptr end'_b (Ptrofs.add str_ofs' (Ptrofs.repr j)));
       
       temp _upper_boundary (Vlong upper_boundary);
       temp _last_digit_max (Vlong (Int64.add last_digit_max Int64.one)))
     SEP (
       valid_pointer (Vptr end'_b str_ofs);
       valid_pointer (Vptr end'_b end'_ofs);
       data_at sh_str tschar (Vbyte i) (Vptr end'_b str_ofs);
       data_at sh_str (tarray tschar j) (map Vbyte (sublist 1 (j + 1) ls')) (Vptr end'_b str_ofs');
       data_at sh_str tschar (Vbyte i0) (Vptr end'_b (Ptrofs.add str_ofs' (Ptrofs.repr j)));
       data_at sh_str (tarray tschar (Zlength ls'')) (map Vbyte ls'')
               (Vptr end'_b (Ptrofs.add (Ptrofs.add str_ofs' (Ptrofs.repr j)) Ptrofs.one));
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
             (* true, data_at_succ_sublist lemma *)
             admit.
             
             repeat forward.
             forward_if.
             (* compare pointers *)
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
