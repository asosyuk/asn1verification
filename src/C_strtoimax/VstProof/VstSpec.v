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
         contents : list byte,
         (* contents of intp *)
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

          (* length of contents = distance between str and end' *)
          Zlength contents =
          Z.max 0 (Ptrofs.unsigned end'_ofs - Ptrofs.unsigned str_ofs))
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
           (* str points to contents with readable permission *)
           data_at sh_str (tarray tschar (Zlength contents)) 
                   (map Vbyte contents) (Vptr str_b str_ofs) ; 
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
         of abstract spec on contents *)
      LOCAL (temp ret_temp (Vint (asn_strtox_result_e_to_int 
                                   (res 
                                      (Z_of_string contents)))))
      (* Propositions about memory that hold after executing the function *)
      SEP( (* this part didn't change after execution *) 
           
           valid_pointer (Vptr end'_b end'_ofs) ;
           valid_pointer (Vptr str_b str_ofs) ;
           data_at sh_str (tarray tschar (Zlength contents)) 
                   (map Vbyte contents) (Vptr str_b str_ofs) ;
           let r := res (Z_of_string contents) in
            (* in 3 cases intp stays unchanged,
              otherwise store the end value of Z_of_string *)
            match r with 
              | ASN_STRTOX_ERROR_RANGE 
              | ASN_STRTOX_ERROR_INVAL 
              | ASN_STRTOX_EXPECT_MORE => 
                data_at sh_intp (tlong) v (Vptr intp_b intp_ofs)
              | _ => data_at sh_intp (tlong) 
                         (Vlong (Int64.repr (value (Z_of_string contents))))
                         (Vptr intp_b intp_ofs) 
            end ;
           (* if str >= end, end doesn't change, 
              otherwise store the address of the last char read 
              (before going out of range, reading extra data 
              or successfully terminating) *)
            let i := index (Z_of_string contents) in
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


Definition Gprog := ltac:(with_library prog [asn_strtoimax_lim_vst_spec]).

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
      subst; apply typed_false_ptr_ge in H.
      rewrite Z.gtb_lt in H.
      assert (0 < Ptrofs.unsigned end'_ofs - Ptrofs.unsigned str_ofs)
        by Lia.lia.
      destruct contents.
      replace (Zlength []) with (0) in LEN by reflexivity.
      Lia.lia.
      rewrite semax_lemmas.cons_app in LEN.
      rewrite semax_lemmas.cons_app with (x := i).
      rewrite Zlength_app in LEN.
      assert (Zlength [i] = 1) as SING by reflexivity.
      assert (Zlength contents = (Ptrofs.unsigned end'_ofs - 
                                 Ptrofs.unsigned str_ofs) - 1) by lia.
      rename H1 into LEN2.
      assert (Zlength (map Vbyte [i]) = 1) as SINGB by reflexivity.
      assert (Zlength (map Vbyte contents) = Zlength contents) 
        as LENB by (apply Zlength_map); rewrite LEN2 in LENB.
      rewrite <-Zlength_app in LEN; rewrite LEN; rewrite map_app.
      rewrite split2_data_at_Tarray_app with (mid := 1) ; [|try eassumption | admit].
      Intros.
      rename v into v0.
      assert (map Vbyte [i] = [Vbyte i]) as T by reflexivity.
      pose proof data_at_singleton_array_eq (sh_str) (tschar) (Vbyte i) 
           (map Vbyte [i]) (Vptr end'_b str_ofs) T as T1; rewrite T1; clear T T1.
      forward.
      forward.
      normalize.
      pose (sep_precondition := 
              valid_pointer (Vptr end'_b end'_ofs) *
              valid_pointer (Vptr end'_b str_ofs) *
              data_at sh_str tschar (Vbyte i) (Vptr end'_b str_ofs) *
              data_at sh_str (tarray tschar 
                                     (Ptrofs.unsigned end'_ofs - 
                                      Ptrofs.unsigned str_ofs - 1))
                      (map Vbyte contents)
                      (field_address0 (tarray tschar 
                                              (Ptrofs.unsigned end'_ofs - 
                                               Ptrofs.unsigned str_ofs))
                                      [ArraySubsc 1] (Vptr end'_b str_ofs)) *
              data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs) 
                      (Vptr end_b end_ofs) *
              data_at sh_intp tlong v0 (Vptr intp_b intp_ofs)).
      forward_if (
          if Byte.signed i =? 45
          then PROP()
               LOCAL(temp _sign (Vint (Int.repr (-1)));
                     temp _str (Vptr end'_b
                                     (Ptrofs.add str_ofs (Ptrofs.repr 1))))
               SEP(sep_precondition)
          else if Byte.signed i =? 43
               then PROP()
                    LOCAL( temp _str (Vptr end'_b 
                                           (Ptrofs.add str_ofs (Ptrofs.repr 1))))
                    SEP(sep_precondition)
               else !!(Byte.signed i =? 43 = false /\ Byte.signed i =? 45 = false)). 
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
           admit.
           apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
           entailer!.
           apply valid_pointer_weak.
           (* end_ofs <= str_ofs + 1, return EXPECT_MORE *)
        ** repeat forward.
           rename H1 into IFCON2.
           apply typed_true_ptr_ge in IFCON2.
           replace (Ptrofs.add str_ofs (Ptrofs.mul (Ptrofs.repr 1) 
                                                   (Ptrofs.of_ints (Int.repr 1))))
             with (Ptrofs.add str_ofs Ptrofs.one) in * by auto with ptrofs.
           apply Z.geb_le in IFCON2.
           replace (Ptrofs.unsigned (Ptrofs.add str_ofs Ptrofs.one)) 
             with (Ptrofs.unsigned str_ofs + 1) in *. (* follows from IFCON *)
           assert (Ptrofs.unsigned end'_ofs - Ptrofs.unsigned str_ofs - 1 = 0) as Z 
               by nia.
           assert (contents = []) as CONTENT.
           rewrite Z in LEN2.
           apply Zlength_nil_inv; assumption.
           rewrite CONTENT.
           unfold is_sign, plus_char, minus_char.
           assert (Byte.eq i (Byte.repr 45) = true) as IS.
           erewrite Byte.eq_signed.
           break_if; auto.
           rewrite IS; simpl.
           replace (Byte.eq i (Byte.repr 43) || true)%bool with true by intuition.
           simpl.
           entailer!.
           assert (map Vbyte [i] = [Vbyte i]) as T by reflexivity.
           rewrite <-T; rewrite SING.
           pose proof data_at_singleton_array_eq (sh_str) (tschar) (Vbyte i) 
                (map Vbyte [i]) (Vptr end'_b str_ofs) T as T1; rewrite T1; clear T T1. 
           entailer!.
           replace (Ptrofs.unsigned end'_ofs - Ptrofs.unsigned str_ofs - 1) with 0.
           apply data_at_zero_array_inv; simpl; reflexivity.
           admit. (* Need to add precondition about str_ofs + Zlength contents <= Ptrofs.unsigned_max *)
        ** (* str_ofs + 1 < end_ofs *)
          forward.
          rename H1 into IFCON2.
          subst.
          apply typed_false_ptr_ge in IFCON2.
          replace (Ptrofs.add str_ofs (Ptrofs.mul (Ptrofs.repr 1) 
                                                  (Ptrofs.of_ints (Int.repr 1))))
            with (Ptrofs.add str_ofs Ptrofs.one) in * by auto with ptrofs.
          rewrite Z.gtb_lt in IFCON2.
          replace (Ptrofs.unsigned (Ptrofs.add str_ofs Ptrofs.one)) 
            with (Ptrofs.unsigned str_ofs + 1) in *. (* follows from IFCON *)
          rewrite E.
          replace (Ptrofs.unsigned str_ofs + 1 <? Ptrofs.unsigned end'_ofs)
            with true.
          unfold sep_precondition. entailer!.
          admit.
          admit.
      * (* if *str = '+' *)
        repeat forward.
        forward_if.
        admit.
        repeat forward.
        entailer!.
        normalize.
        eapply typed_true_ptr_ge in H1.
        replace  (Ptrofs.add str_ofs (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1))))
          with  (Ptrofs.add str_ofs (Ptrofs.repr 1)) in * by auto with ptrofs.
        assert (contents = []) as N.
        eapply Z.geb_le in H1.
        replace (Ptrofs.unsigned (Ptrofs.add str_ofs (Ptrofs.repr 1)))
          with (Ptrofs.unsigned str_ofs + 1) in * by admit. (* follows from IFCON *)
        assert (Ptrofs.unsigned end'_ofs - Ptrofs.unsigned str_ofs - 1 = 0) as Z by nia.
        
        autorewrite with sublist in *|-.
        rewrite Z in LEN2.
        Search Zlength [].
        apply Zlength_nil_inv.
        assumption.
        rewrite N.
        unfold is_sign, plus_char, minus_char.
        assert (Byte.eq i (Byte.repr 43) = true) as IS.
        Search Byte.eq.
        erewrite Byte.eq_signed.
        break_if; auto.
        rewrite IS; simpl.
        replace (true || Byte.eq i (Byte.repr 45))%bool with true.
        reflexivity.
        reflexivity.
        normalize.
        eapply typed_true_ptr_ge in H1.
        replace  (Ptrofs.add str_ofs (Ptrofs.mul (Ptrofs.repr 1)
                                                 (Ptrofs.of_ints (Int.repr 1))))
          with  (Ptrofs.add str_ofs (Ptrofs.repr 1)) in * by auto with ptrofs.
        assert (contents = []) as N.
        eapply Z.geb_le in H1.
        replace (Ptrofs.unsigned (Ptrofs.add str_ofs (Ptrofs.repr 1)))
          with (Ptrofs.unsigned str_ofs + 1) in * by admit. (* follows from IFCON *)
        assert (Ptrofs.unsigned end'_ofs - Ptrofs.unsigned str_ofs - 1 = 0) as Z by nia.
        
        autorewrite with sublist in *|-.
        rewrite Z in LEN2.
        apply Zlength_nil_inv.
        assumption.
        rewrite N.
        unfold is_sign, plus_char, minus_char.
        assert (Byte.eq i (Byte.repr 43) = true) as IS.
        erewrite Byte.eq_signed.
        break_if; auto.
        rewrite IS; simpl.
        replace (true || Byte.eq i (Byte.repr 45))%bool with true.
        simpl.
        entailer.
        erewrite data_at_singleton_array_eq.
        instantiate (1 :=  (Vbyte i)).
        entailer!.
        rewrite <- H14.
        autorewrite with sublist.
        rewrite data_at_zero_array_eq.
        entailer!.
        all: try auto.
        
        forward.
        rewrite E.
        replace (43 =? 45) with false by reflexivity.
        replace (43 =? 43) with true by reflexivity.
        replace (Ptrofs.unsigned str_ofs + 1 <? Ptrofs.unsigned end'_ofs)
          with true.
        unfold sep_precondition. entailer!.
        admit.    
      * (* default case *) 
        forward.
        replace (Byte.signed i =? 45) with false.
        replace (Byte.signed i =? 43) with false.
        unfold sep_precondition. entailer.
        admit.
        admit.
      * (* Loop *)
        repeat break_if.
        ** forward.
           forward_loop (
               EX i : Z, 
                 let i' := (Ptrofs.add str_ofs (Ptrofs.repr i)) in
                 PROP(0 <= i <= Zlength contents)
                 LOCAL(temp _end (Vptr end_b end_ofs); 
                       temp _intp (Vptr intp_b intp_ofs);
                       temp _str (Vptr end'_b i');
                       temp _value (Vlong (Int64.repr 
                                            (value (Z_of_string
                                                      (sublist 0 i contents))))))
                 SEP(
                   valid_pointer (Vptr end'_b end'_ofs) *
                   valid_pointer (Vptr end'_b i') *
                   data_at sh_str
                           (tarray tschar (Ptrofs.unsigned end'_ofs -
                                           Ptrofs.unsigned str_ofs))
                           (map Vbyte contents)
                           (field_address0
                              (tarray tschar (Ptrofs.unsigned end'_ofs -
                                              Ptrofs.unsigned str_ofs))
                              [ArraySubsc i] 
                              (Vptr end'_b str_ofs)) *
                   data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs)
                           (Vptr end_b end_ofs) *
                   data_at sh_intp tlong v0 (Vptr intp_b intp_ofs)))
           break: (PROP()
                  LOCAL( if true then temp _sign (Vint (Int.repr 1))
                         else temp _sign (Vint (Int.repr (-1)));

                       temp _end (Vptr end_b end_ofs); 
                       temp _intp (Vptr intp_b intp_ofs);
                       temp _str 
                             (Vptr end'_b 
                                   (Ptrofs.add str_ofs 
                                      (Ptrofs.repr (Zlength contents))));
                      if true (* TODO *)
                        then temp _value (Vlong (Int64.repr
                                  (value (Z_of_string contents))))
                        else temp _value (Vlong (Int64.repr
                                  (- value (Z_of_string contents)))))
                  SEP(valid_pointer (Vptr end'_b end'_ofs) ;
                      valid_pointer (Vptr end'_b str_ofs) ;
                      data_at sh_str (tarray tschar (Zlength contents)) 
                                 (map Vbyte contents) (Vptr end'_b str_ofs) ; 
                      data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs) 
                                 (Vptr end_b end_ofs);
                      data_at sh_intp (tlong) v0 (Vptr intp_b intp_ofs))).
           ***
             Exists 1.
             entailer!.
             admit.
             unfold sep_precondition.
             entailer!.
             admit. (* fix loop invariant *)
         *** Intros x.
             forward.
             forward_if.
             -- admit.
             -- admit.
             -- forward.
                entailer!.
                admit.
         *** repeat forward.
             admit.
             
        ** admit.
        ** admit.
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
      assert (Zlength contents = 0) as L by admit.
      subst.
      pose proof Zlength_nil_inv contents L as NIL.
      rewrite NIL; simpl; entailer!.
    +  (* end' <= str = true || str < end' = true (from forward_if) *)
      try apply Z.ltb_lt in IFCON.
      rewrite EQB in H; apply typed_false_ptr_ge in H.
      rewrite Z.gtb_lt in H. lia.
Admitted.
