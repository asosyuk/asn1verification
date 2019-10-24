(* VST specification of asn_strtoimax_lim *)
Require Import Clight.INTEGER. 
Require Import Core.Core Core.Tactics Core.PtrLemmas.
Require Import StructTact.StructTactics.
Require Import VST.floyd.proofauto.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Require Import AbstractSpecFinal.

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

Lemma body_asn_strtoimax_lim : semax_body Vprog Gprog f_asn_strtoimax_lim  asn_strtoimax_lim_vst_spec.
Proof.
  start_function.
  rename H into EQB.
  rename H0 into LEN.
  forward.
  forward.
  forward.
  entailer!; break_and; inversion H7. 
  forward.
  entailer!; break_and; inversion H7.
  destruct Z.ltb eqn:IFCON.
  all: Intros.
  all: forward.
  all: forward_if.
  all: try apply Z.ltb_lt in IFCON.
  all: try apply Z.ltb_ge in IFCON.
  
  - (* str < end' = true *)
    (* Valid pointer proof *)
    unfold test_order_ptrs; simpl.
    destruct peq; [simpl|contradiction].

    apply andp_right.
    *
      autorewrite with sublist in *|-.
      (* follows from LEN and IFCON *)
      assert (valid_pointer (Vptr end'_b end'_ofs) * valid_pointer (Vptr end'_b str_ofs) *
              data_at sh_str (tarray tschar (Zlength contents)) (map Vbyte contents) (Vptr end'_b str_ofs) *
              data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs) *
              data_at sh_intp tlong v (Vptr intp_b intp_ofs)
                      |-- valid_pointer (Vptr end'_b str_ofs)) by entailer!.
      pose proof valid_pointer_weak (Vptr end'_b str_ofs).
      apply derives_trans with (Q := valid_pointer (Vptr end'_b str_ofs)).
      all: assumption.
    *
      assert (valid_pointer (Vptr end'_b end'_ofs) * valid_pointer (Vptr end'_b str_ofs) *
              data_at sh_str (tarray tschar (Zlength contents)) (map Vbyte contents) (Vptr end'_b str_ofs) *
              data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs) *
              data_at sh_intp tlong v (Vptr intp_b intp_ofs)|-- valid_pointer (Vptr end'_b end'_ofs)) 
        by entailer!.
      pose proof valid_pointer_weak (Vptr end'_b end'_ofs).
      apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
      all: assumption.

  - (* str < end' = true || end' <= str = true (from forward_if) *)
    forward.
    apply typed_true_ptr_ge in H.
    rewrite Z.geb_le in H; Lia.lia.

  - (* str < end' = true || str < end' = true (from forward_if) *)
    rewrite EQB in H; apply typed_false_ptr_ge in H.
    rewrite Z.gtb_lt in H.
    autorewrite with sublist in *|-.
    assert (0 < Ptrofs.unsigned end'_ofs - Ptrofs.unsigned str_ofs)
      by Lia.lia.
    admit.

  - (* end' <= str = true *)
    (* Valid pointer proof *)
    unfold test_order_ptrs; simpl.
    destruct peq; [simpl|contradiction].

    apply andp_right.
    * 
      assert ( valid_pointer (Vptr end'_b end'_ofs) * valid_pointer (Vptr end'_b str_ofs) *
               data_at sh_str (tarray tschar (Zlength contents)) (map Vbyte contents) (Vptr end'_b str_ofs) *
               data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs) *
               data_at sh_intp tlong v (Vptr intp_b intp_ofs) 
                      |-- valid_pointer (Vptr end'_b str_ofs)) by entailer!.
      pose proof valid_pointer_weak (Vptr end'_b str_ofs).
      apply derives_trans with (Q := valid_pointer (Vptr end'_b str_ofs)).
      all: assumption.
    *
      assert (valid_pointer (Vptr end'_b end'_ofs) * valid_pointer (Vptr end'_b str_ofs) *
              data_at sh_str (tarray tschar (Zlength contents)) (map Vbyte contents) (Vptr end'_b str_ofs) *
              data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs) *
              data_at sh_intp tlong v (Vptr intp_b intp_ofs) 
                      |-- valid_pointer (Vptr end'_b end'_ofs)) by entailer!.
      pose proof valid_pointer_weak (Vptr end'_b end'_ofs).
      apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
      all: assumption.

  - (* end' <= str = true || end' <= str = true (from forward_if) *)
    forward.
    autorewrite with sublist in *|-.
    pose proof Zlength_nil_inv contents LEN as NIL.
    rewrite NIL; simpl; entailer!.
  - (* end' <= str = true || str < end' = true (from forward_if) *)
    rewrite EQB in H; apply typed_false_ptr_ge in H.
    rewrite Z.gtb_lt in H; Lia.lia.
Admitted.
