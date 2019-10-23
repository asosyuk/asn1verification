(* VST specification of asn_strtoimax_lim *)
Require Import Clight.INTEGER.


Require Import Spec2.
Require Import Core.Core Core.Tactics Core.PtrLemmas.
Require Import StructTact.StructTactics.
Require Import VST.floyd.proofauto.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Section VstStrtoimaxSpec.

 Definition asn_strtoimax_lim_vst_spec : ident * funspec :=
  DECLARE _asn_strtoimax_lim
    WITH str_b : block, str_ofs : ptrofs,
         (* points at the start of the string *)
         end_b : block, end_ofs : ptrofs,
         (* points at the end of the string *)
         end'_b : block, end'_ofs : ptrofs,
         (* points at the last character in the string *)
         intp_b : block, intp_ofs : ptrofs,
         (* pointers to store result in *)
         sh_s : share, sh_e : share, sh_r : share,
         (* string share, end share, result share *)
         con : list Z, ch : val, res : val
         (* contents, char at the end of string, initial value of intp *)
    PRE [_str OF (tptr tschar), _end OF (tptr (tptr tschar)), _intp OF (tptr tlong)]
      PROP(readable_share sh_s; writable_share sh_e; writable_share sh_r;
           str_b = end'_b;
           Zlength con = Z.max 0 (Ptrofs.unsigned end'_ofs - Ptrofs.unsigned str_ofs))
      LOCAL(temp _str (Vptr str_b str_ofs);
            temp _end (Vptr end_b end_ofs); 
            temp _intp (Vptr intp_b intp_ofs))
      SEP(if (Ptrofs.unsigned str_ofs <? Ptrofs.unsigned end'_ofs) 
          then data_at sh_s (tarray tschar (Zlength con)) 
                       (map Vbyte (map Byte.repr con)) (Vptr str_b str_ofs) * 
               data_at sh_e (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs) * 
               data_at sh_s tschar ch (Vptr end'_b end'_ofs)
          else valid_pointer (Vptr str_b str_ofs) * 
               valid_pointer (Vptr end_b end_ofs) *
               valid_pointer (Vptr end'_b end'_ofs);
          data_at sh_r tint res (Vptr intp_b intp_ofs))
    POST [tint]
      PROP()
      LOCAL(temp ret_temp (Vint (asn_strtox_result_e_to_int 
                                   (return_type 
                                      (asn_strtoimax_lim_spec con)))))
      SEP(if (Ptrofs.unsigned str_ofs <? Ptrofs.unsigned end'_ofs) 
          then data_at sh_s (tarray tschar (Zlength con)) 
                       (map Vbyte (map Byte.repr con)) (Vptr str_b str_ofs) * 
               data_at sh_e (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs) * 
               data_at sh_s tschar ch (Vptr end'_b end'_ofs)
          else valid_pointer (Vptr str_b str_ofs) * 
               valid_pointer (Vptr end_b end_ofs) *
               valid_pointer (Vptr end'_b end'_ofs);
          data_at sh_r tint res (Vptr intp_b intp_ofs)).

Arguments valid_pointer p : simpl never.

End VstStrtoimaxSpec.

Lemma Zmax0ltr : forall x, 0 < x -> Z.max 0 x = x.
Proof.
  intros.
  unfold Z.max.
  destruct Z.compare eqn:LOL; [congruence|reflexivity|congruence].
Qed.

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
    Ptrofs.unsigned ptr2 >=? Ptrofs.unsigned ptr1 = true.
Proof.
  intros.
  unfold typed_false, force_val, sem_cmp_pp in H; simpl in H.
  destruct eq_block in H; [simpl in H|discriminate].
  unfold Ptrofs.ltu in H.
  destruct zlt in H; [simpl in H|discriminate].
  rewrite Z.geb_le.
  Lia.lia.
Qed.

Definition Gprog := ltac:(with_library prog [asn_strtoimax_lim_vst_spec]).

Lemma body_asn_strtoimax_lim : semax_body Vprog Gprog f_asn_strtoimax_lim  asn_strtoimax_lim_vst_spec.
Proof.
  start_function.
  forward.
  forward.
  forward.
  entailer!;
       inversion H;
       inversion H4.
  forward.
  entailer!;
       inversion H;
       inversion H4.
  destruct Z.ltb eqn:KEK.
  Intros.
  forward.
  apply Z.ltb_lt in KEK.
  rewrite <-Z.lt_0_sub in KEK.
  pose proof Zmax0ltr (Ptrofs.unsigned end_ofs - Ptrofs.unsigned str_ofs) KEK.
  rewrite H1 in H0; clear H1.
  forward_if.
  
  unfold test_order_ptrs; simpl.
  destruct peq; [simpl|contradiction].
  apply andp_right.
  - 
    assert (data_at sh_s (tarray tschar (Zlength con)) 
                    (map Vbyte (map Byte.repr con)) (Vptr end'_b str_ofs) * 
            data_at sh_e (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs) * 
            data_at sh_s tschar ch (Vptr end'_b end'_ofs) * 
            data_at sh_r tint res (Vptr intp_b intp_ofs) 
                    |-- valid_pointer (Vptr end'_b str_ofs)) by entailer!.
    pose proof valid_pointer_weak (Vptr end'_b str_ofs).
    apply derives_trans with (Q := valid_pointer (Vptr end'_b str_ofs)).
    all: assumption.
  -
    assert (data_at sh_s (tarray tschar (Zlength con)) 
                    (map Vbyte (map Byte.repr con)) (Vptr end'_b str_ofs) * 
            data_at sh_e (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs) * 
            data_at sh_s tschar ch (Vptr end'_b end'_ofs) * 
            data_at sh_r tint res (Vptr intp_b intp_ofs) 
                    |-- valid_pointer (Vptr end'_b end'_ofs)) by entailer!.
    pose proof valid_pointer_weak (Vptr end'_b end'_ofs).
    apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
    all: assumption.
  - (* str_ofs <= end_ofs = true *)
    rewrite H in H1.
    apply typed_true_ptr_ge in H1.
    rewrite Z.geb_le in H1.
    rewrite Z.lt_0_sub in KEK.
    contradict KEK.
    apply Znot_lt_ge.
    
    admit.
  - (* str_ofs > end_ofs = true *)
    rewrite H in H1.
    apply typed_false_ptr_ge in H1.
    rewrite Z.geb_le in H1.
    rewrite Z.lt_0_sub in KEK.
    *
    
    * entailer!.
    
  

Admitted.
