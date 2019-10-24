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
               valid_pointer (Vptr end'_b end'_ofs) *
               data_at sh_e (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs);
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
               valid_pointer (Vptr end'_b end'_ofs) *
               data_at sh_e (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs);
          data_at sh_r tint res (Vptr intp_b intp_ofs)).

End VstStrtoimaxSpec.

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

Definition Gprog := ltac:(with_library prog [asn_strtoimax_lim_vst_spec]).

Lemma body_asn_strtoimax_lim : semax_body Vprog Gprog f_asn_strtoimax_lim  asn_strtoimax_lim_vst_spec.
Proof.
  start_function.
  rename H into EQB.
  rename H0 into LEN.
  forward.
  forward.
  forward.
  entailer!; inversion H1; inversion H3.
  forward.
  entailer!; inversion H1; inversion H3.
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
      assert (data_at sh_s (tarray tschar (Zlength con)) 
                      (map Vbyte (map Byte.repr con)) (Vptr end'_b str_ofs) * 
              data_at sh_e (tptr tschar) (Vptr end'_b end'_ofs) 
                      (Vptr end_b end_ofs) * 
              data_at sh_s tschar ch (Vptr end'_b end'_ofs) * 
              data_at sh_r tint res (Vptr intp_b intp_ofs) 
                      |-- valid_pointer (Vptr end'_b str_ofs)) by entailer!.
      pose proof valid_pointer_weak (Vptr end'_b str_ofs).
      apply derives_trans with (Q := valid_pointer (Vptr end'_b str_ofs)).
      all: assumption.
    *
      assert (data_at sh_s (tarray tschar (Zlength con)) 
                      (map Vbyte (map Byte.repr con)) (Vptr end'_b str_ofs) * 
              data_at sh_e (tptr tschar) (Vptr end'_b end'_ofs) 
                      (Vptr end_b end_ofs) * 
              data_at sh_s tschar ch (Vptr end'_b end'_ofs) * 
              data_at sh_r tint res (Vptr intp_b intp_ofs) 
                      |-- valid_pointer (Vptr end'_b end'_ofs)) 
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
      assert (valid_pointer (Vptr end'_b str_ofs) * 
              valid_pointer (Vptr end'_b end'_ofs) * 
              data_at sh_e (tptr tschar) (Vptr end'_b end'_ofs) 
                      (Vptr end_b end_ofs) * 
              data_at sh_r tint res (Vptr intp_b intp_ofs) 
                      |-- valid_pointer (Vptr end'_b str_ofs)) by entailer!.
      pose proof valid_pointer_weak (Vptr end'_b str_ofs).
      apply derives_trans with (Q := valid_pointer (Vptr end'_b str_ofs)).
      all: assumption.
    *
      assert (valid_pointer (Vptr end'_b str_ofs) * 
              valid_pointer (Vptr end'_b end'_ofs) * 
              data_at sh_e (tptr tschar) (Vptr end'_b end'_ofs) 
                      (Vptr end_b end_ofs) * 
              data_at sh_r tint res (Vptr intp_b intp_ofs) 
                      |-- valid_pointer (Vptr end'_b end'_ofs)) by entailer!.
      pose proof valid_pointer_weak (Vptr end'_b end'_ofs).
      apply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
      all: assumption.

  - (* end' <= str = true || end' <= str = true (from forward_if) *)
    forward.
    autorewrite with sublist in *|-.
    pose proof Zlength_nil_inv con LEN as NIL.
    rewrite NIL; simpl; entailer!.
  - (* end' <= str = true || str < end' = true (from forward_if) *)
    rewrite EQB in H; apply typed_false_ptr_ge in H.
    rewrite Z.gtb_lt in H; Lia.lia.
Admitted.
