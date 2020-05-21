Require Import Core.Core  Core.VstTactics Core.StructNormalizer VstLib DWT.Exec 
        ErrorWithWriter.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_tlv_tag ExecBer_tlv_tag_serialize.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Definition ber_tlv_tag_serialize_spec : ident * funspec :=
  DECLARE _ber_tlv_tag_serialize
  WITH tag: Z, bufp : val, size : Z, buf_size : Z
  PRE[tuint, tptr tvoid, tuint]
    PROP(0 <= size < Int.modulus;
         32 <= buf_size )
    PARAMS(Vint (Int.repr tag); bufp; Vint (Int.repr size))
    GLOBALS()
    SEP(data_at_ Tsh (tarray tuchar buf_size) bufp)
  POST[tuint]
    let (ls, z) := ber_tlv_tag_serialize tag size in
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr z)))
    SEP(if eq_dec ls [] 
        then data_at_ Tsh (tarray tuchar buf_size) bufp 
        else data_at Tsh (tarray tuint (Zlength ls)) (map Vubyte ls) bufp).

Definition Gprog := ltac:(with_library prog [ber_tlv_tag_serialize_spec]).

Theorem ber_tlv_tag_serialize_correct : 
  semax_body Vprog Gprog (normalize_function f_ber_tlv_tag_serialize composites)
             ber_tlv_tag_serialize_spec.
Proof.
  start_function.
  repeat forward.
  forward_if.
  - forward_if (
       let (ls, z) := ber_tlv_tag_serialize tag size in
       PROP()
       LOCAL()
       SEP(if eq_dec size 0 
           then data_at_ Tsh (tarray tuchar buf_size) bufp 
           else data_at Tsh (tarray tuint (Zlength ls)) (map Vubyte ls) bufp)).
    + forward. break_let. 
      rewrite_if_b. entailer!.
       unfold upd_Znth.
      break_if.
      autorewrite with sublist.
      entailer!.
      unfold ber_tlv_tag_serialize in *.
      replace (Z.shiftr tag 2 <=? 30) with true in *.
      break_if.
      replace l with [Byte.repr (Z.lor (Z.shiftl (Z.land tag 3) 6) (Z.shiftr tag 2))].
      entailer!.
      unfold upd_Znth. 
      all: admit.
    + forward. break_let. entailer!. 
      break_if. entailer.
      assert (Int.unsigned (Int.repr size) = Int.unsigned (Int.repr 0)).
      f_equal. auto.
      repeat rewrite Int.unsigned_repr_eq in *.
      rewrite Zmod_small in *.
      rewrite Zmod_small in *.
      nia.
      rep_omega.
      nia.
    + unfold POSTCONDITION.
      unfold abbreviate. 
      break_let.
      forward.
      rewrite_if_b.
      break_if.
      unfold ber_tlv_tag_serialize in *.
      replace (Z.shiftr tag 2 <=? 30) with true in *.
      admit.
      admit.
      unfold ber_tlv_tag_serialize in *.
      replace (Z.shiftr tag 2 <=? 30) with true in *.
      (* rewrite Heqb in *.
      inversion Heqp.
      break_if.
      congruence.
      entailer!. *)
      admit.
      admit.
  - forward_if True.
    + forward.
      forward.
            admit.
    + forward. entailer!.
    + repeat forward.
      (* loop *)
      admit.
Admitted.

