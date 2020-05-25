Require Import Core.Core  Core.VstTactics Core.StructNormalizer VstLib DWT.Exec 
        ErrorWithWriter.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_tlv_tag ExecBer_tlv_tag_serialize.
Require Import Core.Notations.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

(* Open Scope Z.

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
        else data_at Tsh (tarray tuint buf_size)
                     (map Vubyte ls ++
                          sublist (len ls) buf_size 
                          (default_val (tarray tuint (buf_size - len ls))))
                     bufp).

Definition Gprog := ltac:(with_library prog [ber_tlv_tag_serialize_spec]).

Theorem ber_tlv_tag_serialize_correct : 
  semax_body Vprog Gprog (normalize_function f_ber_tlv_tag_serialize composites)
             ber_tlv_tag_serialize_spec.
Proof.
  start_function.
  repeat forward.
  forward_if.
  - forward_if (
       PROP()
       LOCAL()
       SEP(if eq_dec size 0 
           then data_at_ Tsh (tarray tuchar buf_size) bufp 
           else (data_at Tsh (tarray tuchar buf_size)
    (upd_Znth 0 (default_val (tarray tuchar buf_size))
       (Vint
          (Int.zero_ext 8
             (Int.or (Int.shl 
                        (Int.repr (tag & 3)) (Int.repr 6)) 
                     (Int.repr tag >> Int.repr 2)%int))))
    bufp))).
    + forward. 
      rewrite_if_b. entailer!.
    + forward. entailer!. 
      assert (Int.unsigned (Int.repr size) = Int.unsigned (Int.repr 0))
             by (f_equal; auto).
      repeat rewrite Int.unsigned_repr_eq in *.
      do 2 rewrite Zmod_small in *.
      rewrite_if_b.
      entailer!.
      all: rep_omega.
    + unfold POSTCONDITION.
      unfold abbreviate. 
      break_let.
      forward.
      break_if.
      *  unfold ber_tlv_tag_serialize in *.
         replace (Z.shiftr tag 2 <=? 30) with true in *.
         rewrite_if_b.
         inversion Heqp.
         rewrite_if_b.
         entailer!.
         admit.
      * unfold ber_tlv_tag_serialize in *.
        replace (Z.shiftr tag 2 <=? 30) with true in *.
        rewrite_if_b.
        inversion Heqp.
        assert ([Byte.repr (2 * (2 * (2 * (2 * (2 * (2 * (tag & 3)))))) or (tag >> 2))] <> [])
               by congruence.
        rewrite_if_b.
        entailer!. 
        unfold upd_Znth in *.
        break_if.
        entailer!.
        admit.
        assert (buf_size = 0) as E by admit.
        rewrite E.
        entailer!.
        admit.
  - forward_if True.
    + forward.
      forward.
            admit.
    + forward. entailer!.
    + repeat forward.
      (* loop *)
      admit.
Admitted. *)

Open Scope IntScope.

Definition ber_tlv_tag_serialize_spec' : ident * funspec :=
  DECLARE _ber_tlv_tag_serialize
  WITH tag: int, bufp : val, size : int, buf_size : Z
  PRE[tuint, tptr tvoid, tuint]
    PROP((32 <= buf_size)%Z)
    PARAMS(Vint tag; bufp; Vint size)
    GLOBALS()
    SEP(data_at_ Tsh (tarray tuchar buf_size) bufp)
  POST[tuint]
    let (ls, z) := ber_tlv_tag_serialize' tag size in
    PROP()
    LOCAL(temp ret_temp (Vint z))
    SEP(if eq_dec ls [] 
        then data_at_ Tsh (tarray tuchar buf_size) bufp 
        else data_at Tsh (tarray tuchar buf_size)
                     (map (fun x => Vint (Int.zero_ext 8 x)) ls ++
                          sublist (len ls) buf_size 
                          (default_val (tarray tuchar buf_size)))
                     bufp). 

Definition Gprog' := ltac:(with_library prog [ber_tlv_tag_serialize_spec']).

Arguments valid_pointer p : simpl never.

Open Scope Z.

Proposition split_non_empty_list (cs : compspecs) i ls' ls sh b ofs:
      ls = i::ls'  -> Ptrofs.unsigned ofs + Zlength ls < Ptrofs.modulus -> 
      data_at sh (tarray tuchar (Zlength ls)) (map Vbyte ls) (Vptr b ofs) =
      (data_at sh tuchar (Vbyte i) (Vptr b ofs) *
      data_at sh (tarray tuchar (Zlength ls')) (map Vbyte ls')
              (Vptr b (Ptrofs.add ofs Ptrofs.one)))%logic.
Proof.
  intros LEN MOD.
  rewrite LEN.
  replace (i::ls') with ([i] ++ ls') by reflexivity.
  rewrite map_app. 
  rewrite split2_data_at_Tarray_app with (mid := 1).
  assert (map Vbyte [i] = [Vbyte i]) as T by reflexivity.
  pose proof data_at_singleton_array_eq sh tuchar (Vbyte i) 
       (map Vbyte [i]) (Vptr b ofs) T as T1; rewrite T1; clear T T1.

  assert (Vptr b (Ptrofs.add ofs Ptrofs.one) =
          field_address0 (tarray tuchar (Zlength (app [i] ls'))) [ArraySubsc 1]
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

Open Scope IntScope.

Theorem ber_tlv_tag_serialize_correct' : 
  semax_body Vprog Gprog' (normalize_function f_ber_tlv_tag_serialize composites)
             ber_tlv_tag_serialize_spec'.
Proof.
  start_function.
  repeat forward.
  forward_if.
  assert (((tag >> Int.repr 2) <=u Int.repr 30) = true) as C.
  { unfold Int.ltu.
    break_if;
    autorewrite with norm in *; try nia.
    auto.  }
  - forward_if (
       PROP()
       LOCAL()
       SEP(if eq_dec size 0 
           then data_at_ Tsh (tarray tuchar buf_size) bufp 
           else (data_at Tsh (tarray tuchar buf_size)
    (upd_Znth 0 (default_val (tarray tuchar buf_size))
       (Vint
          (Int.zero_ext 8
             (Int.or (Int.shl 
                        ((tag & Int.repr 3)) (Int.repr 6)) 
                     (tag >> Int.repr 2)%int)))) bufp))).
    + forward. 
      rewrite_if_b. entailer!.
    + forward.
      rewrite_if_b.
      entailer!.
    + unfold POSTCONDITION.
      unfold abbreviate. 
      break_let.
      forward.
      break_if; unfold ber_tlv_tag_serialize' in *; rewrite C in *;
        rewrite_if_b.
      * inversion Heqp.
        rewrite_if_b.
        entailer!.               
      * inversion Heqp.
        rewrite if_false by congruence.
        erewrite upd_Znth_unfold.
        replace (len (default_val (tarray tuchar buf_size))) with buf_size.
                entailer!.
        all: unfold default_val;
        simpl;
        erewrite Zlength_list_repeat;
        try nia; auto.
  - (* 30 < tag *)
   forward_if (
       PROP()
       LOCAL(if eq_dec size 0 
             then temp _buf__1 bufp
             else temp _buf__1 (offset_val 1 bufp)  ;
             if eq_dec size 0 
             then temp _size (Vint size)
             else temp _size (Vint (size - 1)))
       SEP(if eq_dec size 0 
           then data_at_ Tsh (tarray tuchar buf_size) bufp 
           else (data_at Tsh (tarray tuchar buf_size)
    (upd_Znth 0 (default_val (tarray tuchar buf_size))
       (Vint
          (Int.zero_ext 8
             (Int.or (Int.shl 
                        ((tag & Int.repr 3)) (Int.repr 6)) 
                     (Int.repr 31))))) bufp))).
    + unfold tarray. 
      erewrite split2_data_at__Tarray_tuchar with (n1 := 1%Z).
      replace (data_at_ Tsh (Tarray tuchar 1 noattr) bufp) 
        with (data_at_ Tsh tuchar bufp).
      Intros.
      repeat forward.
      repeat rewrite_if_b.
      erewrite upd_Znth_unfold.
      replace (len (default_val (tarray tuchar buf_size))) with buf_size.
                entailer!.
      unfold tarray.
      erewrite split2_data_at_Tarray_tuchar with (n1 := 1%Z).
      autorewrite with sublist.
      entailer!.
      admit.
      all: try nia;
        unfold default_val;
        simpl;
        try erewrite Zlength_list_repeat;
        try nia; auto.
      admit.
      admit.
      admit.
      admit.
    + forward. entailer!.
    + repeat forward.
      (* loop *)
      admit.
Admitted.
