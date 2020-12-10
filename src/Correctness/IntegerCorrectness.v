Require Import Core.Core Core.StructNormalizer Lib.VstLib Callback.Dummy
        Int.Exec ErrorWithWriter DWT.VST.Der_write_tags.
Require Import VST.floyd.proofauto.
Require Import Clight.dummy Clight.der_encoder.
Require Import Core.Notations. 
Require Import Int.Exec AbstractSpec Lib Prim.Exec.
Require Import Clight.dummy Clight.asn_codecs_prim Clight.INTEGER Lib.Stdlib
        Clight.ber_tlv_tag Clight.ber_tlv_length.
Require Import Clight.ber_decoder.
Require Import Lib.BCT.Vst  Lib.DWT.VST.Der_write_TL 
         Lib.DWT.VST.Ber_tlv_tag_serialize  Lib.DWT.VST.Ber_tlv_length_serialize
         Lib.BCT.VST.ASN__STACK_OVERFLOW_CHECK Prim.Der_encode_primitive Int.VstEnc.
Require Import VST.floyd.library.

                 (* C <-> EXECUTIVE SPEC *) 
     
Inductive C_to_ESPEC_correctness (f : function) (f_spec : ident * funspec) 
      (aux_fs : list (function * (ident * funspec)))
      (V : varspecs) (G : list (ident * funspec)) : Prop :=
| NoAuxCorr (C : compspecs) : aux_fs = [] -> 
          semax_body V G f f_spec ->
          C_to_ESPEC_correctness f f_spec aux_fs V G
| WithAuxCorr (C : compspecs) : 
    aux_fs <> [] ->
    semax_body V G f f_spec ->
    (* all aux functions (aux_fs) correspond to the aux specs *)
    (forall g g_spec,
         In g aux_fs ->
         g_spec <> f_spec ->
         (exists fs V' G', C_to_ESPEC_correctness (fst g) (snd g) fs V' G')) ->
         C_to_ESPEC_correctness f f_spec aux_fs V G.

                (* ASSUMPTIONS *)

(* Normalizer works correctly *) 
Hypothesis normalizer_correctness: forall comps {CompSpecs : compspecs} V G f f_spec,
    semax_body V G (normalize_function f comps) f_spec ->
    semax_body V G f f_spec.

(* C library functions correspond to our (and VST) specs *)
Parameter f_calloc : function. (* some C implementation of calloc *)
Parameter f_malloc : function. (* some C implementation of malloc *)
Parameter f_memcpy : function. (* some C implementation of memcpy *)
Parameter f___assert_fail : function.
Hypothesis calloc_correctness : exists V G,
    @semax_body V G Vst.CompSpecs
                f_calloc (_calloc, @calloc_spec BCT.Vst.CompSpecs).
Hypothesis malloc_correctness : exists V G, 
    @semax_body V G Vst.CompSpecs
                f_malloc (_malloc, @malloc_spec' Vst.CompSpecs).
Hypothesis memcpy_correctness : exists V G, 
    @semax_body V G Vst.CompSpecs 
                f_memcpy (_memcpy, @memcpy_spec Vst.CompSpecs).
Hypothesis assert_fail_correctness : exists V G,
    @semax_body V G Vst.CompSpecs f___assert_fail
                (___assert_fail, @assert_spec BCT.Vst.CompSpecs).


Require Import Lib.BCT.Vst Clight.ber_decoder Clight.ber_tlv_tag Clight.ber_tlv_length
         Lib.BCT.BFL.Vst Lib.BCT.BFT.Vst Prim.Ber_decode_primitive
         Lib.BCT.VST.ASN__STACK_OVERFLOW_CHECK.

Lemma primitive_decoder_C_to_ESPEC_correctness :
  C_to_ESPEC_correctness f_ber_decode_primitive ber_decode_primitive_spec
                         [(f_ber_check_tags, ber_check_tags_spec);
                          (f_calloc, (ber_decoder._calloc,
                                      @calloc_spec BCT.Vst.CompSpecs));
                          (f_memcpy, 
                           (ber_decoder._memcpy, @memcpy_spec Vst.CompSpecs));
                          (f_malloc, 
                           (ber_decoder._malloc, @malloc_spec' Vst.CompSpecs))]
                          Ber_decode_primitive.Vprog 
                          Ber_decode_primitive.Gprog.
Proof.
  eapply WithAuxCorr with (C := Prim.Ber_decode_primitive.CompSpecs);
    try discriminate.
  - apply (@normalizer_correctness asn_codecs_prim.composites 
                                   Prim.Ber_decode_primitive.CompSpecs).
    eapply ber_decode_primitive_correctness.
  - intros g g_spec INf EQ.
    inversion INf as [EQf | R0 ]; try contradiction; clear INf.
    erewrite <- EQf.
    exists [(f___assert_fail, (ber_decoder.___assert_fail, (@assert_spec BCT.Vst.CompSpecs)));
       (f_ber_fetch_tag, Vst.ber_fetch_tag_spec);
       (f_ber_fetch_length, ber_fetch_len_spec);
       (ber_decoder.f_ASN__STACK_OVERFLOW_CHECK, ASN__STACK_OVERFLOW_CHECK_spec)]. 
    repeat eexists.
    eapply WithAuxCorr with (C := BCT.Vst.CompSpecs).
    + discriminate.
    + eapply (normalizer_correctness ber_decoder.composites).
      apply BCT.Vst.ber_check_tags_correctness.
    + clear.
      intros g g_spec INf EQ.
      inversion INf as [EQf | R];
        [ | inversion R as [L1 | R1];  
            [ erewrite <- L1; clear |
              inversion R1 as [L2 | R2]; 
              [ erewrite <- L2;  clear |
                inversion R2 as [L3 | ]]]]; 
      try contradiction.
      erewrite <- EQf. clear.
      * exists [].
        destruct assert_fail_correctness as [V A]; destruct A as [G A].
        repeat eexists.
        eapply NoAuxCorr with (C := BCT.Vst.CompSpecs). auto.
        unfold fst, snd.
        eapply A.
      * exists [].
        repeat eexists.
        eapply NoAuxCorr with (C := BFT.Vst.CompSpecs). auto.
        unfold fst, snd.
        eapply ber_fetch_tag_correctness.
      * exists [].
        repeat eexists.
        eapply NoAuxCorr with (C := BFL.Vst.CompSpecs). auto.
        unfold fst, snd.
        eapply ber_fetch_len_correctness.
      * erewrite <- L3. clear.
        exists [].
        repeat eexists.
        eapply NoAuxCorr with (C := ASN__STACK_OVERFLOW_CHECK.CompSpecs). auto.
        unfold fst, snd.
        eapply ASN__STACK_OVERFLOW_CHECK_correctness.
    + inversion R0 as [EQf | R]; [  erewrite <- EQf; clear 
                                    | inversion R as [L1 | R1];  [ erewrite <- L1; clear |
                                      inversion R1 as [L2 | R2]; 
                                          [ erewrite <- L2;  clear |
                                            inversion R2]]]; 
      try contradiction.
      * exists [].
        destruct calloc_correctness as [V A]; destruct A as [G A].
        repeat eexists.
        eapply NoAuxCorr with (C := BCT.Vst.CompSpecs). auto.
        unfold fst, snd.
        eapply A.
      *  exists [].
        destruct memcpy_correctness as [V A]; destruct A as [G A].
        repeat eexists.
        eapply NoAuxCorr with (C := BCT.Vst.CompSpecs). auto.
        unfold fst, snd.
        eapply A.
      * exists [].
        destruct malloc_correctness as [V A]; destruct A as [G A].
        repeat eexists.
        eapply NoAuxCorr with (C := BCT.Vst.CompSpecs). auto.
        unfold fst, snd.
        eapply A.
Qed.

Require Import Clight.dummy Clight.asn_codecs_prim Clight.INTEGER Lib.Stdlib
        Clight.ber_tlv_tag Clight.ber_tlv_length.
Require Import Clight.ber_decoder.
Require Import Lib.BCT.Vst  Lib.DWT.VST.Der_write_TL 
         Lib.DWT.VST.Ber_tlv_tag_serialize  Lib.DWT.VST.Ber_tlv_length_serialize
         Lib.BCT.VST.ASN__STACK_OVERFLOW_CHECK Prim.Der_encode_primitive Int.VstEnc.
Require Import VST.floyd.library.

Lemma integer_encoder_C_to_ESPEC_correctness :
  C_to_ESPEC_correctness f_INTEGER_encode_der
                   int_der_encode_spec
                   [(f_der_encode_primitive,
                     Der_encode_primitive.der_primitive_encoder_spec)]
                   Vprog Gprog.
Proof.
  eapply WithAuxCorr with (C := CompSpecs);
    try discriminate.
  - apply (normalizer_correctness composites).
    apply int_der_encode_correctness.
  - intros g g_spec INf EQ.
    inversion INf as [EQf |  ]; try contradiction; clear INf.
    erewrite <- EQf.
    exists [(f_der_write_tags, Der_write_tags.der_write_tags_spec)]. repeat eexists.
      eapply WithAuxCorr with (C := Der_encode_primitive.CompSpecs).
    + discriminate.
    + eapply (normalizer_correctness Der_encode_primitive.composites).
      apply Der_encode_primitive.der_encode_primitive_correctness.
    + clear.
      intros g g_spec INf EQ.
      inversion INf as [EQf |  ]; try contradiction; clear INf.
      erewrite <- EQf. clear.
     exists [(f_der_write_TL,
        Der_write_TL.der_write_TL_spec)]. repeat eexists.
      eapply WithAuxCorr with (C := Der_write_tags.CompSpecs); try discriminate.
      * eapply (normalizer_correctness Der_write_tags.composites).
        eapply Der_write_tags.der_write_tags_correctness.
      * clear.
        intros g g_spec INf EQ.
        inversion INf as [EQf |  ]; try contradiction; clear INf.
        erewrite <- EQf. clear.
        exists [(f_ber_tlv_tag_serialize, 
            Ber_tlv_tag_serialize.ber_tlv_tag_serialize_spec); 
           (f_der_tlv_length_serialize, 
            Ber_tlv_length_serialize.der_tlv_length_serialize_spec);
           (f_dummy, dummy_callback)]. repeat eexists.
        eapply WithAuxCorr with (C := Der_write_TL.CompSpecs) ; try discriminate.
      -- eapply (normalizer_correctness Der_write_TL.composites).
         eapply Der_write_TL.der_write_TL_correctness.
      -- clear.
         intros g g_spec INf EQ.
         inversion INf as [EQf | F]; try contradiction; clear INf;
           try erewrite <- EQf.
         ++ exists []. repeat eexists.
            eapply NoAuxCorr with (C := Ber_tlv_tag_serialize.CompSpecs). auto.
            unfold fst.
            eapply (normalizer_correctness ber_tlv_tag.composites).
            apply ber_tlv_tag_serialize_correct.
         ++ inversion_clear F as [F1 | F2].
            **
            erewrite <- F1.
            simpl.
            exists []. repeat eexists.
            eapply NoAuxCorr with (C := Ber_tlv_length_serialize.CompSpecs). auto.
            eapply (normalizer_correctness ber_tlv_length.composites).
            apply ber_tlv_length_serialize_correct.
            ** inversion_clear F2 as [ F | ]; try contradiction.
               erewrite <- F. 
               exists []. repeat eexists. simpl.
               eapply NoAuxCorr with (C := Dummy.CompSpecs). auto.
               eapply (normalizer_correctness dummy.composites).
               eapply dummy_callback_correctness.
Qed.

                       (* Exec <-> Abstract Spec *)

Lemma ESPEC_to_HSPEC_correctness_int_encoder : forall td struct_len buf_size li ls z,
  decoder_type td = INTEGER_t ->
  int_encoder td struct_len buf_size li [] = inr (ls, z) ->
  DER (PRIM_INTEGER li) (map Byte.repr (map Int.unsigned ls)).
Admitted.

(* Need Exec.der_fetch_tags correctness *)

Lemma ESPEC_to_HSPEC_correctness_int_decoder : forall td ctx size sizeofval sizemax ls li z,
    decoder_type td = INTEGER_t ->
    primitive_decoder td ctx size (sizeof tuint) (Int.max_unsigned) ls = Some (li, z) ->
    BER (PRIM_INTEGER li) ls.
Admitted.

(* Proof needs Exec.ber_check_tags correctness *)

Lemma int_roundtrip : forall td ls struct_len ctx size sizeofval sizemax li z,
    decoder_type td = INTEGER_t ->
    int_encoder td struct_len size li [] = inr (ls, z) ->
    primitive_decoder td ctx size (sizeof tuint) (Int.max_unsigned)
                      (map Byte.repr (map Int.unsigned ls))
    = Some (li, z).
Admitted.
