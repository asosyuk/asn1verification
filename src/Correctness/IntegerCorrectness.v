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
         Lib.BCT.VST.ASN__STACK_OVERFLOW_CHECK Int.VstEnc.

                 (* C <-> executive spec *) 
     
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

(* We assume that normalizer works correctly *) 
Hypothesis normalizer_correctness: forall comps {CompSpecs : compspecs} V G f f_spec,
    semax_body V G (normalize_function f comps) f_spec ->
    semax_body V G f f_spec.
  
Lemma integer_encoder_C_to_ESPEC_correctness :
  C_to_ESPEC_correctness f_INTEGER_encode_der
                   int_der_encode_spec
                   [(f_der_encode_primitive,
                     Der_encode_primitive.der_primitive_encoder_spec)]
                   Vprog Gprog.
Proof.
  eapply WithAuxCorr;
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
    primitive_decoder td ctx size sizeofval sizemax ls = Some (li, z) ->
    BER (PRIM_INTEGER li) ls.
Admitted.

(* Proof needs Exec.ber_check_tags correctness *)

Lemma int_roundtrip : forall td ls struct_len ctx size sizeofval sizemax li z,
    decoder_type td = INTEGER_t ->
    int_encoder td struct_len size li [] = inr (ls, z) ->
    primitive_decoder td ctx size sizeofval sizemax
                      (map Byte.repr (map Int.unsigned ls))
    = Some (li, z).
Admitted.
