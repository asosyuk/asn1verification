Require Import Core.Core Core.StructNormalizer VstLib DWT.Exec 
        ErrorWithWriter.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_tlv_tag ExecBer_tlv_tag_serialize.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Definition ber_tlv_tag_serialize_spec : ident * funspec :=
  DECLARE _ber_tlv_tag_serialize
  WITH tag: Z, bufp : val, size : Z
  PRE[tuint, tptr tvoid, tuint]
    PROP()
    PARAMS(Vint (Int.repr tag); bufp; Vint (Int.repr size))
    GLOBALS()
    SEP(data_at_ Tsh tvoid bufp)
    POST[tuint]
    let (ls, z) := ber_tlv_tag_serialize tag size in
      PROP()
      LOCAL(temp ret_temp (Vint (Int.repr z)))
      SEP(data_at Tsh (tarray tuint (Zlength ls)) (map Vubyte ls) bufp).
