Require Import Core.Core Core.Tactics Core.VstTactics Core.StructNormalizer
        VstLib ErrorWithWriter BCT.Exec.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_tlv_tag.
Require Import VST.ASN__STACK_OVERFLOW_CHECK.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Definition ber_fetch_tag_spec : ident * funspec :=
  DECLARE _ber_fetch_tag
    WITH (* Codec context pointer *) 
         tag_r_p : val, size : Z, ptr : val 
    PRE [(tptr tvoid), tuint, (tptr tuint)]
      PROP ()
      PARAMS (tag_r_p; (Vint (Int.repr size)); ptr)
      GLOBALS ()
      SEP ()
    POST [tint]
      PROP ()
      LOCAL (temp ret_temp (Vint (Int.repr 1)))
      SEP ().

