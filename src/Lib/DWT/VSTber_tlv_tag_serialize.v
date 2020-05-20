Require Import Core.Core Core.StructNormalizer VstLib DWT.Exec 
        ErrorWithWriter.
Require Import VST.floyd.proofauto.
Require Import Clight.ber_tlv_tag.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Definition ber_tlv_tag_serialize (tag size : Z) : list byte * Z :=
  let tclass := Z.land tag 3 in 
  let tval := Z.shiftr tag 2 in
  if tval <=? 30 then (* Encoded in 1 octet *)
    if negb (size =? 0) 
    then ([Byte.repr (Z.lor (Z.shiftr tclass 6) tval)], 1)
    else ([], 1)
  else if negb (size =? 0) (* Encoded in > 1 octet *) 
       then let buf1 := (Z.lor (Z.shiftr tclass 6) 31) in
            let size' := size - 1 in 
            ([], 1)
       else ([], 1).
  
Definition ber_tlv_tag_serialize_spec : ident * funspec :=
  DECLARE _ber_tlv_tag_serialize
  WITH tag: Z, bufp : val, size : Z
  PRE[tuint, tptr tvoid, tuint]
    PROP()
    PARAMS(Vint (Int.repr tag); bufp; Vint (Int.repr size))
    GLOBALS()
    SEP(data_at_ Tsh tvoid bufp)
    POST[tuint]
    let (ls, s) := ber_tlv_tag_serialize tag size in
      PROP()
      LOCAL(temp ret_temp (Vint (Int.repr s)))
      SEP(data_at Tsh (tarray tuint (Zlength ls)) (map Vubyte ls) bufp).
