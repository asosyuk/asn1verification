Require Import Core.Core Core.StructNormalizer VstLib.
Require Import VST.floyd.proofauto.
Require Import BFT.Exec.
Require Import Clight.ber_tlv_tag.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
  
Open Scope Z.

Section Ber_fetch_tag.

Definition ber_fetch_tag_spec : ident * funspec :=
  DECLARE _ber_fetch_tag
    WITH ptr_b : block, ptr_ofs : ptrofs, ptr_v : list Z, size : Z, 
         tag_p : val
    PRE [tptr tvoid, tuint, tptr tuint]
      PROP (0 <= size <= Int.max_unsigned;
           (* Zlength ptr_v = size; *)
            Forall (fun x => 0 <= x <= Byte.max_unsigned) ptr_v;
            Ptrofs.unsigned ptr_ofs + (Zlength ptr_v) < Ptrofs.modulus;
           (* 0 <= tag_v <= Int.max_unsigned; *)
            isptr tag_p)
      PARAMS ((Vptr ptr_b ptr_ofs); Vint (Int.repr size); tag_p)
      GLOBALS ()
      SEP (data_at Tsh (tarray tuchar (Zlength ptr_v)) 
                   (map Vubyte (map Byte.repr ptr_v)) (Vptr ptr_b ptr_ofs);
           data_at_ Tsh tuint tag_p)
    POST [tint]
      let r := ber_fetch_tags ptr_v size 0 (sizeof tuint) in
      PROP ()
      LOCAL (temp ret_temp (Vint (Int.repr (fst r))))
      SEP (data_at Tsh (tarray tuchar (Zlength ptr_v)) 
                   (map Vubyte (map Byte.repr ptr_v)) (Vptr ptr_b ptr_ofs);
           data_at Tsh tuint (Vubyte (Byte.repr (snd r))) tag_p).

Definition Gprog := ltac:(with_library prog [ber_fetch_tag_spec]).

Theorem ber_fetch_tag : semax_body Vprog Gprog 
                                   (normalize_function f_ber_fetch_tag composites) 
                                   ber_fetch_tag_spec.
Proof.
Admitted.

End Ber_fetch_tag.

