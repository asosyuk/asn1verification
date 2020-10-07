Require Import Core.Core Core.StructNormalizer VstLib.
Require Import VST.floyd.proofauto.
Require Import BFL.Exec.
Require Import Clight.ber_tlv_length.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Section Ber_fetch_len.

Definition ber_fetch_len_spec : ident * funspec :=
  DECLARE _ber_fetch_length
    WITH size : Z, data : list Z,
         isc : Z, buf_b : block, buf_ofs : ptrofs, res_v : Z, res_ptr : val
    PRE [tint, tptr tvoid, tuint, tptr tint]
      PROP (isptr res_ptr;
            Zlength data = size;
            0 <= size <= Int.max_unsigned;
            Int.signed (Int.repr size) <= Int.max_signed)
      PARAMS (Vint (Int.repr isc); Vptr buf_b buf_ofs; Vint (Int.repr size); res_ptr)
      GLOBALS ()
      SEP (data_at Tsh (tarray tuchar (Zlength data)) 
                   (map (fun v => Vubyte (Byte.repr v)) data) (Vptr buf_b buf_ofs);
           data_at Tsh tuint (Vubyte (Byte.repr res_v)) res_ptr;
           valid_pointer res_ptr)
    POST [tint]
      let r := ber_fetch_len data isc res_v size (sizeof tuint) 1 in
      PROP ()
      LOCAL (temp ret_temp (Vint (Int.repr (fst r))))
      SEP (data_at Tsh (tarray tuchar (Zlength data)) 
                   (map (fun v => Vubyte (Byte.repr v)) data) (Vptr buf_b buf_ofs);
           data_at Tsh tuint (Vubyte (Byte.repr (snd r))) res_ptr;
           valid_pointer res_ptr).

Definition Gprog := ltac:(with_library prog [ber_fetch_len_spec]).

Theorem ber_fetch_len : semax_body Vprog Gprog 
                                          (normalize_function f_ber_fetch_length
                                                              composites) 
                                          ber_fetch_len_spec.
Proof.
Admitted.

End Ber_fetch_len.
