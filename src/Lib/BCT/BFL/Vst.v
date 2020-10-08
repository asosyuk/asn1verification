Require Import Core.Core Core.StructNormalizer VstLib.
Require Import VST.floyd.proofauto.
Require Import BFL.Exec.
Require Import Clight.ber_tlv_length.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Section Ber_fetch_len.

Definition ber_fetch_len_spec : ident * funspec :=
  DECLARE _ber_fetch_length
    WITH c : Z,  buf_p : val,
         size : Z, data : list Z,
         res_ptr : val
    PRE [tint, tptr tvoid, tuint, tptr tint]
      PROP (isptr buf_p;
            isptr res_ptr;
            Zlength data = size;
            0 <= size <= Int.max_unsigned)
      PARAMS (Vint (Int.repr c); buf_p; Vint (Int.repr size); res_ptr)
      GLOBALS ()
      SEP (data_at Tsh (tarray tuchar (Zlength data)) 
                   (map Vubyte (map Byte.repr data)) buf_p;
           data_at_ Tsh tint res_ptr)
    POST [tint]
      let r := ber_fetch_len data c 0 size (sizeof tuint) 1 in
      PROP ()
      LOCAL (temp ret_temp (Vint (Int.repr (fst r))))
      SEP (data_at Tsh (tarray tuchar (Zlength data)) 
                   (map Vubyte (map Byte.repr data)) buf_p;
           data_at Tsh tint (Vubyte (Byte.repr (snd r))) res_ptr).

Definition Gprog := ltac:(with_library prog [ber_fetch_len_spec]).

Theorem ber_fetch_len : semax_body Vprog Gprog 
                                          (normalize_function f_ber_fetch_length
                                                              composites) 
                                          ber_fetch_len_spec.
Proof.
Admitted.

End Ber_fetch_len.
