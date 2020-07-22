Require Import ExtLib.Structures.Monad Types.
Require Import Core.Core Core.Notations Core.Tactics.
Require Import Exec.Ber_tlv_tag_serialize_m
        Exec.Ber_tlv_length_serialize_m.
Require Import VST.floyd.sublist.

Open Scope Z.

Definition der_write_TL_m tag len size constructed : errW1 asn_enc_rval := 
 pass
 ('(encode t, tl) <- listen (tag_serialize tag (Int.repr size)) ;;
  '(encode l, ll) <- listen (length_serialize len (Int.repr (size - t))) ;;
  if (32 <? t) || (32 <? t + l) 
  then raise (CustomError DWT_Error)
  else if negb (constructed == 0%int) 
       then ret (encode (t + l), id) 
       else ret (encode (t + l), fun ls =>
                             (upd_Znth 0 ls (Znth 0 ls or (Int.repr 32))%int))).
