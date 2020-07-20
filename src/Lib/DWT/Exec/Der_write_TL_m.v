Require Import ExtLib.Structures.Monad Types.
Require Import Core.Core Core.Notations Core.Tactics.
Require Import Exec.Ber_tlv_tag_serialize_m
        Exec.Ber_tlv_length_serialize.
Require Import VST.floyd.sublist.

Open Scope Z.

Definition der_write_TL_m tag len size constructed : errW1 asn_enc_rval := 
  let (tl, t) := tag_serialize tag (Int.repr size) in
  let (ll, l) := length_serialize len (Int.repr (size - t)) in
  let ls := if negb (constructed == 0%int) 
            then tl ++ ll 
            else (upd_Znth 0 tl (Znth 0 tl or (Int.repr 32))%int) ++ ll in
  if ((t =? -1) || (32 <? t))%bool 
  then raise (CustomError DWT_Error)
  else if l =? -1 
       then raise (CustomError DWT_Error)
       else let s := l + t in
            if 32 <? s 
            then raise (CustomError DWT_Error)
            else tell1 ls >>= fun _ => ret (encode s).
