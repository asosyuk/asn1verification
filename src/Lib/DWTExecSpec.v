Require Import Core.Core Core.Notations Types Core.Notations List.
Require Import ExtLib.Structures.Monad.

Import ListNotations.
Import MonadNotation.

Inductive DWT_Error := NotBoolean.

(* Writes header octets *)
Definition der_write_tags (td : TYPE_descriptor) : errW1 asn_enc_rval :=
  match decoder_type td with
  | BOOLEAN_t => tell1 (map Byte.repr [1; 1]) >>= fun _ => ret (encode 2)
  | _ => raise (CustomError NotBoolean)
  end.
