Require Import Core.Core Core.Notations Core.Tactics Types DWTExecSpec BCTExecSpec.
From ExtLib.Structures Require Import Monad MonadWriter.
From ExtLib.Data Require Import Monads.OptionMonad.

Require Export Types.
Require Export ExtLib.Structures.Monad.
From ExtLib.Data Require Export Monads.OptionMonad List.

Import ListNotations.
Import MonadNotation.

Open Scope monad.

Definition primitive_decoder td ls : option (list byte * Z) :=
    match ls with
    | [] => None
    | _ => ber_check_tags td ls >>=
                        fun x => let c := tag_consumed x in 
                              let e := tag_expected x in 
                              if (Zlength ls - c <? e)
                              then None 
                              else let y := skipn (Z.to_nat c) ls in
                                    Some (y, c + 1)
    end.

(* writes tags, copies ls and outputs the number of encoded bytes *)
Definition primitive_encoder td ls : errW1 asn_enc_rval :=
  der_write_tags td >>= 
                 fun x => tell ls >>= 
                            fun _ => ret (encode (Zlength ls + encoded x)).

Definition ZeroChar := Byte.repr 48.

Definition bool_of_byte (b : byte) := 
  if (b == default_byte)%byte then false else true.
Definition byte_of_bool (b : bool) := Byte.repr (if b then 255 else 0).
Definition int_of_bool (b : bool) := Int.repr (if b then 255 else 0).
