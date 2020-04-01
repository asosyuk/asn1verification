Require Import Core.Core Core.Notations Core.Tactics Types.
From ExtLib.Structures Require Import Monad MonadWriter Monoid.
From ExtLib.Data Require Import Monads.OptionMonad List.

Require Export Types.

Import ListNotations.
Import MonadNotation.

Open Scope monad.

Existing Class Monoid.
Existing Instance Monoid_list_app.

(* Writes header octets *)
Parameter der_write_tags : TYPE_descriptor -> errW1 asn_enc_rval.

(* checks the tag, outputs consumed length and expected length *)
Parameter ber_check_tag : TYPE_descriptor -> list byte -> option check_tag_r.

Definition primitive_decoder td ls : option (list byte * Z) :=
    match ls with
    | [] => None
    | _ => ber_check_tag td ls >>=
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
