Require Import Core.Core Core.Notations Lib ErrorWithWriter.
From Coq Require Import String.
From ExtLib.Structures Require Import Monad Monoid MonadWriter.
Require Import ExtLib.Data.Monads.OptionMonad. 

Import MonadNotation.
Import ListNotations.

Open Scope monad.

(* Section Encoder.

Definition output_stream : Monoid (list byte) :=
{| monoid_plus := @List.app _
 ; monoid_unit := @nil _
 |}.

Record asn_enc_rval : Type := encode {
  encoded : Z ;
}.

Definition errW1 `{ Monoid (list byte) } := @errW string (list byte).
Parameter der_write_tags : TYPE_descriptor -> @errW1 output_stream asn_enc_rval.

(* Typeclasses eauto := 1.*)

Definition Writer_errW1 := @Writer_errW string (list byte). output_stream.

Definition tellW1 := @tell (list byte) output_stream.

Definition bool_prim_encoder (td : TYPE_descriptor) (b : bool) : errW1 asn_enc_rval :=
  let r := if b then (Byte.repr 255) else (Byte.repr 0) in
  der_write_tags td >>= fun x => tell [r] >>= fun _ => ret (encode (1 + encoded x)).

End Encoder. *)

Section Decoder.

  Definition bool_decoder (td : TYPE_descriptor) (ls : list byte) : option (byte * Z) :=
    match ls with
    | [] => None
    | _ => ber_check_tag td ls >>=
                        fun x => let c := tag_consumed x in
                               let e := tag_expected x in
                               if (Zlength ls - c <? e) || negb (e =? 1)
                               then None
                               else (hd_error (skipn (Z.to_nat c) ls)) 
                                      >>= fun y => Some (y, c + 1)
    end.

End Decoder.
