Require Import Core.Core Lib ErrorWithWriter.
From Coq Require Import String.
From ExtLib.Structures Require Import Monad Monoid MonadWriter.
Require Import ExtLib.Data.Monads.OptionMonad. 

Import MonadNotation.
Import ListNotations.

Open Scope monad.

Section Encoder.

Definition output_stream : Monoid (list byte) :=
{| monoid_plus := @List.app _
 ; monoid_unit := @nil _
 |}.

Record asn_enc_rval : Type := encode {
  encoded : Z ;
}.

Check errW.

Definition errW1 `{ Monoid (list byte) } := @errW string (list byte).
Parameter der_write_tags : TYPE_descriptor -> @errW1 output_stream asn_enc_rval.

(* Typeclasses eauto := 1.*)
Definition bool_prim_encoder (td : TYPE_descriptor) (b : bool) : errW1 asn_enc_rval :=
  let r := if b then (Byte.repr 255) else (Byte.repr 0) in
  der_write_tags td >>= fun x => tell [r] >>= fun _ => ret (encode (1 + encoded x)).

End Encoder.

Section Decoder.

Definition bool_content_decoder len ls : byte :=
  match (filter (fun elem => negb (Byte.eq elem Byte.zero)) 
                (skipn (Z.to_nat len) ls)) with
  | [] => Byte.zero
  | x :: _ => x
  end.

Definition bool_prim_decoder (td : TYPE_descriptor) (ls : list byte) : option (byte) :=
  match ls with
  | [] => None
  | l :: lss => ber_check_tag td ls >>= fun x => 
               if Zlength ls - (tag_consumed x) <? (tag_expected x)
               then None
               else Some (bool_content_decoder (tag_consumed x) ls)
  end.

End Decoder.
