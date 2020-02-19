Require Import Core.Core Lib.
Import ListNotations.
From Coq Require Import String.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Structures.Monad.
Import MonadNotation.
Open Scope monad.

Section Encoder.

Parameter der_write_tags : TYPE_descriptor -> option (list byte).

Definition bool_prim_encoder (td : TYPE_descriptor) (b : bool) : option (list byte) :=
  match der_write_tags td with
  | None => None
  | Some header => Some (if b 
                  then cons (Byte.repr 255) header
                  else cons (Byte.repr 0) header)
  end.

End Encoder.

Section Decoder.

Definition bool_content_decoder len ls :=
  match (filter (fun elem => negb (Byte.eq elem Byte.zero)) 
                (skipn (Z.to_nat len) ls)) with
  | [] => Byte.zero
  | x :: _ => x
  end.

Definition bool_prim_decoder (td : TYPE_descriptor) (ls : list byte) : option byte :=
  match ls with
  | [] => None
  | l :: lss => x <- ber_check_tag td ls ;;
               if Zlength ls - (tag_consumed x) <? (tag_expected x)
               then None
               else Some (bool_content_decoder (tag_consumed x) ls)
  end.

End Decoder.
