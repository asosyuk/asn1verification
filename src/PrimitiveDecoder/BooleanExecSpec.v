Require Import Core.Core Lib.
From Coq Require Import String.
Require Import ExtLib.Data.Monads.WriterMonad ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadWriter.
Require Import ExtLib.Structures.Monoid.

Import MonadNotation.
Import ListNotations.

Open Scope monad.

Section Encoder.

Variable m : Type -> Type.

Definition output_stream : Monoid (list byte) :=
{| monoid_plus := @List.app _
 ; monoid_unit := @nil _
 |}.

Context {Monad_m : Monad m}.
Context {Writer_m : MonadWriter output_stream m}.

Parameter der_write_tags : TYPE_descriptor -> m Type.

Definition bool_prim_encoder' (td : TYPE_descriptor) (b : bool) :=
  (der_write_tags td) >>= 
    (listen (ret (if b then (Byte.repr 255) else (Byte.repr 0)))).

Definition bool_prim_encoder (td : TYPE_descriptor) (b : bool) :option (list byte) :=
  match der_write_tags td with | None => None
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
