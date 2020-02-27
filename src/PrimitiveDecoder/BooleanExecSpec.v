Require Import Core.Core Lib.
From Coq Require Import String.
Require Import ExtLib.Data.Monads.WriterMonad ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadWriter.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Structures.MonadExc.

Import MonadNotation.
Import ListNotations.

Open Scope monad.

Definition output_stream : Monoid (list byte) :=
{| monoid_plus := @List.app _
 ; monoid_unit := @nil _
 |}.

Section Error.

Variable Wr : Type.

Definition errW A := Wr -> string + (Wr * A).

Global Instance errW_Monad : Monad errW := {
  ret := fun _ x => fun w => inr (w, x) ;
  bind := fun _ _ m f => fun w => match m w with
                            | inl v => inl v
                            | inr (w', x) => f x w'
                            end
}.

Global Instance errW_Exception : MonadExc string errW := {
  raise := fun _ v => fun w => inl v ;
  catch := fun _ c h => fun w => match c w with
                           | inl v => h v w
                           | inr x => inr x
                           end
}.

Global Instance errW_Writer : MonadWriter (Monoid Wr) errW := {
  tell := fun w => fun w' => inr (monoid_plus w' w, tt) ;
  listen := fun _ f => f >>= 
  tell : T -> m unit ;
  listen : forall A : Type, m A -> m (A * T) ;
  pass : forall A : Type, m (A * (T -> T)) -> m A ;
}.

End Section.

Section Encoder.

Variable m : Type -> Type.

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
