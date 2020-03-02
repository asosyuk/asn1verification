Require Import Core.Core Lib ErrorWithWriter.
From Coq Require Import String.
From ExtLib.Structures Require Import Monad Monoid MonadWriter.

Import MonadNotation.
Import ListNotations.

Open Scope monad.

Section Encoder.

Definition output_stream : Monoid (list byte) :=
{| monoid_plus := @List.app _
 ; monoid_unit := @nil _
 |}.

Variable m : Type -> Type.

Context {Monad_m : Monad m}.
Context {Writer_m : MonadWriter output_stream m}.

Record asn_enc_rval : Type := encode {
  encoded : Z ;
}.

Parameter der_write_tags : TYPE_descriptor -> m asn_enc_rval.

Definition bool_prim_encoder' (td : TYPE_descriptor) (b : bool) : m asn_enc_rval :=
  let r := if b then (Byte.repr 255) else (Byte.repr 0) in
  (der_write_tags td) >>= fun x => tell [r] >>= fun _ => ret (encode (1 + encoded x)).

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
