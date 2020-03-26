Require Import ASN1V.Core.Core Core.Notations Lib ErrorWithWriter.
From ExtLib.Structures Require Import Monad MonadWriter MonadExc.
From ExtLib.Data Require Import Monads.OptionMonad.

Import MonadNotation.
Import ListNotations.

Open Scope monad.

(* Decoding fails : 
   1) when calloc fails to allocate memory for the output structure sptr (FAIL) SEP spec
   2) if ber_check_tags return FAIL (when?) or MORE (?) - executable spec
   3) if not enough data according to length read (MORE) - executable spec
   4) expected length doesn't fit into size (FAIL) ?
   5) malloc buf allocation fails (FAIL) SEP spec
 *)

Section Encoder.

(* TODO Get rid of this context definitions *)
Context {MT : Monoid.Monoid (list Z)}.
Context {MW : MonadWriter MT errW1}.

Fixpoint canonicalize_int (l : list byte) : list byte :=
  match l with
  | nil => nil
  | x::xs => match xs with
            | nil => l
            | y::ys => 
              if (x == Byte.repr 0)%byte 
              then if (Byte.and y (Byte.repr 128) == 0)%byte 
                   then canonicalize_int xs else xs 
              else if (x == Byte.repr 255)%byte 
                   then if (negb (Byte.and y (Byte.repr 128) == 0))%byte 
                        then canonicalize_int xs else xs
                   else l
            end
  end.

Definition int_encoder (td : TYPE_descriptor) (i : list Z) : errW1 asn_enc_rval :=
  let ib := map (Byte.repr) i in
  let c := canonicalize_int ib in primitive_encoder td c.

End Encoder.

Section Decoder.

Definition int_decoder := primitive_decoder.

End Decoder.
