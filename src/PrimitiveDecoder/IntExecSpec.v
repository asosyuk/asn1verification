Require Import ASN1V.Core.Core Core.Notations Lib.Lib Lib.ErrorWithWriter.
From ExtLib.Structures Require Import Monad MonadWriter MonadExc.
From ExtLib.Data Require Import Monads.OptionMonad.

Import MonadNotation.
Import ListNotations.

Open Scope byte.

(* Decoding fails : 
   1) when calloc fails to allocate memory for the output structure sptr (FAIL) SEP spec
   2) if ber_check_tags return FAIL (when?) or MORE (?) - executable spec
   3) if not enough data according to length read (MORE) - executable spec
   4) expected length doesn't fit into size (FAIL) ?
   5) malloc buf allocation fails (FAIL) SEP spec
 *)

Section Encoder.

(* If the contents octets of an integer value encoding
   consist of more than one octet, then the bits of the
   first octet and bit 8 of the second octet:
   a) shall not all be ones; and
   b) shall not all be zero. *)

Fixpoint canonicalize_int (l : list byte) : list byte :=
  match l with
  | nil => nil 
  | x::xs => match xs with
            | nil => l (* If there is only one octet do nothing *)
            | y::ys => (* else do check *)
              if x == 0
              then if y @ 0 (* 1st bit of y is one *)
                   then xs 
                   else canonicalize_int xs 
              else if x == all_one
                   then if y @ 0
                        then canonicalize_int xs
                        else xs
              else l
            end
  end.

Definition int_encoder td (ls : list byte) := let c := canonicalize_int ls in
                                              primitive_encoder td c.
End Encoder.

Section Decoder.

Definition int_decoder := primitive_decoder.

End Decoder.
