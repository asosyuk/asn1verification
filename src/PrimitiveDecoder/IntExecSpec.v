Require Import Core.Core Core.Notations Lib ErrorWithWriter.
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

Definition remove_leading_zeros__t : forall (l : list Z), (l <> nil) -> list Z.
Proof.
  intros.
  destruct l.
  contradiction.
  assumption.
Defined.

Print remove_leading_zeros__t.

(* TODO Add non-empty proof to get rid of nil *)
Fixpoint remove_leading_zeros (l : list Z) : list Z := 
  match l with
  | 0%Z::tl => remove_leading_zeros tl
  | x::tl => x::tl
  | nil => nil
  end.

Inductive IntEncError := NoBufferError.

(* TODO Get rid of this context definitions *)
Context {MT : Monoid.Monoid (list Z)}.
Context {MW : MonadWriter MT errW1}.

(* Fixpoint canonicalize_int (l : list Z) : list Z :=
  match l with
  | 0%Z::x::xs => nil
  | nil => nil
  end. *)

Definition int_encoder (td : TYPE_descriptor) (i : list Z) : errW1 asn_enc_rval :=
  match i with
  | nil => raise (CustomError NoBufferError)
  | _ => let rlz := remove_leading_zeros i in 
        der_write_tags td >>= 
                       fun x => tell rlz >>= 
                                  fun _ => ret (encode (1 + encoded x))
  end.

End Encoder.

Section Decoder.

Definition int_decoder := primitive_decoder.

End Decoder.
