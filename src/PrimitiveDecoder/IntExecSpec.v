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

Definition int_decoder (td : TYPE_descriptor) (ls : list byte) : option (byte * Z) :=
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
