Require Import Core.Core.
Import ListNotations.
From Coq Require Import String.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Structures.Monad.

Inductive dec_rval_error := FAIL | MORE.

Record dec_rval := rval { code : dec_rval_error;
                          consumed : Z }.

Definition err T := sum dec_rval T.

Instance Monad_err : Monad err := Monad_either dec_rval.
Instance Exception_err : MonadExc dec_rval err := Exception_either dec_rval.

Inductive TYPE_descriptor :=
  def { tags : list Z;
        elements : list TYPE_descriptor 
      }.

(* checks the tag, outputs consumed length and expected length *)
Parameter ber_check_tag : TYPE_descriptor -> list byte -> err (Z*Z).

Definition ZeroChar := Byte.repr 48.

Import MonadNotation.
Open Scope monad.

(* Decoding fails : 
   1) when calloc fails to allocate memory for the output structure sptr (FAIL) SEP spec
   2) if ber_check_tags return FAIL (when?) or MORE (?) - executable spec
   3) if not enough data according to length read (MORE) - executable spec
   4) expected length doesn't fit into size (FAIL) ?
   5) malloc buf allocation fails (FAIL) SEP spec
 *)

(* skip len bytes and add '\0' at the end *)
Definition prim_content_decoder len ls :=
   skipn (Z.to_nat len) 
          ls ++ [ZeroChar].

Definition prim_decoder (td : TYPE_descriptor) (ls : list byte) : err (list byte) := 
  match ls with 
  | [] => inl (rval FAIL 0)
  | h :: tl => x <- ber_check_tag td ls 
                ;; if Zlength ls - (fst x) <? (snd x)
                   then inl (rval MORE 0)
                   else inr (prim_content_decoder (snd x) ls)
  end.


