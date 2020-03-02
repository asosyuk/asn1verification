From Coq Require Import String.
Require Import Core.Core Lib.
Require Import ExtLib.Structures.Monad.
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

(* skip len bytes and add '\0' at the end *)
Definition prim_content_decoder len ls :=
   skipn (Z.to_nat len) ls ++ [ZeroChar].

(*
Definition int_prim_decoder (td : TYPE_descriptor) (ls : list byte) : err (list byte) := 
  match ls with 
  | [] => inl (rval FAIL 0)
  | h :: tl => x <- ber_check_tag td ls ;; 
              if Zlength ls - (tag_consumed x) <? (tag_expected x)
              then inl (rval MORE 0)
              else inr (prim_content_decoder (tag_consumed x) ls)
  end.
*)
