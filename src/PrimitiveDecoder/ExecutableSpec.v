Require Import Core.Core Core.Notations.
Import ListNotations.
From Coq Require Import String.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Structures.Monad.

Inductive dec_rval_error := FAIL | MORE.

Record dec_rval := rval { error_code : dec_rval_error;
                          consumed : Z }.

Definition err T := sum dec_rval T.

Instance Monad_err : Monad err := Monad_either dec_rval.
Instance Exception_err : MonadExc dec_rval err := Exception_either dec_rval.

Inductive asn_type := BOOLEAN_t | INTEGER_t | SEQUENCE_t.

Inductive TYPE_descriptor :=
  def { tags : list Z;
        type : asn_type;
        elements : list TYPE_descriptor 
      }.

Record check_tag_r := mk_check_tag_rval { tag_consumed : Z; tag_expected : Z }.

(* checks the tag, outputs consumed length and expected length *)
Parameter ber_check_tag : TYPE_descriptor -> list byte -> err check_tag_r.

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
   skipn (Z.to_nat len) ls ++ [ZeroChar].

Definition int_prim_decoder (td : TYPE_descriptor) (ls : list byte) : err (list byte) := 
  match ls with 
  | [] => inl (rval FAIL 0)
  | h :: tl => x <- ber_check_tag td ls ;; 
              if Zlength ls - (tag_consumed x) <? (tag_expected x)
              then inl (rval MORE 0)
              else inr (prim_content_decoder (tag_consumed x) ls)
  end.


Definition bool_content_decoder len ls :=
  match (filter (fun elem => negb (Byte.eq elem Byte.zero)) 
                (skipn (Z.to_nat len) ls)) with
  | [] => Byte.zero
  | x :: _ => x
  end.

Definition bool_prim_decoder (td : TYPE_descriptor) (ls : list byte) : err byte :=
  match ls with
  | [] => inl (rval FAIL 0)
  | l :: lss => x <- ber_check_tag td ls ;;
               if Zlength ls - (tag_consumed x) <? (tag_expected x)
               then inl (rval MORE 0)
               else inr (bool_content_decoder (tag_consumed x) ls)
  end.

(* writes tags and length: tag specified in td, length is always one *)

Parameter der_write_tag : TYPE_descriptor -> list byte.

Definition bool_prim_encoder (td : TYPE_descriptor) (b : int) : list byte :=
  der_write_tag td ++ [Byte.one] ++ [if (b == 0)%int then Byte.zero else Byte.one].

                