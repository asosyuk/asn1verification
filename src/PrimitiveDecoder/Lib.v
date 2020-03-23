From Coq Require Import String.
Require Import Core.Core.
Require Import VST.floyd.proofauto.
Require Import Clight.asn_codecs_prim.
Require Import ExtLib.Structures.Monad.
Require Import ErrorWithWriter.
From ExtLib.Data Require Import List.
From ExtLib.Structures Require Import Monoid.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Import ListNotations.

Existing Class Monoid.
Existing Instance Monoid_list_app.

(* Decoder return type *)
Record asn_dec_rval := rval { consumed : Z }.

(* Encoder return type *)
Record asn_enc_rval : Type := encode {
  encoded : Z ;
}.

Inductive TYPE_descriptor :=
  def { tags : list Z;
        elements : list TYPE_descriptor 
      }.

Record check_tag_r := mk_check_tag_rval { tag_consumed : Z; tag_expected : Z }.

(* The function can return error in 3 cases:
   1) If der_write_tags fails.
   2) If cb fails.
   3) Fail of encoding or decoding with custom error message, to distinguish between them.
*)
(* TODO Maybe rename CustomError constructor to smt like LogicError *)
Inductive Err := HeaderEncodeError 
                 | CBEncodeError
                 | CustomError {T : Type} : T -> Err.

(* Specialized version of errW with custom Error and Log type *)
Definition errW1 := @errW Err (list byte).

(* Writes header octets *)
Parameter der_write_tags : TYPE_descriptor -> errW1 asn_enc_rval.

(* checks the tag, outputs consumed length and expected length *)
Parameter ber_check_tag : TYPE_descriptor -> list byte -> option check_tag_r.

Definition ZeroChar := Byte.repr 48.
  
(* memory representation of abstract types *)
Parameter TYPE_descriptor_rep : TYPE_descriptor
                                -> reptype (Tstruct _asn_TYPE_descriptor_s noattr). 

(* These two will express memory specifications *)

(* on any error write {buf = 0; size = 0},
    else {buf = ls; size = |ls|}*)
Parameter PRIMITIVE_TYPE_rep : option byte
                               -> reptype (Tstruct _ASN__PRIMITIVE_TYPE_s noattr).

(* on error rval c l write {code := c; consumed := l},
   else {code := OK; consumed := |ls| *)
Parameter dec_rval_rep : option byte -> reptype (Tstruct _asn_dec_rval_s noattr).
