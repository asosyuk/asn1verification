Require Import Core.Core.
Import ListNotations.
From Coq Require Import String.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Structures.Monad.
Require Import VST.floyd.proofauto.
Require Import Clight.asn_codecs_prim.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Record dec_rval := rval { consumed : Z }.

Inductive TYPE_descriptor :=
  def { tags : list Z;
        elements : list TYPE_descriptor 
      }.

Record check_tag_r := mk_check_tag_rval { tag_consumed : Z; tag_expected : Z }.

(* checks the tag, outputs consumed length and expected length *)
Parameter ber_check_tag : TYPE_descriptor -> list byte -> option check_tag_r.

Definition ZeroChar := Byte.repr 48.
  
(* memory representation of abstract types *)
Parameter TYPE_descriptor_rep : TYPE_descriptor
                                -> reptype (Tstruct _asn_TYPE_descriptor_s noattr). 

(* These two will express memory specifications *)

(* on any error write {buf = 0; size = 0},
    else {buf = ls; size = |ls|}*)
Parameter PRIMITIVE_TYPE_rep : option (list byte) 
                               -> reptype (Tstruct _ASN__PRIMITIVE_TYPE_s noattr).

(* on error rval c l write {code := c; consumed := l},
   else {code := OK; consumed := |ls| *)
Parameter dec_rval_rep : option (list byte) -> reptype (Tstruct _asn_dec_rval_s noattr).