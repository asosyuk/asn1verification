Require Import Core.Core.
Require Import VST.floyd.proofauto.
Require Import Clight.asn_codecs_prim.
Require Import Lib.

Require Export Lib.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.

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


Definition cb_type := (Tfunction 
                          (Tcons (tptr tvoid) 
                                 (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint 
                          cc_default).
Definition enc_rval_s := Tstruct _asn_enc_rval_s noattr.
Definition type_descriptor_s := Tstruct _asn_TYPE_descriptor_s noattr.
