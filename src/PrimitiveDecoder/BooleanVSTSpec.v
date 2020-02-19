(* VST specification of as *)
Require Import Clight.asn_codecs_prim.
Require Import Core.Core Lib.
Require Import VST.floyd.proofauto.
Require Import BooleanExecSpec.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section PrimitiveParser.

End PrimitiveParser.
