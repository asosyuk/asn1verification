Require Import Core.Core Core.Tactics.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Clight.asn_application.
Require Import Lib.VstLib Lib.Stdlib.
Require Import Core.Notations.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Definition dummy_callback  : funspec :=
    WITH  data_p : val, size : Z,
         key_p : val
    PRE [tptr tvoid, tuint, tptr tvoid]
      PROP ()
      PARAMS (data_p; Vint (Int.repr size); key_p)
      GLOBALS ()
      SEP ()
    POST [tint]
      PROP ()
      LOCAL (temp ret_temp Vzero)
      SEP (). 
