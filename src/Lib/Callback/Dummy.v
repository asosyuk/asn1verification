Require Import Core.Core Core.Tactics Lib.VstLib Lib.Stdlib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Clight.dummy.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope Z.

 Definition dummy_callback_spec : funspec :=
    WITH data_p : val, size : Z,
         key_p : val
    PRE [tptr tvoid, tuint, tptr tvoid]
      PROP (0 <= size <= Int.max_unsigned)
      PARAMS (data_p; Vint (Int.repr size); key_p)
      GLOBALS ()
      SEP ()
    POST [tint]
      PROP ()
      LOCAL (temp ret_temp (if size <? 0 then (Vint (Int.repr (-1))) else Vzero))
      SEP (). 

Definition dummy_callback : ident * funspec :=
  DECLARE _dummy dummy_callback_spec.

Definition Gprog := ltac:(with_library prog [dummy_callback]).

Theorem dummy_callback_correctness : semax_body Vprog Gprog f_dummy dummy_callback.
Admitted.

(* 
Proof.
  start_function.
  forward_if (
      PROP ( ) 
      LOCAL (temp _t'1 (if size <? 0 
                        then (Vint (Int.repr (-1))) 
                        else Vzero);
             temp _buffer data_p; temp _size (Vint (Int.repr size)); 
             temp _application_specific_key key_p)  
      SEP ()).
  * (* if size = 0 *)
    forward.
    entailer!.
  * (* if size <> 0 *)
    forward.
    entailer!.
    break_if; [rewrite Z.eqb_eq in Heqb; congruence| reflexivity].
  * forward.
Qed. 
*)
