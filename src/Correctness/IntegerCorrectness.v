(*       Require Import Int.Exec AbstractSpec Lib Prim.Exec.
Require Import Core.Core Core.Notations Core.Tactics.
From ExtLib.Structures Require Import Monad MonadWriter Monoid.
From ExtLib.Data Require Import Monads.OptionMonad List.

Import MonadNotation.

Open Scope monad.

(* Exec spec *)

Parameter int_to_byte : Z -> list byte.
Parameter int_of_byte : list byte -> Z.

Definition int_encoder : TYPE_descriptor -> Z -> errW1 asn_enc_rval :=
  fun td i => int_encoder td (int_to_byte i). 

Definition int_decoder : TYPE_descriptor -> list byte -> option (list byte * Z) :=
  fun td ls => int_decoder td ls.

(* Exec spec correctness wrt to the relational spec *)

Parameter int_der_encoder_correctness : forall td i z ls ,
    decoder_type td = INTEGER_t ->
    int_encoder td i [] = inr (ls, z) ->
    DER (INTEGER i) ls.

Parameter int_ber_decoder_correctness : forall td ls ls' z,
    decoder_type td = INTEGER_t ->
    int_decoder td ls = Some (ls', z) ->
    BER (INTEGER z) ls.

(* Roundtrip *)

Parameter int_roundtrip : forall td ls i z,
    decoder_type td = INTEGER_t ->
    int_encoder td i nil = inr (ls, encode z) ->
    int_decoder td ls = Some ([], i).

Require Import Primitive.Int.VstDec.

(* Check int_der_encode_spec. *)
*)
