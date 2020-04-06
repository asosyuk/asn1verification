Require Import BooleanExecSpec AbstractSpec Lib.Lib.
Require Import Core.Core Core.Notations Core.Tactics.
From ExtLib.Structures Require Import Monad MonadWriter Monoid.
From ExtLib.Data Require Import Monads.OptionMonad List.

Import MonadNotation.

Open Scope monad.

Theorem der_encoder_correctness : forall td b ls ,
  decoder_type td = BOOLEAN_t ->
  execErrW (bool_encoder td b) nil = Some ls ->
  DER (BOOLEAN b) ls.
Proof.
  intros TD Val Res; intros.
  destruct TD; cbv in H; subst.
  unfold bool_encoder, primitive_encoder in H0.
  destruct Val eqn:V in H0.
Admitted.

Definition byte_to_bool b := if (b == 0)%byte then false else true.

Theorem ber_decoder_correctness : forall td ls b z,
    decoder_type td = BOOLEAN_t ->
    bool_decoder td ls = Some (b, z) ->
    BER_Bool (byte_to_bool b) (firstn (Z.to_nat z) ls).
Admitted.

