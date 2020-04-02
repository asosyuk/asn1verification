Require Import Primitive.BooleanExecSpec Primitive.AbstractSpec Lib.Lib.
Require Import Core.Core Core.Notations Core.Tactics List.
From ExtLib.Structures Require Import Monad MonadWriter Monoid.
From ExtLib.Data Require Import Monads.OptionMonad List.

Import ListNotations.
Import MonadNotation.

Open Scope monad.

Theorem der_encoder_correctness : forall td b ls ,
  decoder_type td = BOOLEAN_t ->
  execErrW (bool_encoder td b) nil = Some ls ->
  DER (BOOLEAN b) ls.
Proof.
  intros TD Val Res DT Enc; intros.
  unfold bool_encoder, primitive_encoder, DWTExecSpec.der_write_tags in Enc. 
  rewrite DT in Enc; cbn in Enc.
  assert ([Byte.repr 1; Byte.repr 1; if Val 
                                     then Byte.repr 255 
                                     else Byte.repr 0] = Res) 
    as Res' by congruence.
  replace ([Byte.repr 1; Byte.repr 1; if Val 
                                     then Byte.repr 255 
                                     else Byte.repr 0]) with
      ([Byte.repr 1] ++ [Byte.repr 1] ++ [if Val 
                                          then Byte.repr 255 
                                          else Byte.repr 0]) in Res' 
    by reflexivity.
  destruct Val eqn:V in Enc; subst; repeat econstructor.
Qed.

Definition byte_to_bool b := if (b == 0)%byte then false else true.

Theorem ber_decoder_correctness : forall td ls b z,
    decoder_type td = BOOLEAN_t ->
    bool_decoder td ls = Some (b, z) ->
    BER_Bool (byte_to_bool b) (firstn (Z.to_nat z) ls).
Admitted.

