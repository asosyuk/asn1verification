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
  inversion Enc; rename H0 into Res'.
  replace ([Byte.repr 1; Byte.repr 1; if Val 
                                     then Byte.repr 255 
                                     else Byte.repr 0]) with
      ([Byte.repr 1] ++ [Byte.repr 1] ++ [if Val 
                                          then Byte.repr 255 
                                          else Byte.repr 0]) by reflexivity.
  destruct Val eqn:V in Enc; subst; repeat econstructor.
Qed.

Theorem ber_decoder_correctness : forall td ls b z,
    decoder_type td = BOOLEAN_t ->
    bool_decoder td ls = Some (b, z) ->
    (* since bool_encoder returns how many bytes it consumed,
       we need to substract one byte to get to the bool value *)
    BER_Bool b (firstn 1 (skipn (Z.to_nat (z - 1)) ls)).
Proof.
  intros TD ToDec ResB Len DT Dec.
  unfold bool_decoder, BCTExecSpec.ber_check_tags in Dec; cbn in Dec.
  rewrite DT in Dec; cbn in Dec.
  destruct ToDec eqn:K1; [congruence|]; 
    destruct l eqn:K2; [congruence|]; 
      destruct ((i == 1) && (i0 == 1))%byte; cbn in *; [|congruence]; 
        destruct (Zlength_aux 2 byte l0 - 2 <? 1); cbn in *; [congruence|].
  replace (Pos.to_nat 2) with (2)%nat in Dec by reflexivity; 
    do 2 rewrite skipn_cons in Dec; 
    rewrite skipn_O in Dec.
  destruct l0 eqn:K3; cbn in *; [congruence|]; 
    inversion Dec.
  replace (Z.to_nat (3 - 1)) with (2)%nat by reflexivity; 
    do 2 rewrite skipn_cons; rewrite skipn_O; 
      unfold bool_to_byte.
  pose proof Byte.eq_spec i1 (default_byte).
  unfold bool_of_byte.
  destruct (i1 == default_byte)%byte eqn:K; cbn in *; subst; econstructor.
  assumption.
Qed.

Theorem boolean_roundtrip : forall td ls b z,
    decoder_type td = BOOLEAN_t ->
    z = Zlength ls ->
    execErrW (bool_encoder td b) nil = Some ls ->
    bool_decoder td ls = Some (b, z).
Proof.
  intros TD ls B z DT Len.
  unfold execErrW, bool_encoder, primitive_encoder, 
  DWTExecSpec.der_write_tags, bool_decoder, 
  BCTExecSpec.ber_check_tags, bool_of_byte; cbn; rewrite DT.
  intros Res; inversion Res as [T]; clear Res; rename T into Res.
  replace (Byte.repr 1 == 1)%byte with true by reflexivity; cbn.
  replace (Pos.to_nat 2) with (2)%nat by reflexivity.
  do 2 rewrite skipn_cons; rewrite skipn_O; cbn.
  pose proof Byte.eq_spec  
       ((if B then Byte.repr 255 else Byte.repr 0)) 
       (default_byte) as ResC.
  unfold default_byte in *; cbn in ResC.
  rewrite <-Res in Len; cbn in Len.
  subst.
  destruct B; cbn.
  * assert (Byte.repr 255 <> Byte.repr 0) as T by congruence.
    pose proof Byte.eq_false (Byte.repr 255) (Byte.repr 0) T as T'; 
      rewrite T'; reflexivity.
  * pose proof Byte.eq_true (Byte.repr 0) as T; rewrite T; reflexivity.
Qed.