Require Import Boolean.Exec AbstractSpec Lib Prim.Exec.
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
  intros TD Val Res DT.
  rewrite exec_boolean_enc by assumption.
  intros.
  inversion H. 
  replace ([1%byte; 1%byte; byte_of_bool Val]) with
      ([Byte.repr 1] ++ [Byte.repr 1] ++ [byte_of_bool Val]) by reflexivity.
  destruct Val eqn:V; subst; repeat econstructor.
Qed.

Theorem ber_decoder_correctness : forall td ls b z,
    decoder_type td = BOOLEAN_t ->
    bool_decoder td ls = Some (b, z) ->
    (* since bool_encoder returns how many bytes it consumed,
       we need to substract one byte to get to the bool value *)
    BER_Bool (bool_of_byte b) (firstn 1 (skipn (Z.to_nat (z - 1)) ls)).
Proof.
  intros TD ToDec ResB Len DT Dec.
  unfold bool_decoder, Exec.ber_check_tags in Dec; cbn in Dec.
  rewrite DT in Dec; cbn in Dec.
  repeat break_match_hyp; try discriminate.
  inversion Heqo.
  inversion Dec.
  subst; cbn in *.
  replace (Pos.to_nat 2) with (2)%nat in Heqo0 by reflexivity; 
    do 2 rewrite skipn_cons in Heqo0; 
    rewrite skipn_O in Heqo0.
  destruct l0 eqn:K3; cbn in *; [congruence|].
  replace (Pos.to_nat 2) with (2)%nat by reflexivity; 
    do 2 rewrite skipn_cons; rewrite skipn_O; 
      unfold byte_of_bool.
  pose proof Byte.eq_spec i1 (default_byte).
  unfold bool_of_byte.
  inversion Heqo0.
  destruct (i0 == default_byte)%byte eqn:K; cbn in *; subst;
    pose proof Byte.eq_spec ResB default_byte; rewrite K in H0.
  subst; econstructor.
  rewrite K; econstructor; assumption.
Qed.

Theorem boolean_roundtrip : forall td ls b z,
    decoder_type td = BOOLEAN_t ->
    z = Zlength ls ->
    execErrW (bool_encoder td b) nil = Some ls ->
    bool_decoder td ls = Some (byte_of_bool b, z).
Proof.
  intros TD ls B z DT Len.
  unfold execErrW, bool_encoder, primitive_encoder,
  Exec.der_write_tags, bool_decoder,
  Exec.ber_check_tags, byte_of_bool; cbn; rewrite DT.
  intros Res; inversion Res as [T]; clear Res; rename T into Res.
  replace (Byte.repr 1 == 1)%byte with true by reflexivity; cbn.
  replace (Pos.to_nat 2) with (2)%nat by reflexivity.
  do 2 rewrite skipn_cons; rewrite skipn_O; cbn.
  pose proof Byte.eq_spec (byte_of_bool B) default_byte as ResC.
  unfold byte_of_bool in *.
  unfold default_byte in *; cbn in ResC.
  rewrite <-Res in Len; cbn in Len.
  subst.
  destruct B; cbn; repeat f_equal.
Qed.
