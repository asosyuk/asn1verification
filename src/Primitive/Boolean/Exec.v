Require Import Core.Core Core.Notations Lib.Lib BCT.Exec.
Require Import ExtLib.Structures.Monad.
Import MonadNotation.

Section Encoder.

Definition bool_encoder := 
  fun td (b : bool) => primitive_encoder td [byte_of_bool b].

(* Related lemmas *)

Theorem exec_boolean_enc : forall td b, 
  decoder_type td = BOOLEAN_t ->
  execErrW (bool_encoder td b) [] = Some [Byte.one; Byte.one; byte_of_bool b].
Proof.
  intros.
  unfold execErrW, bool_encoder, primitive_encoder, Exec.der_write_tags; 
    rewrite H; cbn.
  reflexivity.
Qed.

Theorem eval_boolean_enc : forall td b,
  decoder_type td = BOOLEAN_t ->
  evalErrW (bool_encoder td b) [] = Some (encode 3).
Proof.
  intros.
  unfold evalErrW, bool_encoder, primitive_encoder, Exec.der_write_tags;
    rewrite H; cbn.
  reflexivity.
Qed.

End Encoder.

Section Decoder.

(* checks tag in ls wrt td, 
   then returns head of ls and consumed bytes or error *) 
Definition bool_decoder td ls : option (bool * Z) :=
    match ls with
    | [] => None
    | _ => ber_check_tags td ls >>=
                        fun x => let c := tag_consumed x in 
                              let e := tag_expected x in 
                              if (Zlength ls - c <? e) || negb (e =? 1) 
                              then None 
                              else hd_error (skipn (Z.to_nat c) ls) 
                                     >>= fun y => Some (bool_of_byte y, c + 1)
    end.

(* Related lemmas *)

Theorem boolean_dec_res : forall td ls res,
  decoder_type td = BOOLEAN_t ->
  bool_decoder td [Byte.repr 1; Byte.repr 1; byte_of_bool res] 
  = Some (res, 3) \/ bool_decoder td ls = None.
Proof.
  intros.
  unfold bool_decoder, primitive_decoder, ber_check_tags, Byte.one; rewrite H.
  assert (Byte.repr 1 == Byte.repr 1 = true)%byte as T by reflexivity; 
    rewrite T; cbn.
  replace (Pos.to_nat 2) with (2)%nat by reflexivity.
  do 2 rewrite skipn_cons; rewrite skipn_O; rewrite hd_error_cons.
  unfold bool_of_byte, byte_of_bool; repeat break_match; try discriminate; auto.
Qed.

End Decoder.
