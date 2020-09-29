Require Import Core.Core Core.Notations Lib.Lib BCT.Exec Prim.Exec.
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
  evalErrW (bool_encoder td b) [] = Some 3.
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
Definition bool_decoder td ls :=
    match ls with
    | [] => None
    | _ => ber_check_tags td ls >>=
                        fun x => let c := tag_consumed x in 
                              let l := tag_length x in 
                              if (Zlength ls - c <? l) || negb (l =? 1) 
                              then None 
                              else hd_error (skipn (Z.to_nat c) ls) 
                                     >>= fun y => Some (bool_of_byte y, c + 1)
    end.

(* Related lemmas *)

Theorem boolean_dec_res : forall td ls,
  decoder_type td = BOOLEAN_t ->
  bool_decoder td ls = None \/ exists res, bool_decoder td ls = Some (res, 3).
Proof.
  intros.
  unfold bool_decoder, primitive_decoder, ber_check_tags, Byte.one; rewrite H.
  repeat break_match; try discriminate; auto.
  cbn.
  repeat break_match; try discriminate; auto.
  right; exists (bool_of_byte i1); reflexivity.
Qed.

End Decoder.
