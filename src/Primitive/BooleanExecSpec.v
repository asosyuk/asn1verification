Require Import Core.Core Core.Notations Lib.Lib Lib.BCTExecSpec.
Require Import ExtLib.Structures.Monad.
Import ListNotations.
Import MonadNotation.

Section Encoder.

Definition bool_encoder := 
  fun td (b : bool) => let t := if b then (Byte.repr 255) else (Byte.repr 0) in 
                 primitive_encoder td (cons t nil).

(* Related lemmas *)

Theorem exec_boolean_enc : forall td b, 
  decoder_type td = BOOLEAN_t ->
  execErrW (bool_encoder td b) [] = Some [Byte.one; Byte.one; bool_to_byte b].
Proof.
  intros.
  unfold execErrW, bool_encoder, primitive_encoder, DWTExecSpec.der_write_tags; 
    rewrite H; cbn.
  unfold bool_to_byte; reflexivity.
Qed.

Theorem eval_boolean_enc : forall td b,
  decoder_type td = BOOLEAN_t ->
  evalErrW (bool_encoder td b) [] = Some (encode 3).
Proof.
  intros.
  unfold evalErrW, bool_encoder, primitive_encoder, DWTExecSpec.der_write_tags; 
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

End Decoder.
