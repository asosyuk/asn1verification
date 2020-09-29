Require Import Core.Core Core.Notations Core.Notations Types.
Require Import ExtLib.Structures.Monad.

Import MonadNotation.

Inductive DWT_Error := NotBoolean.

(* Writes header octets *)
Definition der_write_tags (td : TYPE_descriptor) : errW1 Z :=
  match decoder_type td with
  | BOOLEAN_t => tell1 (map Byte.repr [1; 1]) >>= fun _ => ret 2
  | _ => raise (CustomError NotBoolean)
  end.

Theorem eval_dwt_boolean : forall td,
  decoder_type td = BOOLEAN_t ->
  evalErrW (der_write_tags td) [] = Some 2.
Proof.
  intros.
  unfold evalErrW, der_write_tags; rewrite H; cbn.
  reflexivity.
Qed.

Theorem exec_dwt_boolean : forall td,
  decoder_type td = BOOLEAN_t ->
  execErrW (der_write_tags td) [] = Some [Byte.one; Byte.one].
Proof.
  intros.
  unfold execErrW, der_write_tags; rewrite H; cbn.
  reflexivity.
Qed.    
  
