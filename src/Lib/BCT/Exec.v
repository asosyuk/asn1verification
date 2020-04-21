Require Import Core.Core Core.Notations Core.Notations Types.
Require Import ExtLib.Structures.Monad.

Import MonadNotation.

(* checks the tag, outputs consumed length and expected length *)
Definition ber_check_tags (td : TYPE_descriptor) (ls : list byte) : 
  option check_tag_r :=
  match decoder_type td with
  | BOOLEAN_t => match ls with
                | x1::x2::_ => if ((x1 == Byte.one) && (x2 == Byte.one))%byte
                            then Some (mk_check_tag_rval 2 1 )
                            else None
                | _ => None
                end
  | _ => None
  end.

Theorem ber_check_tags_bool_succ : forall td ls,
    decoder_type td = BOOLEAN_t ->
    ber_check_tags td ([Byte.one; Byte.one] ++ ls) = 
    Some (mk_check_tag_rval 2 1).
Proof.
  intros.
  unfold ber_check_tags.
  rewrite H.
  reflexivity.
Qed.
