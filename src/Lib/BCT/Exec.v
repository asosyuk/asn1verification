Require Import Core.Core Core.Notations Core.Notations Types.
Require Import ExtLib.Structures.Monad.

(* checks the tag, outputs consumed length and expected length *)
Definition ber_check_tags (td : TYPE_descriptor) (ls : list byte) : 
  option check_tag_r :=
  match decoder_type td with
  | BOOLEAN_t => match ls with
                | x1::x2::_ => if ((x1 == Byte.one) && (x2 == Byte.one))%byte
                            then Some (mk_check_tag 2 1 )
                            else None
                | _ => None
                end
  | _ => None
  end.

Theorem ber_check_tags_bool_res : forall td ls,
    decoder_type td = BOOLEAN_t ->
    ber_check_tags td ls = Some (mk_check_tag 2 1) 
    \/ ber_check_tags td ls = None.
Proof.
  intros.
  unfold ber_check_tags; rewrite H.
  repeat break_match; auto.
Qed.

Theorem ber_check_tags_bool_Some : forall td ls,
    decoder_type td = BOOLEAN_t ->
    ber_check_tags td (Byte.one::Byte.one::ls) = 
    Some (mk_check_tag 2 1).
Proof.
  intros.
  unfold ber_check_tags.
  rewrite H.
  reflexivity.
Qed.

Theorem ber_check_tags_bool_Some_intro : forall td ls,
    decoder_type td = BOOLEAN_t ->
    ber_check_tags td ls = Some (mk_check_tag 2 1) ->
    exists tl, ls = 1%byte::1%byte::tl.
Proof.
  intros td ls DT.
  unfold ber_check_tags.
  repeat break_match; try discriminate.
  intros.
  unfold andb in Heqb; repeat break_match_hyp; try discriminate.
  pose proof Byte.eq_spec i 1%byte as T; rewrite Heqb0 in T.
  pose proof Byte.eq_spec i0 1%byte as T1; rewrite Heqb in T1.
  rewrite T, T1.
  exists l0; reflexivity.
Qed.
