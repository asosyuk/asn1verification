Require Import StructTact.StructTactics.
Require Import Core.Core.
Require Import C_strtoimax.Spec. 

Lemma OK_None_contradiction_1 :
  forall dist str fin inp value s last_digit m m' val,
    asn_strtoimax_lim_loop m str fin inp value s last_digit dist m
    <> Some {| return_type := ASN_STRTOX_OK;
              value := val;
              str_pointer := None;
              memory := Some m'
           |}.
Proof.
  induction dist; intros; simpl.
    + break_match;
      congruence.
    + repeat break_match;
        try congruence.
      eapply IHdist.
Qed.

Proposition OK_None_contradiction_2 :
  forall dist str fin inp value s last_digit m m' p,
    asn_strtoimax_lim_loop m str fin inp value s last_digit dist m
    <> Some {| return_type := ASN_STRTOX_OK;
              value := None;
              str_pointer := p;
              memory := Some m'
           |}.
Proof.
  induction dist; intros; simpl.
    + break_match;
      congruence.
    + repeat break_match;
        try congruence.
      eapply IHdist.
Qed.
