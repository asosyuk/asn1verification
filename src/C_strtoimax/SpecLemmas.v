Require Import StructTact.StructTactics.
Require Import Core.Core.
Require Import Spec. 

Lemma OK_None_ptr_contradiction :
  forall dist str fin inp value s last_digit m m' s' val,
    asn_strtoimax_lim_loop m str fin inp value s last_digit dist m
    <> Some {| return_type := ASN_STRTOX_OK;
               value := val;
               str_pointer := None;
               memory := Some m';
               sign := s'; |}.
Proof.
  destruct dist as [dist |].
    - induction dist; intros; simpl.
      + try congruence.
      + repeat break_match; 
          try congruence.
        unfold asn_strtoimax_lim_loop in IHdist.
        eapply IHdist.
    - discriminate.
Qed.

Proposition OK_None_val_contradiction :
  forall dist str fin inp value s last_digit m m' s' p,
    asn_strtoimax_lim_loop m str fin inp value s last_digit dist m
    <> Some {| return_type := ASN_STRTOX_OK;
               value := None;
               str_pointer := p;
               memory := Some m';
               sign := s'; |}.
Proof.
  destruct dist as [dist |].
    - induction dist; intros; simpl.
      + try break_match;
          congruence.
      + repeat break_match; 
          try congruence.
        unfold asn_strtoimax_lim_loop in IHdist.
        eapply IHdist.
    - discriminate.
Qed.

Lemma ED_None_ptr_contradiction :
  forall dist str fin inp value s last_digit m m' s' val,
    asn_strtoimax_lim_loop m str fin inp value s last_digit dist m
    <> Some {| return_type := ASN_STRTOX_EXTRA_DATA;
               value := val;
               str_pointer := None;
               memory := Some m';
               sign := s'; |}.
Proof.
  destruct dist as [dist |].
    - induction dist; intros; simpl.
      + try congruence.
      + repeat break_match; 
          try congruence.
        unfold asn_strtoimax_lim_loop in IHdist.
        eapply IHdist.
    - discriminate.
Qed.

Proposition ED_None_val_contradiction :
  forall dist str fin inp value s last_digit m m' s' p,
    asn_strtoimax_lim_loop m str fin inp value s last_digit dist m
    <> Some {| return_type := ASN_STRTOX_EXTRA_DATA;
               value := None;
               str_pointer := p;
               memory := Some m';
               sign := s'; |}.
Proof.
  destruct dist as [dist |].
    - induction dist; intros; simpl.
      + try break_match;
          congruence.
      + repeat break_match; 
          try congruence.
        unfold asn_strtoimax_lim_loop in IHdist.
        eapply IHdist.
    - discriminate.
Qed.
