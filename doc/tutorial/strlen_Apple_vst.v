Require Import Coq.Program.Basics.
Require Import Clight.strlen_Apple.
Require Import VST.floyd.proofauto.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope program_scope.

Definition strlen_spec : ident * funspec :=
  DECLARE _strlen
    WITH str : ptrofs, sh : share, s : list byte, b : block
    PRE [_str OF tptr tschar]
      PROP(readable_share sh;
           Ptrofs.unsigned str + (Zlength s + 1) < Ptrofs.modulus)
      LOCAL(temp _str (Vptr b str))
      SEP(cstring sh s (Vptr b str))
    POST [tuint]
      PROP()
      LOCAL(temp ret_temp (Vint (Int.repr (Zlength s))))
      SEP(cstring sh s (Vptr b str)).

Definition Gprog := ltac:(with_library prog [strlen_spec]).

Lemma znth_length_subsc_eq : forall i s, Znth i (s ++ [Byte.zero]) = Byte.zero -> 
                           0 <= i < Zlength s + 1 -> ~In Byte.zero s ->
                           Zlength s = i.
Proof.
  intros.
  apply Z.le_antisymm.
  replace (Zlength s + 1) with (Z.succ (Zlength s)) in H0 by reflexivity.
  rewrite Z.lt_succ_r in H0.
  cstring.
  Lia.lia.
Qed.

Lemma body_max: semax_body Vprog Gprog f_strlen strlen_spec.
Proof.
  start_function.
  unfold cstring in *.
  Intros.
  forward.
  forward_loop (
      EX i : Z,
        PROP(0 <= i < Zlength s + 1)
        LOCAL(temp _str (Vptr b str); 
              temp _s (Val.add (Vptr b str) (Vint (Int.repr i))))
        SEP(cstring sh s (Vptr b str)))
    break: (
      EX i : Z,
        PROP(i =? (Zlength s) = true)
        LOCAL(temp _str (Vptr b str);
              temp _s (Val.add (Vptr b str) (Vint (Int.repr (Zlength s)))))
        SEP(cstring sh s (Vptr b str)));
  unfold cstring in *.
  entailer!.
  Exists 0.
  entailer!.
  Intros i.
  assert_PROP (
      Vptr b (Ptrofs.add str (Ptrofs.of_int (Int.repr i))) =
      field_address (tarray tschar (Zlength s + 1)) 
                    [ArraySubsc i] (Vptr b str)).
  entailer!. {
    rewrite field_address_offset.
    unfold offset_val, nested_field_offset; simpl.
    normalize.
    unfold field_compatible.
    simpl.
    normalize.
    econstructor; trivial.
    econstructor; trivial.
    econstructor; [assumption|].
    econstructor.
    eapply align_compatible_rec_Tarray.
    intros.
    eapply align_compatible_rec_by_value.
    econstructor.
    simpl.
    normalize.
    unfold Z.divide.
    exists (Ptrofs.unsigned str + i0).
    rewrite Z.mul_1_r.
    reflexivity.
    easy.
  }
  forward.
  forward_if.
  normalize.
  abbreviate_semax.
  deadvars!.
  forward.
  Exists (i + 1).
  entailer!.
  cstring.
  forward.
  normalize.
  Exists (Zlength s).
  entailer!.
  pose proof znth_length_subsc_eq i s H3 H1 H0.
  rewrite H8.
  econstructor.
  apply Z.eqb_refl.
  reflexivity.
  Intros i.
  forward.
  autorewrite with sublist in *|-.
  unfold denote_tc_samebase.
  entailer!.
  simpl.
  destruct peq.
  simpl; trivial.
  contradiction.
  autorewrite with sublist in *|-.
  entailer!.
  unfold sem_sub; simpl.
  destruct eq_block; simpl.
  replace (Ptrofs.repr 1) with Ptrofs.one by reflexivity.
  rewrite Ptrofs.divs_one. 
  rewrite Ptrofs.sub_add_l; rewrite Ptrofs.sub_idem; 
    rewrite Ptrofs.add_zero_l.
  unfold Vptrofs; simpl.
  rewrite ptrofs_to_int_repr.
  reflexivity.
  reflexivity.
  contradiction.
Qed.
