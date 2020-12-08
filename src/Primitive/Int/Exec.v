Require Import VST.floyd.proofauto.
Require Import Core.Core Core.Notations Lib.Lib Prim.Exec.
From ExtLib.Structures Require Import Monad MonadWriter MonadExc.
From ExtLib.Data Require Import Monads.OptionMonad.



Open Scope byte.

(* Decoding fails : 
   1) when calloc fails to allocate memory for the output structure sptr (FAIL) SEP spec
   2) if ber_check_tags return FAIL (when?) or MORE (?) - executable spec
   3) if not enough data according to length read (MORE) - executable spec
   4) expected length doesn't fit into size (FAIL) ?
   5) malloc buf allocation fails (FAIL) SEP spec
 *)

Section Encoder.

(* If the contents octets of an integer value encoding
   consist of more than one octet, then the bits of the
   first octet and bit 8 of the second octet:
   a) shall not all be ones; and
   b) shall not all be zero. *)

(*Notation "t @ n" := (Int.testbit t n) (at level 50).
Notation all_zero := Int.zero.
Definition all_one  := Int.repr (Byte.max_unsigned).
Notation default_byte := all_zero. *)

Fixpoint canonicalize_int (l : list byte) : list byte :=
  match l with
  | nil => nil 
  | x :: xs => match xs with
            | nil => l (* If there is only one octet do nothing *)
            | y :: ys => (* else do check *)
              if eq_dec x 0
              then if eq_dec (y & Byte.repr 128) (Byte.repr 255) (* 1st bit of y is one *)
                   then xs 
                   else canonicalize_int xs 
              else if eq_dec x (Byte.repr 255)
                   then if  eq_dec (y & Byte.repr 128) (Byte.repr 255)
                        then canonicalize_int xs
                        else xs
              else l
            end
  end.

Definition int_encoder td struct_len buf_size (ls : list byte) := 
  let ls_c := canonicalize_int ls in
  let c := map Int.repr (map Byte.unsigned ls_c) in
  let shift := (len ls - len ls_c)%Z in
  primitive_encoder td (struct_len - shift) buf_size c.

End Encoder.

Lemma can_data_len : forall ll, (Zlength (canonicalize_int ll) <= Zlength ll)%Z.
Proof.
  induction ll; simpl.
  - lia.
  - repeat break_match; autorewrite with sublist in *; try list_solve.
Qed.


Definition LI_int i data := 
           (Znth i data = 0 /\ Znth (i + 1) data & Byte.repr 128 = 0) \/
           (Znth i data = Byte.repr 255 /\  Znth (i + 1) data & Byte.repr 128 <> 0).
(*
Lemma canonicalize_int_spec : 
  forall data z , (0 < z)%Z ->
            (forall i, 0 <= i < z -> LI_int i data) ->
            (Znth z data <> 0 \/
             Znth (z + 1) data & Byte.repr 128 <> 0%byte) /\
            (Znth z data <> Byte.repr 255 \/
             Znth (z + 1) data & Byte.repr 128 = 0) ->
            canonicalize_int data <> data.
  { induction data.
    - admit.
    - intros.
      simpl.
      break_match. admit.
      repeat break_if; try discriminate.
      admit.
      admit.
      admit.
      admit.
      unfold LI_int in H0.
      pose proof (H0 0%Z).
      cbn in H2.
      destruct H2. lia. intuition. intuition.
Admitted. *)


Lemma canonicalize_int_spec_z : 
  forall data z , (0 < z)%Z ->
            (forall i, 0 <= i < z -> LI_int i data) ->
            (Znth z data <> 0 \/
             Znth (z + 1) data & Byte.repr 128 <> 0%byte) /\
            (Znth z data <> Byte.repr 255 \/
             Znth (z + 1) data & Byte.repr 128 = 0) ->
            z = (len data - len (canonicalize_int data))%Z.
  { induction data.
    - admit.
    - intros.
      simpl.
      break_match. admit.
      repeat break_if; try discriminate.
      admit.
      admit.
      admit.
      admit.
      unfold LI_int in H0.
      pose proof (H0 0%Z).
      cbn in H2.
      destruct H2. lia. intuition. intuition.
Admitted.


Open Scope Z.

Definition LI i data := 
           (Byte.unsigned (Znth i data) = 0 /\ 
            Byte.unsigned (Znth (i + 1) data)
            & 128 = 0) \/ (Byte.unsigned (Znth i data) = 255 /\ 
                          Byte.unsigned (Znth (i + 1) data)
                          & 128 <> 0).

Lemma canonicalize_Z_spec : forall data z,
    (forall i, 0 <= i < z -> LI i data) ->
    Byte.unsigned (Znth z data) <> 0 \/
    Byte.unsigned (Znth (z + 1) data) & 128 <> 0 \/
    Byte.unsigned (Znth z data) <> 255 \/
    Byte.unsigned (Znth (z + 1) data) & 128 = 0 ->
     z = (len data - len (canonicalize_int data))%Z.
Proof.
  intros.
Admitted.

Lemma canonicalize_Z_spec_r : forall data z,
    z >= len data - 1 ->
    (forall i, 0 <= i < z -> LI i data) ->
    (z = len data - len (canonicalize_int data))%Z.
Admitted.

Lemma canonicalize_int_sublist : forall data,
  data = sublist 0 (len data - len (canonicalize_int data)) data 
                 ++ canonicalize_int data.
Admitted.


Lemma sublist_eq_Zlength : forall ls, exists y, 0 <= y <= len ls /\
                                         canonicalize_int ls = sublist y (len ls) ls.
Proof.
  induction ls.
  - exists 0. simpl. autorewrite with sublist. easy.
  - simpl. 
    repeat break_match. 
    1, 6: exists 0; autorewrite with sublist; split; try lia; auto. list_solve.
    1, 4: exists 1; erewrite sublist_1_cons; autorewrite with sublist; auto;
              split; try lia; auto; try list_solve.
            destruct IHls as [y IHls].
            destruct (zeq y 0).
            exists (1).
            inversion IHls as [P1 P2].
            erewrite P2.
            erewrite sublist_1_cons.
            autorewrite with sublist; split; auto.
            list_solve.
            exists (y + 1).
            inversion IHls as [P1 P2].
            erewrite P2.
            replace (a :: i :: l) with ([a] ++ i :: l).
            erewrite sublist_app2. autorewrite with sublist.
            split. admit. reflexivity.  list_solve. reflexivity.
            destruct IHls as [y IHls].
            destruct (zeq y 0).
            exists (1).
            inversion IHls as [P1 P2].
            erewrite P2.
            erewrite sublist_1_cons.
            autorewrite with sublist; split; auto.
            list_solve.
            exists (y + 1).
            inversion IHls as [P1 P2].
            erewrite P2.
            replace (a :: i :: l) with ([a] ++ i :: l).
            erewrite sublist_app2. autorewrite with sublist.
            split. admit. reflexivity.  list_solve. reflexivity. 
Admitted.
