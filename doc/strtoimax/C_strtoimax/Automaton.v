Require Import Nat List Decimal DecimalNat List Lia.
Import ListNotations.

Set Implicit Arguments.

Record fsa (S A : Type) := FSA {
  initial : S;
  next : S -> A -> S -> Prop
}.

Inductive fsa_run {S A : Type } (m : fsa S A) : list A -> S -> Prop :=
| step : forall a s, m.(next) m.(initial) a s -> fsa_run m [a] s
| trans : forall s1 a s2 l rs, m.(next) s1 a s2 -> fsa_run m l rs -> fsa_run m (a::l) rs.

Section strtoimax_automaton.
  
  Variable blen : nat.
  
  Definition MAX := to_uint (2 ^ (blen - 1) - 1).
  Definition MIN := to_uint (2 ^ (blen - 1)).
  
  (** inputs *)
  Inductive char :=
  | sign_char (s : bool)  (* [true] for [+] *)
  | digit_char (d : nat)
  | other_char.
  
  (** states *)
  Inductive strtoimax_state :=
  | EMPTY
  | INVAL
  | MORE (max : uint)
  | OK (n : nat) (max : uint) (b : Datatypes.comparison)
  | OK_MAX
  | RANGE
  | EXTRA.
  
  (* [n]th decimal digit of [u] *)
  Fixpoint nth_digit (n : nat) (u : uint) : nat :=
    match n, u with
    | O, _      => Unsigned.hd u
    | S n', Nil => 0
    | S n', _   => nth_digit n' (Unsigned.tl u)
    end.

  (* decimal length *)
  Let dlen := Unsigned.usize.
  (* [branch] selects which OK case to go to (over, under or exact) *)
  Let branch (d : nat) (n : nat) (max : uint) := Nat.compare d (nth_digit n max).
  Let branch_len (max : uint) (b : comparison) := match b with
                                                  | Gt => dlen max - 3
                                                  | _ => dlen max - 2
                                                  end.
  
  Reserved Notation "st1 -[ c ]-> st2" (at level 50).
  Inductive strtoimax_next : strtoimax_state -> char -> strtoimax_state -> Prop :=
  | inval         : forall c,       INVAL     -[ c               ]-> INVAL
  | range         : forall c,       RANGE     -[ c               ]-> RANGE
  | extra         : forall c,       EXTRA     -[ c               ]-> EXTRA
  | empty_other   :            EMPTY     -[ other_char      ]-> INVAL
  | empty_plus    :            EMPTY     -[ sign_char true  ]-> MORE MAX
  | empty_minus   :            EMPTY     -[ sign_char false ]-> MORE MIN
  | empty_digit   : forall d,       EMPTY     -[ digit_char d    ]-> OK 0 MAX (branch d 0 MAX)
  | more_other    : forall m,       MORE m    -[ other_char      ]-> INVAL
  | more_sign     : forall m s,     MORE m    -[ sign_char s     ]-> INVAL
  | more_digit    : forall d m,     MORE m    -[ digit_char d    ]-> OK 0 m (branch d 0 m)
  | okmax_other   :            OK_MAX    -[ other_char      ]-> EXTRA
  | okmax_sign    : forall s,       OK_MAX    -[ sign_char s     ]-> EXTRA
  | okmax_digit   : forall d,       OK_MAX    -[ digit_char d    ]-> RANGE
  | ok_other      : forall n m b,   OK n m b  -[ other_char      ]-> EXTRA
  | ok_sign       : forall n m b s, OK n m b  -[ sign_char s     ]-> EXTRA
  | ok_gt_step    : forall n m d,   n < branch_len m Gt ->
                               OK n m Gt -[ digit_char d ]-> OK (S n) m Gt
  | ok_lt_step    : forall n m d,   n < branch_len m Lt ->
                               OK n m Lt -[ digit_char d ]-> OK (S n) m Lt
  | ok_eq_step    : forall n m d,   n < branch_len m Eq ->
                               OK n m Eq -[ digit_char d ]-> OK (S n) m (branch d (S n) m)
  | ok_gt_last    : forall m d,     OK (branch_len m Gt) m Gt -[ digit_char d ]-> OK_MAX
  | ok_lt_last    : forall m d,     OK (branch_len m Lt) m Lt -[ digit_char d ]-> OK_MAX
  | ok_eq_last    : forall m d,     d <= nth_digit (branch_len m Eq) m ->
                               OK (branch_len m Eq) m Eq -[ digit_char d ]-> OK_MAX
  | ok_eq_overfl  : forall m d,     nth_digit (branch_len m Eq) m < d ->
                               OK (branch_len m Eq) m Eq -[ digit_char d]-> RANGE
  where "st1 -[ c ]-> st2" := (strtoimax_next st1 c st2).
  
  Definition strtoimax_fsa := {| initial := EMPTY; next := strtoimax_next |}.

  Lemma strtoimax_next_functional :
    forall c s s1 s2,
      s -[ c ]-> s1 ->
      s -[ c ]-> s2 ->
      s1 = s2.
  Proof.
    intros.
    destruct s.
    all: inversion H; inversion H0.
    all: unfold branch_len, branch in *; subst.
    all: try (replace d0 with d in * by congruence).
    all: try reflexivity.
    all: try discriminate.
    all: lia.
  Qed.

  Lemma strtoimax_next_total :
    forall s1 c, exists s2,
        s1 -[ c ]-> s2.
  Proof.
    intros.
    destruct s1, c.
    all: try (eexists; econstructor).
    destruct s; eexists; econstructor.
    destruct (Nat.compare n (branch_len max b)) eqn:B.
    - apply Compare_dec.nat_compare_eq in B; subst.
      destruct b.
       + destruct (Compare_dec.le_lt_dec d (nth_digit (branch_len max Eq) max)).
         * eexists; eapply ok_eq_last; assumption.
         * eexists; eapply ok_eq_overfl; assumption.
       + eexists; eapply ok_lt_last.
       + eexists; eapply ok_gt_last.
    - apply Compare_dec.nat_compare_Lt_lt in B.
      destruct b;
        econstructor; econstructor; assumption.
    - apply Compare_dec.nat_compare_Gt_gt in B.
      (* UNPROVABLE *)
      (* such state [OK n max b] is, however, unreachable for the automaton: *)
      Fact bad_state_unreachable :
        forall s c n max b,
          s -[ c ]-> OK n max b ->
          n <= branch_len max b.
      Admitted.
      (* this also proves there is always a finite number of OK steps *)
  Abort.
 
End strtoimax_automaton.
