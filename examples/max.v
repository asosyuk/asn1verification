From Coq Require Import String List ZArith Bool.Bool Lia.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Values ClightBigstep Maps Events Memory.
Local Open Scope Z_scope.

Definition _i1 : ident := 53%positive.
Definition _i2 : ident := 54%positive.
Definition _t'1 : ident := 57%positive.

Definition f_max := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_i1, tint) :: (_i2, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Etempvar _i1 tint) (Etempvar _i2 tint) tint)
    (Sset _t'1 (Ecast (Etempvar _i2 tint) tint))
    (Sset _t'1 (Ecast (Etempvar _i1 tint) tint)))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition max_fun_spec (i1 i2 : Z) : Z := if i1 <=? i2 then i2 else i1.
Definition VintZ (x : Z) := Vint (Int.repr x).

Theorem max_correct : forall i1 i2 ge e te m,
    Int.min_signed <= i1 <= Int.max_signed ->
    Int.min_signed <= i2 <= Int.max_signed ->
    te ! _i1 = Some (VintZ (i1)) ->
    te ! _i2 = Some (VintZ (i2)) ->
    exists t te', exec_stmt ge e te m f_max.(fn_body) t te' m 
             (Out_return (Some (VintZ (max_fun_spec i1 i2), tint))).
Proof.
  intros.
  repeat eexists.
  repeat econstructor.
  apply H1.
  apply H2.
  simpl.
  econstructor.
  simpl.
  destruct 
  econstructor.
  instantiate (1 := (Val.of_bool (Z.leb i1 i2))).
  assert (Val.of_bool (negb (Int.lt (Int.repr i2) (Int.repr i1)))
          = Val.of_bool (Z.leb i1 i2)).
  -
    f_equal.
    unfold negb, Int.lt, zlt.
    case Z_lt_dec.
    all: repeat rewrite Int.signed_repr.
    2,5: apply H.
    2,4: apply H0.
    all: intros.
    2: rename n into l.
    all: rewrite <-Z.leb_gt in l.
    2: apply not_false_is_true in l.
    all: auto.
  -
    rewrite <-H3.
    econstructor.
  -
    simpl.
    instantiate (1 := (Z.leb i1 i2)).
    cbn.
    case_eq (Val.of_bool (i1 <=? i2)).
    all: unfold Val.of_bool.
    all: destruct (i1 <=? i2).
    all: intros.
    all: try discriminate.
    all: f_equal.
    all: unfold negb, Int.eq, Int.zero, zeq.
    all: rewrite Int.unsigned_repr.
    1,3: case Z.eq_dec.
    all: intros.
    all: try reflexivity.
    3,4: cbn; lia.
    * 
      inversion H3.
      rewrite <-H5 in e0.
      unfold Int.one in e0.
      rewrite Int.unsigned_repr in e0.
      inversion e0.
      cbn.
      lia.
    *
      inversion H3.
      rename n into e0.
      rewrite <-H5 in e0.
      unfold Int.zero in e0.
      rewrite Int.unsigned_repr in e0.
      contradict e0.
      reflexivity.
      cbn.
      lia.
  -
    case_eq (i1 <=? i2).
    all: repeat econstructor.
    apply H2.
    instantiate (1 := VintZ i2).
    * 
      repeat econstructor.
      apply H2.
      instantiate (1 := VintZ i2).
      econstructor.
    * 
      intros.
      repeat econstructor.
      apply H1.
      cbn.
