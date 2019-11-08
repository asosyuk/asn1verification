Require Import AbstractSpec.
Require Import VST.floyd.proofauto.

Definition value_until j l := 
             (value (Z_of_string (sublist 0 j l))). 

Definition ASN1_INTMAX_MAX := Int64.max_unsigned.
Definition upper_boundary := Z.div ASN1_INTMAX_MAX 10.
Definition last_digit_max := Zmod ASN1_INTMAX_MAX 10.
Definition last_digit_max_minus := last_digit_max + 1.

Lemma lt_ub_bounded : forall j ls, value_until j ls < upper_boundary ->
                bounded (value_until (j + 1) ls) = true.
Admitted.


Lemma value_always_bounded : forall j ls,
  0 <= j < Zlength ls 
  bounded (value_until j ls) = true.

Lemma next_value:
  forall (ls : list byte) (j : Z),
    0 <= j + 1 <= Zlength ls ->
    forall i : byte,
      Znth j ls = i ->
      ((Byte.signed i >=? 48) && (Byte.signed i <=? 57))%bool = true ->
      (value_until (j + 1) ls) =
      (value_until j ls * 10 + (Byte.signed i - 48)).
Admitted.

Lemma ub_last_digit_error_range : forall j i i0 ls,
  0 <= j < Zlength ls ->
  Znth j ls = i0 ->
  (value_until j ls > upper_boundary \/
  (value_until j ls = upper_boundary /\
  last_digit_max < (Byte.signed i0 - 48))) ->
  (res (Z_of_string (i :: ls))) = ASN_STRTOX_ERROR_RANGE.
 Admitted.

Lemma ub_last_digit_error_range_index : forall j i i0 ls,
  0 <= j < Zlength ls ->
  Znth j ls = i0 ->
  (value_until j ls > upper_boundary \/
  (value_until j ls = upper_boundary /\
  last_digit_max < (Byte.signed i0 - 48))) ->
  (index (Z_of_string (i :: ls))) = j + 1.
 Admitted.


Lemma extra_data_index : forall j i ls,
  0 <= j < Zlength ls ->
  Znth j ls = i ->
  is_digit i ->
  (index (Z_of_string ls)) = j.
 Admitted.

(** Need a tactic to take out arithmetic hypotheses from this:

H5 : typed_true tint
         (force_val
            (sem_cmp_pp Clt
               (Vptr end'_b (Ptrofs.add (Ptrofs.add str_ofs Ptrofs.one) (Ptrofs.repr j)))
               (Vptr end'_b end'_ofs))) 

typed_false tint
          (force_val
             (sem_cmp_pp Clt
                (Vptr end'_b
                   (Ptrofs.add (Ptrofs.add (Ptrofs.add str_ofs Ptrofs.one) (Ptrofs.repr j))
                      (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1)))))
                (Vptr end'_b end'_ofs)))


**)
