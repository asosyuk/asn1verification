Require Import AbstractSpec.
Require Import VST.floyd.proofauto.
Require Import StructTact.StructTactics.

Lemma loop_aux : forall ls v ind i r, 
    Z_of_string_loop ls v ind = r ->
    res r = ASN_STRTOX_OK ->
    is_digit i = true ->
    bounded (value r * 10 + (Byte.signed i - 48)) = true ->
    Z_of_string_loop (app ls [i]) v ind = {| res := ASN_STRTOX_OK;
         value := (value r * 10 + (Byte.signed i - 48));
         index := (index r) + 1
      |}.
Proof.
  intros.
  unfold Z_of_string_loop.
             
   
Definition value_until j l := 
             (value (Z_of_string (sublist 0 j l))). 

Definition ASN1_INTMAX_MAX := Int64.max_unsigned.
Definition upper_boundary := Z.div ASN1_INTMAX_MAX 10.
Definition last_digit_max := Zmod ASN1_INTMAX_MAX 10.
Definition last_digit_max_minus := last_digit_max + 1.

Lemma lt_ub_bounded : forall j ls, 
    value_until j ls < upper_boundary -> 
    bounded (value_until (j + 1) ls) = true.
Abort.

Lemma value_always_bounded : forall j ls,
  0 <= j < Zlength ls ->
  bounded (value_until j ls) = true.
Abort.

Lemma next_value_plus:
  forall (ls : list byte) (j : Z) (b : byte),
    0 <= j ->
    j + 1 <= Zlength ls -> 
    Znth j ls = b ->
    ((Byte.signed b >=? 48) && (Byte.signed b <=? 57))%bool = true ->
    (value_until (j + 1) ls) =
    (value_until j ls * 10 + (Byte.signed b - 48)).
Abort.

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

 Lemma LI_to_spec_OK : forall i ls,
                  (forall i : Z, 0 <= i < Zlength ls -> is_digit (Znth i ls) = true) ->
                   ->
                  res (Z_of_string (i :: ls)) = ASN_STRTOX_OK.
                 Proof.
                   intros until ls; intro DIG.
                   simpl.
                   rewrite SIGN.
                   break_match; try  easy.
                   break_if.
                  
                   pose proof (DIG 0) as G.
                   assert (0 <= 0 < Zlength (i0 :: l)) as J by admit.
                   pose proof (G J).
                   replace (is_digit i0) with true.
                   replace (bounded (0 * 10 + Z_of_char i0))
                           with true.
                   simpl.

                   autorewrite with sublist.
                   admit.
                   
                   
                    
                   
                    

