(* Abstract specification from the standard *)
Require Import Core.Core Core.Notations.
Require Import Lists.List Psatz.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import ExecutableSpec.

(* Spec using bytes *)

Definition all_zero : byte := Byte.zero.
Definition all_one : byte := Byte.repr (Byte.max_unsigned).

Inductive Length : Z -> list byte -> Prop :=
(* 8.1.3.4 *)
| Definite_short_form l : (0 <= l < 127)%Z -> Length l [Byte.repr l]
(* 8.1.3.5 *)
| Definite_long_form l ls : (127 < l < 255)%Z -> Length l (Byte.repr (Zlength ls)::ls)
(* 8.1.3.6 *)
| Indefinite_form : Length 127 [Byte.repr 127].

Definition default_byte := all_zero.
Definition get_byte n ls := nth n ls default_byte.
Definition hd ls := hd all_zero ls.
Notation "t @ n" := (Byte.testbit t n) (at level 50).

Inductive Tag : list byte -> Prop :=
(* 8.1.2.2 *)
(* tag number < 31 *)
| Low_tag t : t @ 0 = false -> Tag [t]
(* 8.1.2.4 *)
(* tag number >= 31 *)
| High_tag t ls : forall n,
    (* 1st octet *)
    (0 <= n <= 5 -> t @ n = true) ->
    (* subsequent octets representing the tag number *)
    get_byte 0 ls <> all_zero ->  
    (forall m, (m < (length ls - 1))%nat -> (get_byte m ls) @ 7 = true) ->
    (get_byte (length ls - 1) ls) @ 7 = false ->
    
    Tag (t::ls). 

Reserved Notation "' a" (at level 50).

Inductive asn_value :=
  | BOOLEAN : bool -> asn_value 
  | INTEGER : Z -> asn_value
  | SEQUENCE : list asn_value -> asn_value. 

Definition PrimitiveTag t := (hd t) @ 6 = false /\ Tag t.
Definition ConstructedTag t := (hd t) @ 6 = true /\ Tag t.

Definition DefiniteLength z l := l <> [Byte.repr 127] /\ Length z l. 

(* Integer encoding *)

Definition Z_of_byte (b : byte) (z : Z) :=
  2^z * (Byte.unsigned b).

Definition Z_of_bytes (ls : list byte) :=
  (fix bytes_to_Z_loop ls z :=
    match ls with 
    | [] => z
    | [h] => Z_of_byte h z 
    | h :: tl => Z_of_byte h z + (bytes_to_Z_loop tl (z + 8))
    end) (rev ls) 0. 

Parameter bytes_of_Z : Z -> list byte.

Hypothesis Z_to_bytes_roundtrip : forall z, Z_of_bytes (bytes_of_Z z) = z.

Definition flatten {A} l := fold_right (@app _) (@nil A) l.

Inductive BER : asn_value -> list byte -> Prop :=
| False_BER t:
    PrimitiveTag t ->
    BER (BOOLEAN false) (t ++ [1%byte] ++ [all_zero])
       
| True_BER t v :
    v <> all_zero ->
    PrimitiveTag t ->
    BER (BOOLEAN true) (t ++ [1%byte] ++ [v])

| Integer_short_BER t l v z :
    PrimitiveTag t ->
    Length 1 l ->
    Zlength v = 1 ->
    Z_of_bytes v = z ->
    BER (INTEGER z) (t ++ l ++ v)

| Integer_long_BER t l v z:
    PrimitiveTag t ->
    Length (Zlength v) l ->
    1 < (Zlength v) ->
    get_byte 0 v <> all_one ->
    (get_byte 1 v) @ 7 = true ->
    Z_of_bytes v = z ->
    BER (INTEGER z) (t ++ l ++ v) 

| Sequence_BER t l v ls vs:
    ConstructedTag t ->
    Length (Zlength v) l ->
    v = flatten vs ->
    (forall n ln vn, (n < length vs)%nat ->
          nth_error ls n = Some ln ->
          nth_error vs n = Some vn ->
          BER ln vn) ->
    BER (SEQUENCE ls) (t ++ l ++ v).

(* Correctness proofs *)
Definition byte_to_bool b : bool:= if (b == 0)%byte then false else true.

Definition ber_decoder (td : TYPE_descriptor) (ls : list byte) : err asn_value.
Admitted.

Theorem BOOL_decoder_correctness : forall td ls b, 
    type td = BOOLEAN_t -> 
    bool_prim_decoder td ls = inr b ->
    BER (BOOLEAN (byte_to_bool b)) ls.
Proof.
  intros.
  destruct (byte_to_bool b) eqn : S.
  unfold byte_to_bool in *.
  break_if; try congruence.
  unfold bool_prim_decoder in *.
  break_match; try discriminate.
  simpl in *.
  repeat break_match; try congruence.
  inversion H0.
  unfold bool_content_decoder in *.
  break_match.
  inversion H0.
  admit.
Admitted.

(* 
Theorem decoder_correctness : forall td ls b, 
    ber_decoder td ls = inr b ->
    BER (type td b) ls.
Admitted.


Theorem decoder_completeness :  forall td ls (b : 'type td), 
    BER (type td) b ls ->
    ber_decoder td ls = inr b.
Admitted.

Theorem decoder_completeness_false : forall td ls, 
    type td = BOOLEAN -> 
    BER BOOLEAN false ls ->
    bool_prim_decoder td ls = inr Byte.zero.
Admitted.

Theorem decoder_completeness_true : forall td ls b, 
    type td = BOOLEAN -> 
    BER BOOLEAN true ls ->
    b <> Byte.zero ->
    bool_prim_decoder td ls = inr b.
Admitted.

Parameter int_to_byte : int -> byte.
Parameter bool_to_int : bool -> int.

Theorem roundtrip : forall td b, 
    type td = BOOLEAN -> 
    bool_prim_decoder td (bool_prim_encoder td b) 
                               = inr (int_to_byte b).
Admitted.

Definition ber_encoder td (b : 'type td) : list byte. 
Admitted.
 
Theorem encoder_correctness : forall td (b : 'type td), 
    BER (type td) b (ber_encoder td b).
Admitted.

*)
