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
Definition nth n ls := nth n ls default_byte.

Inductive Tag : list byte -> Prop :=
(* 8.1.2.2 *)
(* tag number < 31 *)
| Low_tag t : Byte.testbit t 0 = false -> Tag [t]

(* 8.1.2.4 *)
(* tag number >= 31 *)
| High_tag t ls : forall n,
    (* 1st octet *)
    (0 <= n <= 5 -> Byte.testbit t n = true) ->
    (* subsequent octets representing the tag number *)
    (forall m, (0 <= m < (length ls - 1))%nat -> 
          Byte.testbit (nth m ls) 7 = true) ->
    Byte.testbit (nth (length ls - 1) ls) 7 = false ->
    nth 0 ls <> all_zero ->
    Tag (t::ls). 

Parameter Seq_type : Set.

Definition asn_type_denot (t : asn_type) :=
  match t with
  | BOOLEAN => bool
  | INTEGER => Z
  | SEQUENCE => Seq_type
  end.

Notation "' a" := (asn_type_denot a) (at level 50).


Definition PrimitiveTag t := let t' := hd Byte.zero t in
                             Byte.testbit t' 6 = false /\ Tag t.

Definition DefiniteLength z l := l <> [Byte.repr 127] /\ Length z l. 

Definition byte_to_Z (b : byte) (z : Z) :=
  2^z * (Byte.unsigned b).

Definition bytes_to_Z (ls : list byte) :=
  (fix bytes_to_Z_loop ls z :=
    match ls with 
    | [] => z
    | [h] => byte_to_Z h z 
    | h :: tl => byte_to_Z h z + (bytes_to_Z_loop tl (z + 8))
    end) (rev ls) 0. 

Inductive BER : forall (type : asn_type), 'type -> list byte -> Prop :=
| False_BER t:
    PrimitiveTag t ->
    BER BOOLEAN false (t ++ [1%byte] ++ [all_zero])
       
| True_BER t v :
    v <> all_zero ->
    PrimitiveTag t ->
    BER BOOLEAN true (t ++ [1%byte] ++ [v])

| Integer_short_BER t l v vz :
    PrimitiveTag t ->
    Length 1 l ->
    Zlength v = 1 ->
    bytes_to_Z v = vz ->
    BER INTEGER vz (t ++ l ++ v)

| Integer_long_BER t l lz v vz:
    PrimitiveTag t ->
    Length lz l ->
    Zlength v = lz ->
    1 < lz ->
    nth 0 v <> all_one ->
    Byte.testbit (nth 1 v) 7 = true ->
    bytes_to_Z v = vz ->
    BER INTEGER vz (t ++ l ++ v).

(* Correctness proofs *)

Definition byte_to_bool b : 'BOOLEAN := if (b == 0)%byte then false else true.

Definition ber_decoder td (ls : list byte) : err ('type td).
(* Definition ber_decoder td ls : err ('type td) := 
  match type td with
    | BOOLEAN => bool_prim_decoder td ls
    | INTEGER => bool_prim_decoder td ls
    | SEQUENCE => bool_prim_decoder td ls
  end. *)
Admitted.

Theorem BOOL_decoder_correctness : forall td ls b, 
    type td = BOOLEAN -> 
    bool_prim_decoder td ls = inr b ->
    BER BOOLEAN (byte_to_bool b) ls.
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

Theorem decoder_correctness : forall td ls (b : 'type td), 
    ber_decoder td ls = inr b ->
    BER (type td) b ls.
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


