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
Notation len a := (Zlength a).

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


Inductive asn_value :=
  | BOOLEAN : bool -> asn_value 
  | INTEGER : Z -> asn_value
  | BIT_STRING : list bool -> asn_value
  | SEQUENCE : list asn_value -> asn_value. 

Definition PrimitiveTag t := (hd t) @ 6 = false /\ Tag t.
Definition ConstructedTag t := (hd t) @ 6 = true /\ Tag t.
Definition DefiniteLength z l := z <> 127 /\ Length z l. 

(* Boolean and Integer BER encodings *)

Inductive BER_Bool : bool -> list byte -> Prop :=
| False_Bool : 
    BER_Bool false [all_zero]
| True_Bool b :
    b <> all_zero ->
    BER_Bool true [b].

Inductive BER_Integer : Z -> list byte -> Prop :=
| Short_Int z b :
    z = Byte.unsigned b ->
    BER_Integer z [b]
| Long_Int z v b tl : 
    BER_Integer v tl ->
    z = Byte.unsigned b * 2^(8 * len tl) + v ->
    BER_Integer z (b::tl).

Definition flatten {A} l := fold_right (@app _) (@nil A) l.

Inductive BER_BitString_Primitive : list bool -> list byte -> Prop := 
| Empty_BitString : BER_BitString_Primitive [] [all_zero]
| Primitive_BitString i bs tl: 
    i = - (len bs) mod 8 ->
    (forall n b lb, (n < length bs)%nat ->
               nth_error bs n = Some b ->
               nth_error tl (n/8) = Some lb ->
               b = lb @ (Z.of_nat n) mod 8) ->
    BER_BitString_Primitive bs (Byte.repr i::tl).

Notation ϵ := EmptyString.
Parameter BER_OctetString : string -> list byte -> Prop.
  
Inductive BER : asn_value -> list byte -> Prop :=
| Bool_BER b t v:
    PrimitiveTag t ->
    BER_Bool b v ->
    BER (BOOLEAN b) (t ++ [Byte.one] ++ v)
      
| Integer_short_BER t v z :
    PrimitiveTag t ->
    len v = 1 ->
    BER_Integer z v ->
    BER (INTEGER z) (t ++ [Byte.one] ++ v) 

| Integer_long_BER t l v z:
    PrimitiveTag t ->
    DefiniteLength (len v) l ->
    1 < len v ->
    get_byte 0 v <> all_one ->
    (get_byte 1 v) @ 7 = true ->
    BER_Integer z v ->
    BER (INTEGER z) (t ++ l ++ v) 

| Bitstring_Primitive_BER t l v s: 
    PrimitiveTag t ->
    DefiniteLength (len v) l ->
    BER_BitString_Primitive s v ->
    BER (BIT_STRING s) (t ++ l ++ v)

| Bitstring_Constructed_BER t l v bs vs: 
    ConstructedTag t ->
    Length (len v) l ->
    v = flatten vs ->
    (forall n bn vn, 
        (n < length vs - 1)%nat ->
        nth_error bs n = Some bn ->
        nth_error vs n = Some vn ->
        (* TODO: check with 8.6.4 *)
        nth_error vn 0 = Some all_zero -> 
        BER (BIT_STRING bn) vn) ->
    BER (BIT_STRING (flatten bs)) (t ++ l ++ v)

| Sequence_BER t l v ls vs:
    ConstructedTag t ->
    Length (len v) l ->
    v = flatten vs ->
    (forall n ln vn, nth_error ls n = Some ln ->
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
