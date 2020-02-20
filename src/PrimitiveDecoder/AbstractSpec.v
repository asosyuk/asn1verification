(* Abstract specification from the standard *)
Require Import Core.Core Core.Notations.
Require Import Lists.List Psatz.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import ExecutableSpec.

(* ASN.1 types and values *)

Inductive asn_value :=
  | ANY : asn_value
  | BOOLEAN : bool -> asn_value 
  | INTEGER : Z -> asn_value
  | BIT_STRING : list bool -> asn_value
  | SEQUENCE : list asn_value -> asn_value. 

Instance Nth_Asn_value : Nth asn_value :=
  { default := ANY ;
    n_th := fun n ls => nth (Z.to_nat n) ls ANY;
    hd_nth := fun ls => List.hd ANY ls
 }.

(* Spec using bytes *)
(* Tags 8.1.2 *)
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
     ls#0 <> all_zero ->  
    (forall m, m < len ls - 1 -> (ls#m) @ 7 = true) ->
    (ls#(len ls - 1)) @ 7 = false ->
    
    Tag (t::ls). 

Definition PrimitiveTag t := (hd_nth t) @ 6 = false /\ Tag t.

Definition ConstructedTag t := (hd_nth t) @ 6 = true /\ Tag t.

(* Length 8.1.3 *)
Inductive Length : Z -> list byte -> Prop :=
(* 8.1.3.4 *)
| Definite_short_form l : 0 <= l < 127-> Length l [Byte.repr l]
(* 8.1.3.5 *)
| Definite_long_form l ls : 127 < l < 255 -> Length l (Byte.repr (len ls)::ls)
(* 8.1.3.6 *)
| Indefinite_form : Length 127 [Byte.repr 127].

Definition DefiniteLength z l := z <> 127 /\ Length z l. 

(* Primitive Values BER encodings *)
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
    BER_Integer z (b :: tl).

Inductive BER_BitString_Primitive : list bool -> list byte -> Prop := 
| Primitive_BitString bs i tl: 
    i = - (len bs) mod 8 ->
    (forall n, 0 <= n < len bs ->
          bs # n = (tl#(n / 8)) @ (n mod 8)) ->
    BER_BitString_Primitive bs (Byte.repr i :: tl)
(* as per 8.6.2.4, remove trailing 0 bits *) 
| Named_BitString bs i tl:
    BER_BitString_Primitive (bs ++ [false]) (i :: tl) ->
    BER_BitString_Primitive (bs ++ [false]) ((i - 1)%byte :: tl).

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
    v#1 <> all_one ->
    (v#1) @ 7 = true ->
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
    (forall n, n < len vs - 1 ->
          vs#0 = [all_zero] -> 
        BER (BIT_STRING (bs#n)) (vs#n)) ->
    BER (BIT_STRING (flatten bs)) (t ++ l ++ v)

| Sequence_BER t l v ls vs:
    ConstructedTag t ->
    Length (len v) l ->
    v = flatten vs ->
    (forall n, BER (ls#n) (vs#n)) ->
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
