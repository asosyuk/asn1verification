(* Abstract specification from the standard *)
Require Import Core.Core Core.Notations Core.Tactics Lib.Lib.
Require Import Lists.List Psatz.
Import ListNotations.
Require Import StructTact.StructTactics.

(* Tags 8.1.2 *)
(* ls#n is notation for ls[n]
   bs@n is notation for testing nth bit of bs*)

Inductive Tag : list byte -> Prop :=
(* 8.1.2.2 *)
(* tag number < 31 *)
| Low_tag t : t @ 7 = false -> Tag [t]
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

Inductive ByteList_Integer : Z -> list byte -> Prop :=
| Short_Int z b :
    z = Byte.unsigned b -> ByteList_Integer z [b]
| Long_Int z v b tl : 
    ByteList_Integer v tl ->
    z = Byte.unsigned b * 2^(8 * len tl) + v ->
    ByteList_Integer z (b :: tl).

(* Length 8.1.3 *)
Inductive Length : Z -> list byte -> Prop :=
(* 8.1.3.4 *)
| Definite_short_form l : 0 <= l < 127-> Length l [Byte.repr l]
(* 8.1.3.5 *)
| Definite_long_form z l ls : 0 < l < 127 ->
                            len ls = l ->
                            ByteList_Integer z ls ->
                            Length z (Byte.repr l::ls)
(* 8.1.3.6 *)
| Indefinite_form : Length 127 [Byte.repr 127].

Definition DefiniteLength z l := z <> 127 /\ Length z l. 

(* Primitive Values BER and DER encodings *)
Inductive BER_Bool : bool -> list byte -> Prop :=
| False_Bool : 
    BER_Bool false [all_zero]
| True_Bool b :
    b <> all_zero ->
    BER_Bool true [b].

Inductive DER_Bool : bool -> list byte -> Prop :=
| False_Bool_DER : 
    DER_Bool false [all_zero]
| True_Bool_DER :
    DER_Bool true [all_one].
              
Definition BER_Integer := ByteList_Integer.
Definition DER_Integer := BER_Integer.

Inductive BER_BitString_Primitive : list bool -> list byte -> Prop := 
| Primitive_BitString b bs i tl: 
    i = - (len bs) mod 8 ->
    len tl = len bs / 8 ->  
    (forall n, 0 <= n < len bs -> bs#n = (tl#(n / 8)) @ (n mod 8)) ->    
    Forall (fun u => u = false) b -> (* as per 8.6.2.4, remove some trailing 0 bits *) 
    BER_BitString_Primitive (bs ++ b) (Byte.repr i :: tl).

Inductive DER_BitString_Primitive : list bool -> list byte -> Prop := 
| Zero_BitString_DER bs:
    Forall (fun u => u = false) bs ->
    DER_BitString_Primitive bs [all_zero]

| Primitive_BitString_DER bs b i tl: 
    let bs' :=  bs ++ [true] in  (* as per 11.2.2, remove all trailing 0 bits *) 
    Forall (fun u => u = false) b ->
    i = - (len bs') mod 8 ->
    len tl = len bs' / 8 ->                
    (forall n, 0 <= n < len bs' -> bs'#n = (tl#(n / 8)) @ (n mod 8)) ->
    (forall k, 0 <= k <= i -> (tl#(len tl - 1)) @ k = false) ->   (* Unused bits set to 0: 11.2.1 *)
    DER_BitString_Primitive (bs ++ [true] ++ b) (Byte.repr i :: tl).

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

| Bitstring_Constructed_BER t l bs vs: 
    let v := flatten vs in
    let s := flatten bs in
    ConstructedTag t ->
    Length (len v) l ->
    (forall n, 0 <= n < len vs - 1 -> 
          len (bs#n) mod 8 = 0 ->
          BER (BIT_STRING (bs#n)) (vs#n)) ->
    BER (BIT_STRING s) (t ++ l ++ v)

| Sequence_BER t l ls vs:
    let v := flatten vs in
    ConstructedTag t ->
    Length (len v) l ->    
    len vs = len ls ->
    (forall n, n < len ls -> BER (ls#n) (vs#n)) ->
    BER (SEQUENCE ls) (t ++ l ++ v) 

| Set_BER t l ls vs vs':
    let v := flatten vs' in   
    ConstructedTag t ->
    Length (len v) l ->
    len vs = len ls ->
    (forall n, n < len ls -> BER (ls#n) (vs#n)) ->
    Permutation vs vs' ->
    BER (SET ls) (t ++ l ++ v)

| Choice_BER t l v s ls:
    In s ls ->
    BER s (t ++ l ++ v) ->
    BER (CHOICE ls) (t ++ l ++ v).

Inductive DER : asn_value -> list byte -> Prop :=
| Bool_DER b t v:
    PrimitiveTag t ->
    DER_Bool b v ->
    DER (BOOLEAN b) (t ++ [Byte.one] ++ v)
      
| Integer_short_DER t v z :
    PrimitiveTag t ->
    len v = 1 ->
    DER_Integer z v ->
    DER (INTEGER z) (t ++ [Byte.one] ++ v) 

| Integer_long_DER t l v z:
    PrimitiveTag t ->
    DefiniteLength (len v) l ->
    1 < len v ->
    v#1 <> all_one ->
    (v#1) @ 7 = true ->
    DER_Integer z v ->
    DER (INTEGER z) (t ++ l ++ v) 

| Bitstring_Primitive_DER t l v s: 
    PrimitiveTag t ->
    DefiniteLength (len v) l ->
    DER_BitString_Primitive s v ->
    DER (BIT_STRING s) (t ++ l ++ v)

| Sequence_DER t l ls vs:
    let v := flatten vs in
    ConstructedTag t ->
    DefiniteLength (len v) l ->    
    (forall n, n < len ls -> DER (ls#n) (vs#n)) ->
    DER (SEQUENCE ls) (t ++ l ++ v)

| Set_DER t l ls vs vs':
    let v := flatten vs' in   
    ConstructedTag t ->
    DefiniteLength (len v) l ->
    len vs = len ls ->
    (forall n, n < len ls -> BER (ls#n) (vs#n)) ->
    Permutation vs vs' ->
    DER (SET ls) (t ++ l ++ v)

| Choice_DER t l v s ls:
    In s ls ->
    DER s (t ++ l ++ v) ->
    DER (CHOICE ls) (t ++ l ++ v).

(* Correctness proofs *)
(* Definition byte_to_bool b : bool:= if (b == 0)%byte then false else true.

Definition ber_decoder (td : TYPE_descriptor) (ls : list byte) : err asn_value.
Admitted.

Theorem BOOL_decoder_correctness : forall td ls b, 
    type td = BOOLEAN_t -> 
    bool_decoder td ls = inr b ->
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
