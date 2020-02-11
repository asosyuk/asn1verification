(* Abstract specification from the standard *)
(* "It is implicit in the specification of these encoding rules 
       that they are also used for decoding" *)
Require Import Core.Core. 
Require Import Lists.List.
Import ListNotations.

Definition bit := bool.
Inductive bit_word : nat -> Type  := 
  | empty : bit_word O
  | w n : bit -> bit_word n -> bit_word (S n).

Notation octet := (bit_word 8).

Declare Scope word_scope.
Notation "[[ ]]" := empty (format "[[ ]]") : word_scope.
Notation "[[ x ]]" := (w _ x empty) : word_scope.
Notation "[[ x ; y ; .. ; z ]]" := (w _ x (w _ y .. (w _ z empty) ..)) : word_scope.
Infix ":" := (w _) (at level 60, right associativity) : word_scope.
Definition cat {n1} {n2} (w1 : bit_word n1) (w2 : bit_word n2) : bit_word (n1 + n2).
Admitted.

Infix "∘" := cat (at level 60, right associativity) : word_scope.
Open Scope word_scope.

Parameter nth_bit : nat -> octet -> bit.
(* Last n bits of the octet *)
Definition high n : forall m, bit_word m -> bit_word n.
Admitted.
(* First n bits of the octet *)
Definition low n : forall m, bit_word m -> bit_word n.
Admitted.

(* tag encoding rules 8.1.2 *)

Definition tag_class := bit_word 2.

Definition universal_class := [[false; false]].
Definition application_class := [[false; true]].
(* etc *)

Definition encoding_type := bit_word 1.

Definition primitive_type := [[false]].
Definition constructed_type := [[true]].

Fixpoint copy n (b : bit) :=
  match n with
  | O => [[]]
  | S n => b:copy n b
  end.

Definition all_zero : octet := copy 8 false.
Definition all_one : octet := copy 8 true.

(* convert integer into octets according to 8.1.2.4.1-2 *)
Definition Z_to_bit_word n : Z -> bit_word n.
Admitted.
Parameter Z_to_octet : Z -> list octet.

Definition big_tag z (tg: tag_class) (et: encoding_type) := 
  (tg ∘ et ∘ (copy 5 true))::(Z_to_octet z).

Definition small_tag (t : bit_word 5) (tg : tag_class) (et : encoding_type)  :=
  [tg ∘ et ∘ t].

Definition tag z := if z <=? 30 
                    then small_tag (Z_to_bit_word 5 z)
                    else big_tag z.

(* Length encoding *)
(* for primitive types the length encoding is in definite form *)
Definition length z := if z <=? 127 
                       then [([[false]] ∘ (Z_to_bit_word 7 z))]
                       else let z := (Z_to_octet z) in
                            let len := Zlength z in
                            let l := Z_to_bit_word 7 len in
                            ([[true]] ∘ l) :: z.

Inductive bool_BER : bool -> list octet -> Prop:=
  | False_BER (t l : Z) (tc : tag_class) :
      bool_BER false (tag t tc primitive_type ++ (length l) ++ [all_zero])  
       
  | True_BER (t l : Z) (tc : tag_class) (o : octet) :
      o <> all_zero ->
      bool_BER true (tag t tc primitive_type ++ (length l) ++ [o]). 

Inductive bool_DER : bool -> list octet -> Prop:=
  | False_DER (t l : Z) (tc : tag_class) :
      bool_DER false (tag t tc primitive_type ++ (length l) ++ [all_zero])  
       
  | True_DER (t l : Z) (tc : tag_class) :
      bool_DER true (tag t tc primitive_type ++ (length l) ++ [all_one]). 

Parameter ber_decode_bool : list octet -> option bool.
Parameter der_encode_bool : bool-> list octet.

Theorem roundtrip : forall ls b, ber_decode_bool (der_encode_bool b) = Some b.
(* Yes *)
 
Theorem encoder_correctness : BER_bool b (ber_encode_bool ls).

Theorem decoder_correctness_left : forall ls b, ber_decode_bool ls = Some b -> BER_bool b ls.
(* No, since ber_decode_bool (tag ∘ 02 ∘ ...) = Some b *)
 
Theorem decoder_correctness_right : BER_bool b ls -> ber_decode_bool ls = Some b.
(* Yes *)


Fixpoint read_tag (ol: list octet) (ls : list bit) :=
  match ol with
  | [] => ls
  | h :: tl => let z := high 7 h in 
             match nth_bit 0 h with
             (* last tag octet *)
             | false => ls++z
             (* continue *)
             | true => read_tag tl z
             end
  end.


Parameter make_tag : Z -> list octet -> list octet.

Fixpoint tag_number (z : Z) :=
  if z <=? 30
  then Z_to_octet z
  else let n := z / 7 in
       let z := Z_to_octet z  in
       (copy 8 true) :: make_tag n z.


Parameter bit_to_Z : list bit -> Z.

Definition tag_to_Z (ol : list octet) := bit_to_Z (read_tag ol []).

