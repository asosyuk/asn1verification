(* Abstract specification from the standard *)
(* "It is implicit in the specification of these encoding rules 
       that they are also used for decoding" *)
Require Import Core.Core Core.Notations.
Require Import Lists.List.
Import ListNotations.
Require Import ExecutableSpec.

(* Spec using bits *)
Definition bit := bool.
Inductive bit_word : nat -> Type  := 
  | empty : bit_word O
  | w n : bit -> bit_word n -> bit_word (S n).

Notation octet := (bit_word 8).

(* Declare Scope word_scope. *)
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

(* Fixpoint intlist_to_bytelist (l: list int) : list byte :=
 match l with
 | nil => nil
 | i::r =>
     Byte.repr (Int.unsigned (Shr 24 i)) ::
     Byte.repr (Int.unsigned (Shr 16 i)) ::
     Byte.repr (Int.unsigned (Shr 8 i)) ::
     Byte.repr (Int.unsigned i) ::
     intlist_to_bytelist r
 end. *)



(* Length encoding *)
(* for primitive types the length encoding is in definite form *)
Definition length z := if z <=? 127 
                       then [([[false]] ∘ (Z_to_bit_word 7 z))]
                       else let z := (Z_to_octet z) in
                            let len := Zlength z in
                            let l := Z_to_bit_word 7 len in
                            ([[true]] ∘ l) :: z.


Parameter Seq_type : Set.

Definition asn_type_denot (t : asn_type) :=
  match t with
  | BOOLEAN => bool
  | INTEGER => Z
  | SEQUENCE => Seq_type
  end.

Notation "' a" := (asn_type_denot a) (at level 50).

Inductive BER : forall (type : asn_type), 'type -> list octet -> Prop :=
  | False_BER (t l : Z) (tc : tag_class) :
      BER BOOLEAN false (tag t tc primitive_type ++ (length l) ++ [all_zero])  
       
  | True_BER (t l : Z) (tc : tag_class) (o : octet) :
      o <> all_zero ->
      BER BOOLEAN true (tag t tc primitive_type ++ (length l) ++ [o]). 

Inductive DER : forall (type : asn_type), 'type -> list octet -> Prop :=
  | False_DER (t l : Z) (tc : tag_class) :
      DER BOOLEAN false (tag t tc primitive_type ++ (length l) ++ [all_zero])  
       
  | True_DER (t l : Z) (tc : tag_class) :
      DER BOOLEAN true (tag t tc primitive_type ++ (length l) ++ [all_one]). 


Definition byte_to_bool b := if (b == 0)%byte then false else true.
Definition byte_to_octet (b : byte) : octet. 
Admitted.

Parameter octet_to_byte : octet -> byte. 
Coercion byte_to_octet : byte >-> octet.

Parameter seq_decoder : TYPE_descriptor -> err (list byte).

(* Definition ber_decoder td ls : err ('type td) := 
  match type td with
    | BOOLEAN => bool_prim_decoder td ls
    | INTEGER => bool_prim_decoder td ls
    | SEQUENCE => bool_prim_decoder td ls
  end. *)

Definition ber_decoder td (ls : list byte) : err ('type td).
Admitted.

Theorem decoder_correctness : forall td ls (b : 'type td), 
    ber_decoder td ls = inr b ->
    BER (type td) b (map byte_to_octet ls).
Admitted.


Theorem decoder_completeness :  forall td ls (b : 'type td), 
    BER (type td) b ls ->
    ber_decoder td (map octet_to_byte ls) = inr b.
Admitted.

Theorem decoder_completeness_false : forall td ls, 
    type td = BOOLEAN -> 
    BER BOOLEAN false ls ->
    bool_prim_decoder td (map octet_to_byte ls) = inr Byte.zero.
Admitted.

Theorem decoder_completeness_true : forall td ls b, 
    type td = BOOLEAN -> 
    BER BOOLEAN true ls ->
    b <> Byte.zero ->
    bool_prim_decoder td (map octet_to_byte ls) = inr b.
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
    BER (type td) b (map byte_to_octet (ber_encoder td b)).
Admitted.

(* Fixpoint read_tag (ol: list octet) (ls : list bit) :=
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

*)


