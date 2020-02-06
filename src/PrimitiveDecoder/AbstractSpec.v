(* Abstract specification from the standard *)
(* "It is implicit in the specification of these encoding rules 
       that they are also used for decoding" *)
Require Import Core.Core.
Import ListNotations.

Definition bit := bool.
Inductive bit_word : nat -> Type  := 
  | empty : bit_word O
  | w n : bit -> bit_word n -> bit_word (S n).

Notation octet := (bit_word 8).

(* end of contents depends on length *)
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
Parameter high : nat -> octet -> list bit.
(* First n bits of the octet *)
Parameter low : nat -> octet -> list bit.

(* tag encoding rules 8.1.2 *)

Definition tag_class := bit_word 2.
Definition encoding_type := bit_word 1.

Fixpoint copy n (b : bit) :=
  match n with
  | O => [[]]
  | S n => b:copy n b
  end.

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

Parameter Z_to_octet : Z -> list octet.
(* separate z into octets and add leading 1s and 0s, as per 8.1.2.4.2 b:
b) bits 7 to 1 of the first subsequent octet, followed by bits 7 to 1 of the second subsequent octet, followed
in turn by bits 7 to 1 of each further octet, up to and including the last subsequent octet in the identifier
octets shall be the encoding of an unsigned binary integer equal to the tag number, with bit 7 of the first
subsequent octet as the most significant bit; 

*)

Parameter make_tag : Z -> list octet -> list octet.

Fixpoint tag_number (z : Z) :=
  if z <=? 30
  then Z_to_octet z
  else let n := z / 7 in
       let z := Z_to_octet z  in
       (copy 8 true) :: make_tag n z.


Definition big_tag (tg: tag_class) (et: encoding_type) (z : Z) := tg ∘ et ∘ (copy 8 true).
Definition small_tag (tg: tag_class) (et: encoding_type) (t : octet) := tg ∘ et ∘ t.
Parameter bit_to_Z : list bit -> Z.

Definition tag_to_Z (ol : list octet) := bit_to_Z (read_tag ol []).

