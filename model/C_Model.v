Require Import Nat List ZArith Decimal DecimalNat List Lia.
Import ListNotations.

Definition bit := bool.

Inductive bit_word : nat -> Type  := 
  | empty : bit_word O
  | w n : bool -> bit_word n -> bit_word (S n).

Definition octet := bit_word 8.
 
Inductive asn_value := OK | MORE | ERROR.

Parameter bit_word_to_nat : forall n, bit_word n -> nat.

Section Tables.

Inductive TYPE_descriptor :=
  { id : nat ;
    primitive : bool ;
    tags : list nat ;
    elements : list TYPE_descriptor ;
    decoder : nat -> list bit -> asn_value ;
  }.

(* Primitive types *)

(* read until the end of the data, otherwise MORE error *)
Definition primitive_decode (len : nat) (input : list bit) :=
  if len <=? length input then OK else MORE.
 
               
Definition BOOLEAN := {| id := 1;
                         primitive := true;
                         tags := [1];
                         elements := [];
                         decoder := primitive_decode;
                      |}.

Definition INTEGER := {| id := 2;
                         primitive := true;
                         tags := [2];
                         elements := [];
                         decoder := primitive_decode;
                      |}.

Parameter bits_to_nat : list bit -> nat.

(* Check if tag is among allowed tags for this structure *)
Definition check_tag (input : list bit) (DEF : TYPE_descriptor) :=
  existsb (fun z => z =? (bits_to_nat input)) (tags DEF).

End Tables.

Section PRIM_automaton.

  Set Implicit Arguments.

  Inductive PRIM_state :=
  | INIT
  | TAG
  | LEN (n : nat) (* store length *)
  | DEC (l : nat) (v : bit_word l). (* store value *)
  
  Reserved Notation "st1 -[ c ]-> st2" (at level 50).
  
  Inductive PRIM_next : PRIM_state -> forall n, bit_word n -> PRIM_state -> Prop :=
  | read_tag : forall t : bit_word 8,
      INIT -[ t ]-> TAG
  | read_length : forall l : bit_word 8,
      TAG -[ l ]-> LEN (bit_word_to_nat 8 l)
  | read_value : forall l (v : bit_word l), LEN l -[ v ]-> DEC v                    

  where "st1 -[ c ]-> st2" := (PRIM_next st1 c st2).

  Parameter bit_concat : forall {n} {m}, bit_word n -> bit_word m -> bit_word (n + m).

  Notation "a ∘ b" := (bit_concat a b) (at level 25).

  Reserved Notation "st1 -[ c ]*-> st2" (at level 50).

  Inductive PRIM_star : PRIM_state -> forall n, bit_word n -> PRIM_state -> Prop :=
  | base :  forall t : bit_word 8, INIT -[ t ]*-> TAG
  | step :  forall s1 s2 s3
              n1 (w1 : bit_word n1) 
              n2 (w2 : bit_word n2),
      s1 -[ w1 ]*-> s2 -> s2 -[ w2 ]-> s3 -> s1 -[ w1 ∘ w2 ]*-> s3
 
 where "st1 -[ c ]*-> st2" := (PRIM_star st1 c st2).
    
End PRIM_automaton.


