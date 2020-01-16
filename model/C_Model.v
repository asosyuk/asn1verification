Require Import Nat List ZArith Decimal DecimalNat List Lia.
Import ListNotations.

From compcert Require Import Integers.

Inductive asn_value := OK | ERROR.

Parameter byte_to_nat : byte -> nat.

Section Tables.

Inductive TYPE_descriptor :=
  { primitive : bool ;
    tags : list Z ;
    elements : list TYPE_descriptor ;
    decoder : list byte -> asn_value ;
  }.

(* Primitive types *)

(* read until the end of the data *)
Definition primitive_decode (input : list byte) := OK.
 
Open Scope Z.
               
Definition BOOLEAN := {| primitive := true;
                         tags := [1];
                         elements := [];
                         decoder := primitive_decode;
                      |}.

Definition INTEGER := {| primitive := true;
                         tags := [2];
                         elements := [];
                         decoder := primitive_decode;

                      |}.

End Tables.

Section PRIM_automaton.

  Set Implicit Arguments.

  Record fsa (S A : Type) := FSA {
                                 initial : S;
                                 next : S -> A -> S -> Prop
                               }.

  Inductive fsa_run {S A : Type } (m : fsa S A) : list A -> S -> Prop :=
  | step : forall a s, next m (initial m) a s -> fsa_run m [a] s
  | trans : forall s1 a s2 l rs, next m s1 a s2 -> fsa_run m l rs -> fsa_run m (a::l) rs.

  Inductive PRIM_state :=
  | INIT (X : TYPE_descriptor)
  | TAG
  | DEC  (l : nat) (v : list byte)
  | RES (r : asn_value).
  
  Reserved Notation "st1 -[ c ]-> st2" (at level 50).
  
  Inductive PRIM_next : PRIM_state -> byte -> PRIM_state -> Prop :=
  | check_tag t X : 
      In (Byte.unsigned t) (tags X) ->
      INIT X -[ t ]-> TAG 
  | read_prim_length l X : 
      primitive X = true ->
      TAG  -[ l ]-> DEC (byte_to_nat l) []
  | read_value l vl v : 
      1 < l ->
      DEC l vl -[ v ]-> DEC (l-1)%nat (v::vl) 
  | call_prim_decoder vl v X: 
      DEC 1 vl -[ v ]-> RES (decoder X (v::vl))   
  | read_constr_length l X Y n: 
      n < length (elements X) ->
      nth n (elements X) X = Y ->
      primitive X = false ->
      TAG -[ l ]-> INIT Y 

  where "st1 -[ c ]-> st2" := (PRIM_next st1 c st2).

  Definition PRIM_fsa X := {| initial := INIT X ; 
                              next := PRIM_next |}.

  Definition PRIM_star X := fsa_run (PRIM_fsa X).
     
End PRIM_automaton.


