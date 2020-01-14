Require Import Nat List ZArith Decimal DecimalNat List Lia String.
Import ListNotations.
Open Scope Z.

Section Tables.

Definition bit := bool.

Inductive ber_input :=
  | prim_input : nat -> nat -> list bit -> ber_input
  | const_input : nat -> nat -> list ber_input -> ber_input.
  
Check (const_input 16 3 [prim_input 1 1 [true]]).

Inductive asn_value := OK | ERROR.

(* read until the end of the data, otherwise error *)
Fixpoint primitive_decode (len : nat) (input : list bit) :=
  match len, input with
  | O, _ => OK
  | S n, [] => ERROR
  | S n, hd :: tl => primitive_decode n tl
  end.

Fixpoint decode (input : ber_input) :=
  match input with
  | prim_input tag len ls => primitive_decode len ls
  | const_input tag len ls => match ls with 
                             | [] => OK
                             | hd :: tl => decode hd 
                             end
  end.

Parameter context : Type.

Definition tag := Z.

Record seq_specifics := {
                         ctx : context ; 
                         tag_to_el : tag -> nat  
                       }.

Inductive TYPE_descriptor :=
  { name : string ;
    tags : list Z ;
    elements : list TYPE_member ;
    decode : list bit -> nat -> asn_value ;
    seq_specs : list seq_specifics
  }
    with TYPE_member :=
           { mem_tag : Z*Z ; (* tag and flag: implicit *)
             type : TYPE_descriptor ;
           }.

(* Primitive types *)

                               
Definition BOOLEAN := {| name := "BOOLEAN";
                         tags := [1];
                         elements := [];
                         decode := primitive_decode;
                         seq_specs := []
                      |}.

Definition INTEGER := {| name := "INTEGER";
                         tags := [2];
                         elements := [];
                         decode := primitive_decode;
                         seq_specs := []
                      |}.

(* Constructed types *)
  

Fixpoint seq_decode (input : list bit) (DEF : TYPE_descriptor) (len : nat) : asn_value 
  :=  match elements DEF with
      | [] => OK
      | hd :: tl => (decode (type hd)) input len 
      end. 

End Tables.

(*
Set Implicit Arguments.

Record fsa (S A : Type) := FSA {
                               initial : S;
                               next : S -> A -> S -> Prop
                             }.

Inductive fsa_run {S A : Type } (m : fsa S A) : list A -> S -> Prop :=
| step : forall a s, m.(next) m.(initial) a s -> fsa_run m [a] s
| trans : forall s1 a s2 l rs, m.(next) s1 a s2 -> fsa_run m l rs -> fsa_run m (a::l) rs.

Section BOOL_automaton.

  Inductive BOOL_state :=
  | INIT
  | LEN
  | FALSE (z : Z)
  | TRUE (z : Z).
  
  Reserved Notation "st1 -[ c ]-> st2" (at level 50).
  
  Inductive BOOL_next : BOOL_state -> Z -> BOOL_state -> Prop :=
  | read_tag :
      INIT -[1]-> LEN
  | read_length l:
      LEN -[l]-> FALSE l
  | read_zero l :
      l > 0 ->
      FALSE l -[0]-> FALSE (l-1)
  | read_nonzero l k :
      l > 0 ->
      k > 0 ->
      FALSE l -[k]-> TRUE (l-1)
                                  
  where "st1 -[ c ]-> st2" := (BOOL_next st1 c st2).
    
  Definition BOOL_fsa := {| initial := INIT ;
                            next := BOOL_next |}.
End BOOL_automaton.
*)
