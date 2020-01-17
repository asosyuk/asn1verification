Require Import Nat List ZArith Decimal DecimalNat List Lia.
Import ListNotations.

From compcert Require Import Integers.

  Open Scope Z.

Inductive asn_value := OK | ERROR.

Parameter byte_to_nat : byte -> nat.

Section Tables.

Inductive TYPE_descriptor :=
  { tags : list Z ;
    elements : list TYPE_descriptor ;
  }.

(* Primitive types *)

(* read until the end of the data *)
Definition primitive_decoder (input : list Z) := true.
 
Open Scope Z.
               
Definition BOOLEAN := {| tags := [1];
                         elements := [] |}.

Definition INTEGER := {| tags := [2];
                         elements := [] |}.

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
  | DEC  (l : Z) (v : list Z)
  | RES (r : bool).
  
  Reserved Notation "st1 -[ c ]-> st2" (at level 50).
  
  Inductive PRIM_next : PRIM_state -> Z -> PRIM_state -> Prop :=
  | read_tag t X : 
      In t (tags X) ->
      INIT X -[ t ]-> TAG 
  | read_prim_length l : 
      (* primitive X = true -> *)
      TAG  -[ l ]-> DEC l []
  | read_value l vl v : 
      1 < l ->
      DEC l vl -[ v ]-> DEC (l-1) (v::vl) 
  | call_prim_decoder vl v: 
      DEC 1 vl -[ v ]-> RES (primitive_decoder (v::vl))   
  | read_constr_length l X Y n: 
      (n < length (elements X))%nat ->
      nth n%nat (elements X) X = Y ->
      (* primitive X = false -> *)
      TAG -[ l ]-> INIT Y 

  where "st1 -[ c ]-> st2" := (PRIM_next st1 c st2).

  Definition PRIM_fsa X := {| initial := INIT X ; 
                              next := PRIM_next |}.

  Definition PRIM_star X := fsa_run (PRIM_fsa X).
     
End PRIM_automaton.

Section ExampleTYPE.

  Definition n1 := {| tags := [2]; elements := [] |}.
  Definition n2 := {| tags := [2]; elements := [] |}.
  Definition b1 := {| tags := [1]; elements := [] |}.  
  Definition Sb := {| tags := [30]; elements := [b1] |}.                     
  Definition Snb := {| tags := [30]; elements := [n1; n2; Sb] |}.

  Definition check_tag t ts := if existsb (fun l => l =? t) ts
                                then true
                                else false.
  

  Fixpoint seq_decoder (X : TYPE_descriptor) (ls : list Z) :=
    match ls with
    | [] => true 
    | b :: bs =>          
      if check_tag b (tags X)
        then
          match elements X with
          | [] => primitive_decoder bs 
          | es =>
            if forallb (fun x => x)
                       ((fix list_seq_decoder XS :=
                           match XS with
                           | [] => []
                           | X :: XS => (seq_decoder X bs) :: list_seq_decoder XS
                           end) es)
            then true
            else false
          end
        else false
    end.
          
  Compute (seq_decoder Sb [30;1]).
  Compute (seq_decoder Snb [30;2;30;1]).

  (* problem with 1st primitive then constructed: need to output rest of the list *)
  
