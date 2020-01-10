Require Import Nat List ZArith Decimal DecimalNat List Lia String.
Import ListNotations.
Open Scope Z.

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

Section Tables.

Parameter asn_value : Type.
Parameter context : Type.

Definition tag := Z.

Record seq_specifics := {
                         ctx : context ; 
                         tag_to_el : tag -> nat  
                       }.

Inductive TYPE_descriptor :=
  { name : string ;
    tags : list tag ;
    elements : list TYPE_member ;
    decode : list Z -> asn_value -> Prop ;
    seq_specs : list seq_specifics
  }
    with TYPE_member :=
           { mem_tag : Z*Z ; (* tag and flag: implicit *)
             type : TYPE_descriptor ;
           }.

(* Primitive types *)

Parameter asn_true : asn_value.
Parameter asn_false : asn_value.

Inductive bool_decode : list Z -> asn_value -> Prop :=
  | dec_true ls : fsa_run BOOL_fsa ls (TRUE 0) ->
                      bool_decode ls asn_true
  | dec_false ls : fsa_run BOOL_fsa ls (FALSE 0) ->
                      bool_decode ls asn_false.
  
                                
Definition BOOLEAN := {| name := "BOOLEAN";
                         tags := [1];
                         elements := [];
                         decode := bool_decode;
                         seq_specs := []
                      |}.

Parameter integer_decode : list Z -> asn_value -> Prop.
Definition INTEGER := {| name := "INTEGER";
                         tags := [2];
                         elements := [];
                         decode := integer_decode;
                         seq_specs := []
                      |}.

(* Constructed types *)

Parameter seq_decode : list Z -> TYPE_descriptor -> asn_value.

End Tables.
