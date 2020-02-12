Require Import Nat List ZArith Decimal DecimalNat List Lia.
Import ListNotations.

From compcert Require Import Integers.

Open Scope Z.

Inductive asn_value := OK | ERROR | MORE.

Record asn_res := RES { val : asn_value ;
                        rest : list Z }.


Record TYPE_descriptor :=
  DEF { tags : list Z ;
        elements : list TYPE_descriptor 
      }.

Section PrimitiveDecoders.

(* Read data until the end *)
Definition primitive_decoder (len : Z) (ls : list Z) :=
    if len <=? Zlength ls
    then RES OK (skipn (Z.to_nat len) ls)
    else RES MORE ls.  
  
Definition BOOLEAN := DEF [1] [].
Definition INTEGER := DEF [2] [].

End PrimitiveDecoders.

Section SequenceDecoder.

  (* Check if tag is among the list of tags *)
  Definition check_tag t ts := if existsb (fun l => l =? t) ts
                               then true
                               else false.
     
  Fixpoint seq_decoder (X : TYPE_descriptor) (ls : list Z)  :=
    match ls with
    | [] => RES OK ls
    | [t] => RES MORE ls       
    | t :: l :: bs =>          
      if check_tag t (tags X)
        then
          match elements X with 
          | [] => primitive_decoder l bs 
          | XS => (fix elem_seq_decoder XS bs :=
                        match XS with
                        | [] => RES OK bs
                        | X :: XS =>
                          match seq_decoder X bs with
                            | RES OK r => elem_seq_decoder XS r 
                            | r => r
                          end
                        end) XS bs
          end
        else RES ERROR (l::bs)
    end.

  Definition n1 := DEF [2] [].
  Definition n2 := DEF [2] [].
  Definition b1 := DEF [1] [].  
  Definition Sb := DEF [30] [b1].
  Definition Snb := DEF [30] [n1; n2; Sb].

  (* for now ignore seq length *)
  Compute (seq_decoder n1 [3;2;1;1;1]).
  Compute (seq_decoder Sb [30;1;2;1;1;2]).
  Compute (seq_decoder Snb [30;6;2;1;1;2;2;1;3;30;5;1;1;1]).

End SequenceDecoder.


Section PRIM_automaton.

  Set Implicit Arguments.

  Record fsa (S A : Type) := FSA { initial : S;
                                   next : S -> A -> S -> Prop }.

  Inductive fsa_run {S A : Type } (m : fsa S A) : list A -> S -> Prop :=
  | step : forall a s, next m (initial m) a s -> fsa_run m [a] s
  | trans : forall s1 a s2 l rs, next m s1 a s2 -> fsa_run m l rs -> fsa_run m (a::l) rs.

  Inductive PRIM_state :=
  | INIT (X : TYPE_descriptor)
  | TAG
  | DEC  (l : Z) (v : list Z)
  | OUT (r : asn_value).
  
  Reserved Notation "st1 -[ c ]-> st2" (at level 50).
  
  Inductive PRIM_next : PRIM_state -> Z -> PRIM_state -> Prop :=
  | read_tag t X : 
      In t (tags X) ->
      INIT X -[ t ]-> TAG 
  | read_prim_length l : 
      TAG  -[ l ]-> DEC l []
  | read_value l vl v : 
      1 < l ->
      DEC l vl -[ v ]-> DEC (l-1) (v::vl) 
  | call_prim_decoder vl v: 
      DEC 1 vl -[ v ]-> OUT OK   
  | read_constr_length l X Y n: 
      (n < length (elements X))%nat ->
      nth n%nat (elements X) X = Y ->
      TAG -[ l ]-> INIT Y 

  where "st1 -[ c ]-> st2" := (PRIM_next st1 c st2).

  Definition PRIM_fsa X := {| initial := INIT X ; 
                              next := PRIM_next |}.

  Definition PRIM_star X := fsa_run (PRIM_fsa X).
     
End PRIM_automaton.


  
