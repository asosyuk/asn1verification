Require Import Coq.Strings.String Coq.ZArith.ZArith Coq.Lists.List.
Import ListNotations.
Open Scope Z.

Parameter binary : Type.
Parameter asn_value : Type.
Parameter context : Type.
Definition tag := Z.

Record seq_specifics := { ctx : context ;
                 tag_to_el : tag -> nat  
               }.

Inductive TYPE_descriptor :=
  { name : string ;
    tags : list tag ;
    elements : list TYPE_member ;
    decode : binary -> asn_value ;
    seq_specs : list seq_specifics
  }
    with TYPE_member :=
           { mem_tag : Z*Z ; (* tag and flag: implicit *)
             type : TYPE_descriptor ;
           }.

(* Primitive types *)
Parameter bool_decode : binary -> asn_value.
Definition BOOLEAN := {| name := "BOOLEAN";
                         tags := [1];
                         elements := [];
                         decode := bool_decode;
                         seq_specs := []
                      |}.

Parameter integer_decode : binary -> asn_value.
Definition INTEGER := {| name := "INTEGER";
                         tags := [2];
                         elements := [];
                         decode := integer_decode;
                         seq_specs := []
                      |}.

(* Constructed types *)
Parameter seq_decode : binary -> TYPE_descriptor -> asn_value.

Definition BOOLEAN := {| name := "BOOLEAN";
                         tags := [1];
                         elements := [];
                         decode := bool_decode;
                         seq_specs := []
                      |}.

