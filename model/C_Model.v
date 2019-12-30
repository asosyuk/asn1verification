Require Import Coq.Strings.String Coq.ZArith.ZArith Coq.Lists.List.
Import ListNotations.
Open Scope Z.

Parameter binary : Type.
Parameter asn_value : Type.

Inductive TYPE_descriptor :=
  { name : string ;
    tags : list Z ;
    elements : list TYPE_member ;
    encode : asn_value -> binary ;
    decode : binary -> asn_value 
  }
    with TYPE_member :=
           { mem_id : string ;
             outmost_tag : Z ;
             type : TYPE_descriptor ;
             offset : Z
           }.

Parameter bool_encode : asn_value -> binary.
Parameter bool_decode : binary -> asn_value.

Definition BOOLEAN := {| name := "BOOLEAN";
                         tags := [1];
                         elements := [];
                         encode := bool_encode;
                         decode := bool_decode |}.
