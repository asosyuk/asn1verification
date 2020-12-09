Require Import Core.Core Core.Notations ErrorWithWriter.
Require Import ExtLib.Data.List.

Require Export ErrorWithWriter.

(* Decoder return type *)
Record asn_dec_rval := rval { consumed : Z }.

(* tag_consumed - how much buffer ber_check_tags consumed
   tag_length - expected size of value(in bytes) *)
Record check_tag_r := mk_check_tag { tag_consumed : Z; tag_length : Z }.

(* Encoder return type *)
Record asn_enc_rval : Type := encode {
  encoded : Z ;
}.


(* ASN.1 types and values *)
Inductive asn_value :=
  | ANY : asn_value
  | BOOLEAN : bool -> asn_value 
  | INTEGER : Z -> asn_value
  | PRIM_INTEGER : list byte -> asn_value
  | BIT_STRING : list bool -> asn_value
  | SEQUENCE : list asn_value -> asn_value
  | SET : list asn_value -> asn_value
  | CHOICE : list asn_value -> asn_value. 

(* for notation purposes *)
Instance Nth_Asn_value : Nth asn_value :=
  { default := ANY ;
    n_th := fun n ls => nth (Z.to_nat n) ls ANY;
    hd_nth := fun ls => List.hd ANY ls
 }.

Inductive asn_type :=
  | ANY_t 
  | BOOLEAN_t 
  | INTEGER_t 
  | BIT_STRING_t 
  | SEQUENCE_t 
  | SET_t
  | CHOICE_t.

Inductive TYPE_descriptor :=
  def { tags : list Z;
        elements : list TYPE_descriptor; 
        decoder_type : asn_type;
        tags_count : Z
      }.

(* The function can return error in 3 cases:
   1) If der_write_tags fails.
   2) If cb fails.
   3) Fail of encoding or decoding with custom error message, to distinguish between them.
*)
(* TODO Maybe rename CustomError constructor to smt like LogicError *)
Inductive Err := HeaderEncodeError 
                 | CBEncodeError
                 | CustomError {T : Type} : T -> Err.

(* Specialized version of errW with custom Error and Log type with specialized tell *)
Definition errW1 := @errW Err (list int).

Existing Class Monoid.
Existing Instance Monoid_list_app.

Definition tell1 := @tell (list int) (Monoid_list_app) errW1 Writer_errW.
