Require Import Core.Core Core.Notations Core.Tactics ErrorWithWriter.
From ExtLib.Structures Require Import Monad MonadWriter Monoid.
From ExtLib.Data Require Import Monads.OptionMonad List.

Import ListNotations.
Import MonadNotation.

Open Scope monad.

Existing Class Monoid.
Existing Instance Monoid_list_app.

(* Decoder return type *)
Record asn_dec_rval := rval { consumed : Z }.

(* Encoder return type *)
Record asn_enc_rval : Type := encode {
  encoded : Z ;
}.

(* ASN.1 types and values *)
Inductive asn_value :=
  | ANY : asn_value
  | BOOLEAN : bool -> asn_value 
  | INTEGER : Z -> asn_value
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
        decoder_type : asn_type
      }.

Record check_tag_r := mk_check_tag_rval { tag_consumed : Z; tag_expected : Z }.

(* The function can return error in 3 cases:
   1) If der_write_tags fails.
   2) If cb fails.
   3) Fail of encoding or decoding with custom error message, to distinguish between them.
*)
(* TODO Maybe rename CustomError constructor to smt like LogicError *)
Inductive Err := HeaderEncodeError 
                 | CBEncodeError
                 | CustomError {T : Type} : T -> Err.

(* Specialized version of errW with custom Error and Log type *)
Definition errW1 := @errW Err (list byte).

(* Writes header octets *)
Parameter der_write_tags : TYPE_descriptor -> errW1 asn_enc_rval.

(* checks the tag, outputs consumed length and expected length *)
Parameter ber_check_tag : TYPE_descriptor -> list byte -> option check_tag_r.

(* checks tag in ls wrt td, 
   then returns head of ls and consumed bytes or error *) 
Definition primitive_decoder_bool td ls : option (byte * Z) :=
    match ls with
    | [] => None
    | _ => ber_check_tag td ls >>=
                        fun x => let c := tag_consumed x in 
                              let e := tag_expected x in 
                              if (Zlength ls - c <? e) || negb (e =? 1) 
                              then None 
                              else hd_error (skipn (Z.to_nat c) ls) 
                                     >>= fun y => Some (y, c + 1)
    end.

Definition primitive_decoder td ls : option (list byte * Z) :=
    match ls with
    | [] => None
    | _ => ber_check_tag td ls >>=
                        fun x => let c := tag_consumed x in 
                              let e := tag_expected x in 
                              if (Zlength ls - c <? e)
                              then None 
                              else let y := skipn (Z.to_nat c) ls in
                                    Some (y, c + 1)
    end.

(* writes tags, copies ls and outputs the number of encoded bytes *)
Definition primitive_encoder td ls : errW1 asn_enc_rval :=
  der_write_tags td >>= 
                 fun x => tell ls >>= 
                            fun _ => ret (encode (Zlength ls + encoded x)).

Definition ZeroChar := Byte.repr 48.
