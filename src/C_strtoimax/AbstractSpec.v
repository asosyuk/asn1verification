Require Import StructTact.StructTactics.
Require Import Core.Core Core.Notations Core.Tactics Core.PtrLemmas.
Require Import Spec Lists.List.

Import ListNotations.
Open Scope Z.

Notation option_lift := RingMicromega.map_option.

Definition string := list byte.

(** * Memory read *)
(* read [n] consecutive bytes from memory [m] starting at addres [a] *)
Definition bytes_of_mem (m : mem) (a : addr) (n : Z) : option (string) :=
  let '(b, ofs) := a in
  (option_lift proj_bytes) (Mem.loadbytes m b (Ptrofs.unsigned ofs) n).

Definition bytes_between (m : mem) (a1 a2 : addr) : option (string) :=
  match distance m a1 a2 with
  | Some n => bytes_of_mem m a1 (Z.of_nat n + 1%Z)
  | None => None
  end.

(** * High level spec *)
(* common bytes *)
Definition minus_char := Byte.repr 45.
Definition plus_char := Byte.repr 43.
Definition zero_char := Byte.repr 48.
Definition nine_char := Byte.repr 57.

Definition is_digit (i : byte) : bool :=
  ((zero_char <= i) && (i <= nine_char))%byte.

Definition Z_of_char (b : byte) : Z :=
  Byte.signed b - Byte.signed zero_char.

Definition is_sign (b : byte) : bool :=
  ((b == plus_char) || (b == minus_char))%byte.

Definition sign_of_char (b : byte) : Z :=
  if (b == plus_char)%byte then 1
  else if (b == minus_char)%byte then (- 1)
       else 0.

Definition bounded (n : Z) : bool :=
  (Int.min_signed <=? n) && (n <=? Int.max_signed).

(* s is not empty *)
Definition non_empty (s : string) := s <> [].

(* all characters in s are digits *)
Definition all_digits (s : string) := forallb is_digit s.

(* Valid inputs that can be successfully converted into int *)

Inductive valid_input : string -> Prop :=
| ValidInput_EXTRA_DATA : forall s' s,
    (* s' represents a number (optionally) preceded by + or - *) 
    valid_input_all_digits s' ->
    (* append any string to s' to get extra data case *)
    valid_input (app s' s)              
with valid_input_all_digits : string -> Prop :=       
     | ValidInput_OK_unsigned :
         forall s,
           non_empty s ->
           all_digits s = true ->
           valid_input_all_digits s
     | ValidInput_OK_signed :
         forall sg s,
           non_empty s ->
           is_sign sg = true ->
           all_digits s = true ->
           valid_input_all_digits (sg :: s).

(* Converts string into an integer:
   - returns None on empty string
   - otherwise converts s into int until a non-digit is encountered 
   - on [c], with c not a digit, returns 0 
     (later we will call it only on valid data so this is irrelevant)  
   - records index where extra data is encountered or where we go out of range *)

Record Z_of_string_result :=
  { val : Z ;
    index : Z ;
  }.

Definition Z_of_string (sign : byte) (s : string) : option Z_of_string_result :=
  let fix Z_of_string_loop s v i :=
      match s with
      | [] => {| val := v ;
                index := i ; |}
      | c :: tl =>
        let i' := (Zlength s - (Zlength tl) - 1)%Z in (* index of c in s *)
        if is_digit c
        then let v := (v * 10 + (Byte.signed c - 48))%Z in
             if bounded v
             then Z_of_string_loop tl v i
             else Z_of_string_loop tl v i' (* recoreded where went out of range *)          
        else {| val := v ;
                index := i' ; |} (* extra stuff is ignored *)               
      end
  in match s with
     |  nil => None (* no data to convert *)
     |  _ => let res := (Z_of_string_loop s 0%Z 0%Z) in
            if (sign == plus_char)%byte
            then Some res
            else Some {| val := Z.opp (val res);
                         index := index res ; |}
                         end.

(** Relational spec *)

(* Store pointer (a2 + i) at address a1 *)
Definition store_pointer (m : mem) (a1 : addr) (a2 : addr) (i : Z) :=
  let (b1, ofs1) := a1 in
  let (b2, ofs2) := a2 in
  Mem.storev Mptr m (Vptr b1 ofs1) (Vptr b2 (ofs2 + (Ptrofs.repr i))%ptrofs).

(* Store v as a long value at address a *)
Definition store_value (m : mem) (a : addr) (v : Z) :=
  let (b, ofs) := a in
  Mem.storev Mint64 m (Vptr b ofs) (Vlong (Int64.repr v)).

Inductive asn_strtoimax_lim_R m str fin intp : mem -> asn_strtox_result_e -> Prop :=
  
(* Input outside of supported numeric range, first read sign *)
| ASN_STRTOX_ERROR_RANGE_R_signed :
    forall sg s z m',
      bytes_between m str fin = Some (sg :: s) ->
      is_sign sg = true ->
      valid_input (sg :: s) ->
      Z_of_string sg s = Some z ->
      bounded (val z) = false ->
      store_pointer m fin str (index z) = Some m' -> 
      asn_strtoimax_lim_R m str fin intp m' ASN_STRTOX_ERROR_RANGE
                          
(* Input outside of supported numeric range *)
| ASN_STRTOX_ERROR_RANGE_R_unsigned :
    forall s z m',
      bytes_between m str fin = Some s ->
      valid_input s -> 
      Z_of_string plus_char s = Some z ->
      bounded (val z) = false ->
      store_pointer m fin str (index z) = Some m' -> 
      asn_strtoimax_lim_R m str fin intp m' ASN_STRTOX_ERROR_RANGE

(* Invalid data encountered (e.g., "+-", "a") *)                       
| ASN_STRTOX_ERROR_INVAL_R_Some :
    forall s,
      bytes_between m str fin = Some s ->
      ~ (valid_input s) ->
      asn_strtoimax_lim_R m str fin intp m ASN_STRTOX_ERROR_INVAL
                          
(* str >= * end and memory fail (could replace by just str >= *end *)                          
| ASN_STRTOX_ERROR_INVAL_R_None :
    bytes_between m str fin = None ->
    asn_strtoimax_lim_R m str fin intp m ASN_STRTOX_ERROR_INVAL
                        
(* More data expected (e.g. "+", "-") *)
| ASN_STRTOX_EXPECT_MORE_R : forall m',
    bytes_between m str fin = Some [plus_char] \/
    bytes_between m str fin = Some [minus_char] ->
    store_pointer m fin str 1%Z = Some m' ->
    asn_strtoimax_lim_R m str fin intp m' ASN_STRTOX_EXPECT_MORE
                        
(* Conversion succeded, but the string has extra stuff, first read sign *)
| ASN_STRTOX_EXTRA_DATA_R_signed :
    forall sg s z m' m'',
      bytes_between m str fin = Some (sg :: s) ->
      valid_input (sg :: s) ->
      (exists c, In c s /\ is_digit c = false) ->
      is_sign sg = true ->      
      Z_of_string sg s = Some z ->
      bounded (val z) = true ->
      store_pointer m fin str (index z) = Some m' ->
      store_value m' intp (val z) = Some m'' ->
      asn_strtoimax_lim_R m str fin intp m'' ASN_STRTOX_EXTRA_DATA

(* Conversion succeded, but the string has extra stuff *)                          
| ASN_STRTOX_EXTRA_DATA_R_unsigned :
    forall s z m' m'',
      bytes_between m str fin = Some s ->
      valid_input s ->
      (exists c, In c s /\ is_digit c = false) ->
      Z_of_string plus_char s = Some z ->
      bounded (val z) = true ->
      store_pointer m fin str (index z) = Some m' ->
      store_value m' intp (val z) = Some m'' ->
      asn_strtoimax_lim_R m str fin intp m'' ASN_STRTOX_EXTRA_DATA
                          
(* Conversion succeded, first read sign *)
| ASN_STRTOX_OK_R_signed :
    forall sg s z m' m'',
      bytes_between m str fin = Some (sg :: s) ->
      is_sign sg = true ->
      valid_input_all_digits (sg :: s) ->
      Z_of_string sg s  = Some z ->
      bounded (val z) = true ->
      store_pointer m fin str (Zlength (sg :: s)) = Some m' ->
      store_value m' intp (val z) = Some m'' ->
      asn_strtoimax_lim_R m str fin intp m'' ASN_STRTOX_OK

| ASN_STRTOX_OK_R_unsigned :
    forall s z m' m'',
      bytes_between m str fin = Some s ->
      valid_input_all_digits s ->
      Z_of_string plus_char s = Some z ->
      bounded (val z) = true ->
      store_pointer m fin str (Zlength s) = Some m' ->
      store_value m' intp (val z) = Some m'' ->
      asn_strtoimax_lim_R m str fin intp m'' ASN_STRTOX_OK.                    
                        
Theorem asn_strtoimax_lim_func_correct : forall m str fin intp res val p s' m',
    asn_strtoimax_lim m str fin intp = Some {| return_type := res;
                                               value := val;
                                               str_pointer := p;
                                               memory := Some m';
                                               sign := s';|}
    <-> asn_strtoimax_lim_R m str fin intp m' res.
Admitted.
    


    
    
  
