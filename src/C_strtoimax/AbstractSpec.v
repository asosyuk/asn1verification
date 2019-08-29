Require Import StructTact.StructTactics.
Require Import Core.Core Core.Notations Core.Tactics Core.PtrLemmas.
Require Import Spec.

Import ListNotations.

Local Open Scope ByteScope.

(* Abstract specification *)

(* The most abstract level: Coq byte list and Z *)

(* String is a byte list *)
Definition string := list byte.

Definition minus_char := Byte.repr 45.
Definition plus_char := Byte.repr 43.
Definition zero_char := Byte.repr 48.

Definition is_digit (i : byte) := (Byte.repr 48 <= i) && (i <= Byte.repr 57).

Section ZSpec.

  (* Take a string s and return a pair with its integer representation *)

Definition string_to_Z (s : string) : option Z :=
  let fix string_to_Z_loop s v :=
      match s with
      | [] => v
      | c :: tl =>
        if is_digit c
        then let v := (v * 10 + (Byte.signed c - 48))%Z in
             string_to_Z_loop tl v                
        else v(* extra stuff is ignored *)     
      end
  in match s with
     | nil => None (* not enough data *)
     | _ => Some (string_to_Z_loop s 0%Z)
     end.

(* The sign is determined by the first char in the string *)
Definition signed_string_to_Z (s : string) :=
  match s with
  | nil => None 
  | c :: tl => if c == minus_char
             then option_map Z.opp (string_to_Z tl)      
               else if c == plus_char
                    then string_to_Z tl
                    else string_to_Z s
  end.
  

End ZSpec.



Section RelationalSpec.

  (* To relate the abstract spec we need to add assumption about memory *)
Definition byte_of_int b := Byte.repr (Int.unsigned b).

(* There is a string s at address str until fin *)
(* Note: load returns value of type Vint, hence need a conversion from byte *)
Definition string_at_address m str fin : option (list byte) :=
  match load_addr Mptr m fin with
    | Some (Vptr b fin') => 
      match distance m str (b,fin') with
      | Some dist =>
        let fix string_at_address m s str dist : option (list byte) :=
            match dist with
            | O => Some s
            | S n => match load_addr Mint8signed m str with
                    | Some (Vint i) =>
                      string_at_address m ((byte_of_int i)::s) (str++) n
                    | _ => None
                    end
            end in
        string_at_address m nil str dist
      | _ => None
      end
    | _ => None
  end.

  (* Relational spec without memory stores *)
  
  Inductive asn_strtoimax_lim_R m str fin : asn_strtox_result_e -> Prop :=
    (* Input outside of supported numeric range *)
  | ASN_STRTOX_ERROR_RANGE_R s z :
      string_at_address m str fin = Some s ->
      signed_string_to_Z s = Some z ->
      (Int64.max_signed <= z)%Z \/ (z <= Int64.min_signed)%Z ->
      asn_strtoimax_lim_R m str fin ASN_STRTOX_ERROR_RANGE
    (* Invalid data encountered (e.g., "+-") *)
  | ASN_STRTOX_ERROR_INVAL_R :
      addr_ge m str fin = Some true ->
      asn_strtoimax_lim_R m str fin ASN_STRTOX_ERROR_INVAL
    (* More data expected (e.g. "+") *)
  | ASN_STRTOX_EXPECT_MORE_R :
      string_at_address m str fin = Some [plus_char] \/
      string_at_address m str fin = Some [minus_char] ->
      asn_strtoimax_lim_R m str fin ASN_STRTOX_EXPECT_MORE
    (* Conversion succeded, but the string has extra stuff *)
  | ASN_STRTOX_EXTRA_DATA_R s z :
      string_at_address m str fin = Some s ->
      signed_string_to_Z s = Some z ->
      (Int64.min_signed <= z <= Int64.max_signed)%Z ->
      (exists c, In c s /\ is_digit c = false) ->
      asn_strtoimax_lim_R m str fin ASN_STRTOX_EXTRA_DATA
      (* Conversion succeded *)
  | ASN_STRTOX_OK_R s z :
      string_at_address m str fin = Some s ->
      signed_string_to_Z s = Some z ->
      (Int64.min_signed <= z <= Int64.max_signed)%Z ->
      asn_strtoimax_lim_R m str fin ASN_STRTOX_OK.  

  (* Relational spec with memory stores *)
  
  (* We need to store a pointer where we stop in error range, extra data and ok case,
     hence this additional function:

     Take a string s and an index where either the first non-digit is encountered 
     or we go out of range. If none of the above happens return (length s) *)

Definition string_to_Z_endpoint (s : string) : option Z :=
  let fix string_to_Z_loop s v z :=
      match s with
      | [] => z
      | c :: tl =>
        (* index of c in s *)
        let i := (Zlength s - (Zlength tl) - 1)%Z in
        if is_digit c
        then let v := (v * 10 + (Byte.signed c - 48))%Z in
             if (Int64.max_signed <=? z)%Z || (z <=? Int64.min_signed)%Z
             then i
             else string_to_Z_loop tl v z               
        else i 
      end
  in match s with
     | nil => None 
     | _ => Some (string_to_Z_loop s 0%Z (Zlength s))
     end.

(* The sign is determined by the first char in the string *)
Definition signed_string_to_Z_endpoint (s : string) :=
  match s with
  | nil => None 
  | c :: tl => if (c == minus_char) || (c == plus_char)
             then string_to_Z_endpoint tl     
             else string_to_Z_endpoint s
  end.
  
  Inductive asn_strtoimax_lim_R_mem m str fin intp : mem -> asn_strtox_result_e -> Prop :=
    (* Input outside of supported numeric range *)
  | ASN_STRTOX_ERROR_RANGE_R_mem s z m' i :
      string_at_address m str fin = Some s ->
      signed_string_to_Z s = Some z ->
      signed_string_to_Z_endpoint s = Some i ->
      (Int64.max_signed <= z)%Z \/ (z <= Int64.min_signed)%Z ->
      store_addr Mptr m fin (vptr (add_addr str (Ptrofs.repr i)))
      = Some m' -> 
      asn_strtoimax_lim_R_mem m str fin intp m' ASN_STRTOX_ERROR_RANGE
    (* Invalid data encountered (e.g., "+-") *)
  | ASN_STRTOX_ERROR_INVAL_R_mem :
      addr_ge m str fin = Some true ->
      asn_strtoimax_lim_R_mem m str fin intp m ASN_STRTOX_ERROR_INVAL
    (* More data expected (e.g. "+") *)
  | ASN_STRTOX_EXPECT_MORE_R_mem m':
      string_at_address m str fin = Some [plus_char] \/
      string_at_address m str fin = Some [minus_char] ->
      store_addr Mptr m fin (vptr (str++)) = Some m' -> 
      asn_strtoimax_lim_R_mem m str fin intp m' ASN_STRTOX_EXPECT_MORE
    (* Conversion succeded, but the string has extra stuff *)
  | ASN_STRTOX_EXTRA_DATA_R_mem s z m' m'' i:
      string_at_address m str fin = Some s ->
      signed_string_to_Z s = Some z ->
      signed_string_to_Z_endpoint s = Some i ->
      (Int64.min_signed <= z <= Int64.max_signed)%Z ->
      (exists c, In c s /\ is_digit c = false) ->
      store_addr Mptr m fin (vptr (add_addr str (Ptrofs.repr i)))
      = Some m' -> 
      store_addr Mint64 m' intp (Vlong (Int64.repr z)) = Some m'' -> 
      asn_strtoimax_lim_R_mem m str fin intp m'' ASN_STRTOX_EXTRA_DATA
      (* Conversion succeded *)
  | ASN_STRTOX_OK_R_mem s z m' m'':
      string_at_address m str fin = Some s ->
      signed_string_to_Z s = Some z ->
      (Int64.min_signed <= z <= Int64.max_signed)%Z ->
      store_addr Mptr m fin (vptr (add_addr str (Ptrofs.repr (Zlength s))))
      = Some m' -> 
      store_addr Mint64 m' intp (Vlong (Int64.repr z)) = Some m'' -> 
      asn_strtoimax_lim_R_mem m str fin intp m'' ASN_STRTOX_OK.
  
End RelationalSpec.

Theorem asn_strtoimax_lim_func_correct : forall m str fin fin' intp res val p s' m',
    asn_strtoimax_lim m str fin intp = Some {| return_type := res;
                                               value := val;
                                               str_pointer := p;
                                               memory := Some m';
                                               sign := s';|}
    <-> asn_strtoimax_lim_R_mem m str fin' intp m' res.
Proof.
  intros.
  split; intro.
  induction res.
  - econstructor.
    all: admit.
  - inversion H.
    unfold string_at_address in *.
    unfold signed_string_to_Z in *.
    unfold asn_strtoimax_lim in *.
    unfold store_result in *.
    unfold distance in *.
    unfold vptr in *.
    repeat break_match; try congruence.
    unfold addr_ge, ptr_ge in *.
    Admitted.
    
    
(* Functional spec continued *)

(* Moving towards implementation. Step 1: bounds on Z *)
Section ZBoundsSpec.

(* Assume some intsize and 2-complement encoding of negative int *)  
Variable intsize : Z.
Definition upper_boundZ := (intsize / 10)%Z.
Definition last_digit_plusZ := (Zmod intsize 10)%Z.
Definition last_digit_minusZ := (last_digit_plusZ + 1)%Z.
 
Definition string_to_Z_bound s last_digit :=
  let fix string_to_Z_loop s v last_digit :=
      match s with
      | [] => Some v
      | c :: tl =>
        if is_digit c then
          let d := (Byte.signed c - 48)%Z in
          if (v <? upper_boundZ)%Z ||
            ((v =? upper_boundZ)%Z && (d <=? last_digit)%Z)
          then string_to_Z_loop tl (v * 10 + d)%Z
                                last_digit
          else None (* out of range *)
        else Some v (* extra stuff is ignored *)     
      end
  in match s with
     | nil => None (* empty string corresponds to nothing *)
     | _ => (string_to_Z_loop s 0%Z last_digit)
     end.

(* The sign is determined by the first char in the string *)
Definition signed_string_to_Z_bound s :=
  match s with
  | nil => None 
  | c :: tl => if c == minus_char
               then option_map
                      Z.opp (string_to_Z_bound tl last_digit_minusZ)
               else if c == plus_char
                    then string_to_Z_bound tl last_digit_plusZ
                    else string_to_Z_bound s last_digit_plusZ
  end.

End ZBoundsSpec.

Section IntSpec.
  
Local Open Scope Int64Scope.

(* Then we can formulate it on int *)
Definition long_of_byte b := Int64.repr (Byte.unsigned b).

Definition intmax := (Int64.repr Int64.max_unsigned).
Definition upper_bound := Int64.repr (upper_boundZ Int64.max_unsigned).
Definition lower_bound := Int64.neg upper_bound.
Definition last_digit_plus := intmax % (Int64.repr 10).
Definition last_digit_minus := (intmax % (Int64.repr 10)) + 1.

Definition string_to_int_plus s :=
  let fix string_to_Z_loop s v :=
      match s with
      | [] => Some v
      | c :: tl =>
        if is_digit c then
          let d := (long_of_byte c - (Int64.repr 48)) in
          if (v < upper_bound) ||
             ((v == upper_bound) && (d <= last_digit_plus))
          then
            string_to_Z_loop tl (v * (Int64.repr 10) + d)
          else None 
        else Some v  
      end
  in match s with
     | nil => None 
     | _ => string_to_Z_loop s 0%int64
     end.

Definition string_to_int_minus s :=
  let fix string_to_Z_loop s v :=
      match s with
      | [] => Some v
      | c :: tl =>
        if is_digit c then
          let d := (long_of_byte c - (Int64.repr 48)) in
          if (lower_bound < v) ||
             ((v == lower_bound) && (d <= last_digit_minus))
          then
            string_to_Z_loop tl (v * (Int64.repr 10) - d)
          else None 
        else Some v  
      end
  in match s with
     | nil => None 
     | _ => string_to_Z_loop s 0%int64
     end.

(* The sign is determined by the first char in the string *)
Definition signed_string_to_int s :=
  match s with
  | nil => None 
  | c :: tl => if (c == minus_char)%byte
               then string_to_int_minus tl
               else if (c == plus_char)%byte
                    then string_to_int_plus tl
                    else string_to_int_plus s 
  end.

End IntSpec.


    
    
  
