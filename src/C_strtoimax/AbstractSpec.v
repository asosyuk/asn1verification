Require Import Core.Core Core.Tactics.
Require Import Core.PtrLemmas.
Require Import StructTact.StructTactics.
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
(* Take a string and a sign and return its integer representation *)

Definition string_to_Z (s : string) :=
  let fix string_to_Z_loop s v :=
      match s with
      | [] => v
      | c :: tl =>
        if is_digit c
        then let v := (v * 10 - (Byte.signed c - 48))%Z in
             string_to_Z_loop tl v
        else v (* extra stuff is ignored *)     
      end
  in match s with
     | nil => None (* empty string corresponds to nothing *)
     | _ => Some (string_to_Z_loop s 0%Z)
     end.

(* The sign is determined by the first char in the string *)
Definition signed_string_to_Z (s : string) (sign : signedness) :=
  match s with
  | nil => None 
  | c :: tl => if c == minus_char
               then option_map Z.opp (string_to_Z tl)
               else if c == plus_char
                    then string_to_Z tl
                    else string_to_Z s
  end.
End ZSpec.

(* Moving towards implementation. Step 1: bounds on Z *)
Section ZBoundsSpec.

(* Assume some intsize and 2-complement encoding of negative int *)  
Variable intsize : Z.
Definition upper_bound := (intsize / 10)%Z.
Definition last_digit_plus := (Zmod intsize 10)%Z.
Definition last_digit_minus := (last_digit_plus + 1)%Z.
 
Definition string_to_Z_bound s last_digit :=
  let fix string_to_Z_loop s v last_digit :=
      match s with
      | [] => Some v
      | c :: tl =>
        if is_digit c then
          if (v <? upper_bound)%Z ||
              ((v =? upper_bound)%Z && (v <=? last_digit)%Z)
          then string_to_Z_loop tl (v * 10 - (Byte.signed c - 48))%Z
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
                      Z.opp (string_to_Z_bound tl last_digit_minus)
               else if c == plus_char
                    then string_to_Z_bound tl last_digit_plus
                    else string_to_Z_bound s last_digit_plus
  end.

End ZBoundsSpec.

Section IntSpec.
  Local Open Scope Int64Scope.

(* Then we can formulate it on int, TODO: need to account for difference in overflow *)
Definition long_of_byte b := Int64.repr (Byte.unsigned b). 
Variable upper_bound : int64.
Variable last_digit_plus :  int64.
Variable last_digit_minus : int64.

Definition string_to_int s last_digit :=
  let fix string_to_Z_loop s v last_digit :=
      match s with
      | [] => Some v
      | c :: tl =>
        if is_digit c then
          if (v < upper_bound) ||
             ((v == upper_bound) && (v <= last_digit))
          then
            let v := (v * (Int64.repr 10) - (long_of_byte c - (Int64.repr 48)))
                       in string_to_Z_loop tl v last_digit
          else None (* out of range *)
        else Some v (* extra stuff is ignored *)     
      end
  in match s with
     | nil => None (* empty string corresponds to nothing *)
     | _ => (string_to_Z_loop s 0%int64 last_digit)
     end.

(* The sign is determined by the first char in the string *)
Definition signed_string_to_int s :=
  match s with
  | nil => None 
  | c :: tl => if (c == minus_char)%byte
               then option_map
                      Int64.neg (string_to_int tl last_digit_minus)
               else if (c == plus_char)%byte
                    then string_to_int tl last_digit_plus
                    else string_to_int s last_digit_plus
  end.

(* Connecting different levels *)

(* To relate the abstract spec we need to add assumption about memory *)
Definition byte_of_int b := Byte.repr (Int.unsigned b).

(* There is a string s of length dist at address str *)
(* Note: load returns value of type Vint, hence need a conversion from byte *)
Fixpoint string_at_address m s str dist : option (list byte) :=
  match dist with
  | O => Some s
  | S n => match load_addr Mint8signed m str with
          | Some (Vint i) => string_at_address m ((byte_of_int i)::s) (str++) n
          | _ => None
          end
  end.
    
Proposition asn_strtoimax_lim_fun_correct : forall s m str fin intp m' val,
    asn_strtoimax_lim m str fin intp = Some {| return_type := ASN_STRTOX_OK ;
                                             value := Some val ;
                                             memory := m' |}
                                       <->
         addr_ge m str fin = Some false
         /\ string_at_address m nil str (distance str fin) = Some s
         /\ signed_string_to_int s = Some val.
Admitted.

End IntSpec.
