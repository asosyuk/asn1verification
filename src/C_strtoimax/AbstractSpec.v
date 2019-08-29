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
  
(* Take a string and a sign and return its integer representation *)

Definition string_to_Z (s : string) :=
  let fix string_to_Z_loop s v :=
      match s with
      | [] => v
      | c :: tl =>
        if is_digit c
        then let v := (v * 10 + (Byte.signed c - 48))%Z in
             string_to_Z_loop tl v
        else v (* extra stuff is ignored *)     
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

(* Connecting different levels *)

(* To relate the abstract spec we need to add assumption about memory *)
Definition byte_of_int b := Byte.repr (Int.unsigned b).

(* There is a string s at address str until fin *)
(* Note: load returns value of type Vint, hence need a conversion from byte *)
Definition string_at_address m str fin : option (list byte) :=
  match distance m str fin with
  | Some dist =>
    let fix string_at_address m s str dist : option (list byte) :=
        match dist with
        | O => Some s
        | S n => match load_addr Mint8signed m str with
                | Some (Vint i) => string_at_address m
                                                    ((byte_of_int i)::s)
                                                    (str++) n
                 | _ => None
                 end
        end in
    string_at_address m nil str dist
  | _ => None
end.

End IntSpec.

Section RelationalSpec.

Definition store_addr (chunk : memory_chunk) (m : mem) (a : addr) :=
  match a with (b,ofs) => Mem.storev chunk m (Vptr b ofs) end.
  
  Inductive asn_strtoimax_lim_R m str fin intp : asn_strtox_result_e -> Prop :=
    (* Input outside of supported numeric range *)
  | ASN_STRTOX_ERROR_RANGE_R s z :
      string_at_address m str fin = Some s ->
      signed_string_to_Z s = Some z ->
      (Int64.max_signed <= z)%Z \/ (z <= Int64.min_signed)%Z ->
      asn_strtoimax_lim_R m str fin intp ASN_STRTOX_ERROR_RANGE
    (* Invalid data encountered (e.g., "+-") *)
  | ASN_STRTOX_ERROR_INVAL_R :
      addr_ge m str fin = Some true ->
      asn_strtoimax_lim_R m str fin intp ASN_STRTOX_ERROR_INVAL
    (* More data expected (e.g. "+") *)
  | ASN_STRTOX_EXPECT_MORE_R :
      string_at_address m str fin = Some [plus_char] \/
      string_at_address m str fin = Some [minus_char] ->
      asn_strtoimax_lim_R m str fin intp ASN_STRTOX_EXPECT_MORE
    (* Conversion succeded, but the string has extra stuff *)
  | ASN_STRTOX_EXTRA_DATA_R s z m' :
      string_at_address m str fin = Some s ->
      signed_string_to_Z s = Some z ->
      (Int64.min_signed <= z <= Int64.max_signed)%Z ->
      (exists c, In c s /\ is_digit c = false) ->
      store_addr Mint64 m intp (Vlong (Int64.repr z)) = Some m' -> 
      asn_strtoimax_lim_R m str fin intp ASN_STRTOX_EXTRA_DATA
      (* Conversion succeded *)
  | ASN_STRTOX_OK_R s z m' :
      string_at_address m str fin = Some s ->
      signed_string_to_Z s = Some z ->
      (Int64.min_signed <= z <= Int64.max_signed)%Z ->
      store_addr Mint64 m intp (Vlong (Int64.repr z)) = Some m' -> 
      asn_strtoimax_lim_R m str fin intp ASN_STRTOX_OK.  
  
End RelationalSpec.

Theorem asn_strtoimax_lim_func_correct : forall m str fin fin' intp res,
    asn_strtoimax_lim m str fin intp = Some res <->
    (load_addr Mptr m fin = Some (vptr fin') /\
     asn_strtoimax_lim_R m str fin' intp res.(return_type)).
Proof.
  intros.
  destruct res.
  destruct return_type.
  split; intro.
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
    
    
    
    
  
    
    
  
