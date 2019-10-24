Require Import StructTact.StructTactics.
Require Import Core.Core Core.Notations Core.Tactics Core.PtrLemmas.

Import ListNotations.

Local Open Scope Int64Scope.

Section Spec.

(* Functional specification of INTEGER.c/asn_strtoimax_lim *)

(* Informal spec:

  Parse the number in the given string until the given end position,
  returning the position after the last parsed character back using the
  same (end) pointer. WARNING: This behavior is different from the standard strtol/strtoimax(3).
*)

(* Output type, see INTEGER.h  *)

Inductive asn_strtox_result_e :=
  | ASN_STRTOX_ERROR_RANGE (* Input outside of supported numeric range *)
  | ASN_STRTOX_ERROR_INVAL (* Invalid data encountered (e.g., "+-") *)
  | ASN_STRTOX_EXPECT_MORE (* More data expected (e.g. "+") *)
  | ASN_STRTOX_EXTRA_DATA  (* Conversion succeded, but the string has extra stuff *)
  | ASN_STRTOX_OK.         (* Conversion succeded, number ends at (end) *)

(* C light outputs directly int *)

Definition asn_strtox_result_e_to_int (s : asn_strtox_result_e) : int :=
  match s with
    | ASN_STRTOX_ERROR_RANGE => Int.repr (-3)
    | ASN_STRTOX_ERROR_INVAL => Int.repr (-2)
    | ASN_STRTOX_EXPECT_MORE => Int.repr (-1)
    | ASN_STRTOX_EXTRA_DATA => Int.repr 1
    | ASN_STRTOX_OK => Int.repr 0
  end.

(* Useful notations and definitions *)
Definition minus_char := 45.
Definition plus_char := 43.
Definition zero_char := 48.

(* Representing negative and positive int using signedness *)
Definition int_to_int64 (i : int) := Int64.repr (Int.signed i).

Definition sign_to_int s :=
  match s with
  | Signed => (Int.repr (-1))
  | Unsigned => Int.repr 1
  end.

Definition char_to_sign i :=
  if (i == (Int.repr minus_char))%int then Signed else Unsigned.

Definition mult_sign s value :=
  match s with
  | Signed => ((Int64.repr (-1))*value)%int64
  | Unsigned => value
  end.

(* Converting a single char into into a number given previous value *)
Definition digit_to_num s i v :=
  match s with
  | Signed => (Int64.neg v * (Int64.repr 10) -
               int_to_int64 (i - (Int.repr zero_char))%int)
  | Unsigned => (v * (Int64.repr 10) +
                 int_to_int64 (i - (Int.repr zero_char))%int)
  end.
      
  (* Memory, global and local env are fixed *)
  Variable m : mem.
  Variable ge : genv.
  Variable e : env.

  (* Constants of the function *)
  Definition ASN1_INTMAX_MAX := (Int64.not 0) >> 1.
  Definition upper_boundary := ASN1_INTMAX_MAX // (Int64.repr 10).
  Definition upper_boundary_Z := Int64.signed upper_boundary.
  Definition last_digit_max := ASN1_INTMAX_MAX % (Int64.repr 10).
  Definition last_digit_max_Z := Int64.signed last_digit_max.
  Definition last_digit_max_minus := (ASN1_INTMAX_MAX % (Int64.repr 10)) + 1.
  Definition last_digit_max_minus_Z := Int64.signed last_digit_max_minus.
  
  (* digits [0-9]*)
  Definition is_digit (i : Z) := andb (48 <=? i) (i <=? 57).
  
  (* Executable spec *)

  (* Return type *)
  Record asn_strtoimax_lim_result :=
    { return_type : asn_strtox_result_e ;
      len : Z ;
      value : option Z }.

Close Scope Int64Scope.

Definition asn_strtoimax_lim_spec (c : list Z) : asn_strtoimax_lim_result :=
  let fix loop (c : list Z) (value len ld sign : Z) := 
      match c with
      | [] => {| return_type := ASN_STRTOX_OK;
                value := Some (sign * value);
                len := len |}
      | x :: xs => if is_digit x 
                 then if value <? upper_boundary_Z
                      then loop xs (value * 10 + (x - 48)) (len + 1) ld sign
                      else if andb (value =? upper_boundary_Z) 
                                   ((x - 48) <=? ld) 
                           then match xs with
                                | [] => {| return_type := ASN_STRTOX_OK;
                                          value := Some (sign * (value * 10 + (x - 48)));
                                          len := len |}
                                | y :: ys => if is_digit y
                                           then {| return_type := ASN_STRTOX_ERROR_RANGE;
                                                   value := None;
                                                   len := 0 |}
                                           else {| return_type := ASN_STRTOX_EXTRA_DATA;
                                                   value := Some (sign * (value * 10 + (x - 48)));
                                                   len := len |}
                                end
                           else {| return_type := ASN_STRTOX_ERROR_RANGE;
                                   value := None;
                                   len := 0 |}
                 else {| return_type := ASN_STRTOX_EXTRA_DATA;
                         value := Some (sign * value);
                         len := len |}
  end in
  match c with
  | x :: xs => if (x =? 45) (* minus case *)
              then loop xs 0 1 last_digit_max_minus_Z (-1)
              else if (x =? 43) (* plus case *)
                   then loop xs 0 1 last_digit_max_Z 1
                   else loop c 0 0 last_digit_max_Z 1
  | [] => {| return_type := ASN_STRTOX_ERROR_INVAL;
            value := None;
            len := 0 |}
  end.

(* Compute (asn_strtoimax_lim [45; 49; 50; 51; 52; 53]).
Compute (asn_strtoimax_lim [43; 49; 50; 51; 52; 53]).
Compute (asn_strtoimax_lim [49; 50; 51; 52; 53]).
Compute (asn_strtoimax_lim [45; 49; 50; 51; 52; 53; 54; 55; 56; 57; 45]). *)

End Spec.
