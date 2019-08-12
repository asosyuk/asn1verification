Require Import Core.Core Core.Tactics.
Require Import Core.PtrLemmas.
Require Import StructTact.StructTactics.

Import ListNotations.

Local Open Scope Int64Scope.

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
Notation minus_char := (Int.repr 45).
Notation plus_char := (Int.repr 43).
Notation zero_char := (Int.repr 48).

(* Representing negative and positive int *)
Definition int_to_int64 (i : int) := Int64.repr (Int.signed i).

Definition Sign s :=
  match s with
  | Signed => (Int.repr (-1))
  | Unsigned => Int.repr 1
  end.

Definition mult_sign s value :=
  match s with
  | Signed =>  ((Int64.repr (-1))*value)%int64 
  | Unsigned => value
  end.

Definition digit_to_num s i inp_value :=
  match s with
  | Signed => (Int64.neg inp_value * (Int64.repr 10) -
               int_to_int64 (i - zero_char)%int)
  | Unsigned => (inp_value * (Int64.repr 10) +
                 int_to_int64 (i - zero_char)%int)
  end.
    
(* Memory, global and local env are fixed *)
Parameter m : mem.
Parameter ge : genv.
Parameter e : env.

Definition ASN1_INTMAX_MAX :=(Int64.not 0) >> 1.

Fact shift_pow2_div :
  (Int64.shru (Int64.not Int64.zero) Int64.one) =
  Int64.repr (Int64.max_unsigned / 2).
Proof.
  replace (Int64.not Int64.zero) with (Int64.repr Int64.max_unsigned) by (auto with ints).
  unfold Int64.shru.
  f_equal.
Qed.

Definition upper_boundary := ASN1_INTMAX_MAX // (Int64.repr 10).
Definition last_digit_max := ASN1_INTMAX_MAX % (Int64.repr 10).
Definition last_digit_max_minus := (ASN1_INTMAX_MAX % (Int64.repr 10)) + 1.

(* digits [0-9]*)
Definition digits := map Int.repr [48;49;50;51;52;53;54;55;56;57].
Definition is_digit (i : int) := existsb (fun j => Int.eq i j) digits.
(* Functional spec *)

Record asn_strtoimax_lim_result :=
  { return_type : asn_strtox_result_e ;
    value : option int64 ;
    intp : option addr ;
    memory : option mem ; 
    }.

Fixpoint asn_strtoimax_lim_loop (str fin intp : addr) (value : int64) (s: signedness) (last_digit : int64) (dist : nat) (m' : mem) {struct dist} : option asn_strtoimax_lim_result :=
  match dist with
  | O => match (Mem.storev Mptr m (vptr fin) (vptr str)) with
        | Some m' => 
          Some {| return_type := ASN_STRTOX_OK;
                  value := Some (mult_sign s value);
                  intp := Some intp;                        
                  memory := Mem.storev Mint64 m' (vptr intp) (Vlong (mult_sign s value)) |}
        | None => None
        end        
  | S n => match load_addr Mint8signed m str with
          | Some (Vint i) =>
            if is_digit i
            then let d := int_to_int64 (i - zero_char)%int in
                 if value < upper_boundary
                 then asn_strtoimax_lim_loop (str++) fin intp
                      (value * (Int64.repr 10) + d) s last_digit n m
                 else if (value == upper_boundary) && (d <= last_digit)
                      then match s with
                             | Signed => asn_strtoimax_lim_loop (str++) fin intp
                                 (digit_to_num Signed i value) Signed last_digit n m
                             | Unsigned => asn_strtoimax_lim_loop (str++) fin intp
                                 (digit_to_num Unsigned i value) Unsigned last_digit n m
                           end
                      else match (Mem.storev Mptr m (vptr fin) (vptr str)) with
                           | Some m' => 
                             Some {| return_type := ASN_STRTOX_ERROR_RANGE;
                                     value := None;
                                     intp := None;                      
                                     memory := Some m' |}
                           | None => None
                           end                          
            else match (Mem.storev Mptr m (vptr fin) (vptr str)) with
                 | Some m' => Some {| return_type := ASN_STRTOX_EXTRA_DATA;
                                     value := Some (mult_sign s value);
                                     intp := Some str;                      
                                     memory := Mem.storev Mint64 m' (vptr intp) (Vlong (mult_sign s value)) |}
                 | None => None
                 end
          | _ => None                
          end
  end.

Definition sign i :=
  if (i == minus_char)%int then Signed else Unsigned.

(* Representing negative and positive int *)
Definition max_sign s :=
  match s with
  | Signed => last_digit_max_minus 
  | Unsigned => last_digit_max
  end.

Definition asn_strtoimax_lim (str fin intp : addr) : option asn_strtoimax_lim_result :=
  match load_addr Mptr m fin with (* derefencing **fin *)
  | Some (Vptr b ofs) =>
    match addr_ge str (b, ofs) with (* compare str and *fin *)
    | Some true => Some {| return_type := ASN_STRTOX_ERROR_INVAL;
                                           value := None;
                                           intp := None;                        
                                           memory := Some m; |}
    | Some false => let dist := distance str (b,ofs) in
                   match load_addr Mint8signed m str with
                   | Some (Vint i) =>
                     if (i == minus_char)%int || (i == plus_char)%int
                     then match addr_ge (str++) (b,ofs) with
                          | Some true =>  Some {| return_type := ASN_STRTOX_EXPECT_MORE;
                                           value := None;
                                           intp := None;                        
                                           memory := (Mem.storev Mptr m (vptr fin) (vptr (str++))); |}

                          | Some false => asn_strtoimax_lim_loop (str++) fin intp 0 (sign i) (max_sign (sign i)) (dist - 1)%nat m
                          | None => None
                          end
                      else asn_strtoimax_lim_loop str fin intp 0 Unsigned last_digit_max dist m
                   | _ => None (* fail of memory load on str: wrong type or not enough permission *)
                   end
    | None => None (* error in pointer comparison *)
    end 
  | _ => None (* fail of pointer to fin *) 
  end.
