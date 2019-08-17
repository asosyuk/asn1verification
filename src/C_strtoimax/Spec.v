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
Definition minus_char := (Int.repr 45).
Definition plus_char := (Int.repr 43).
Definition zero_char := (Int.repr 48).

(* Representing negative and positive int using signedness *)
Definition int_to_int64 (i : int) := Int64.repr (Int.signed i).

Definition Sign s :=
  match s with
  | Signed => (Int.repr (-1))
  | Unsigned => Int.repr 1
  end.

Definition sign i :=
  if (i == minus_char)%int then Signed else Unsigned.

Definition mult_sign s value :=
  match s with
  | Signed =>  ((Int64.repr (-1))*value)%int64
  | Unsigned => value
  end.

(* Converting a single char into into a number given previous value *)
Definition digit_to_num s i v :=
  match s with
  | Signed => (Int64.neg v * (Int64.repr 10) -
               int_to_int64 (i - zero_char)%int)
  | Unsigned => (v * (Int64.repr 10) +
                 int_to_int64 (i - zero_char)%int)
  end.
      
  (* Memory, global and local env are fixed *)
  Variable m : mem.
  Variable ge : genv.
  Variable e : env.

  (* Constants of the function *)
  Definition ASN1_INTMAX_MAX := (Int64.not 0) >> 1.
  Definition upper_boundary := ASN1_INTMAX_MAX // (Int64.repr 10).
  Definition last_digit_max := ASN1_INTMAX_MAX % (Int64.repr 10).
  Definition last_digit_max_minus := (ASN1_INTMAX_MAX % (Int64.repr 10)) + 1.

  Definition max_sign s :=
    match s with
    | Signed => last_digit_max_minus 
    | Unsigned => last_digit_max
    end.
  
  (* digits [0-9]*)
  Definition is_digit (i : int) := andb ((Int.repr 48) <= i)%int ( i <= (Int.repr 57))%int.
  
  (* Executable spec *)

  (* Return type *)
  Record asn_strtoimax_lim_result :=
    { return_type : asn_strtox_result_e ;
      value : option int64 ;
      str_pointer : option addr ;
      memory : option mem ; 
      }.
  

  Fixpoint asn_strtoimax_lim_loop (str fin intp : addr) (value : int64)
           (s: signedness) (last_digit : int64)
           (dist : nat) (m'' : mem) {struct dist} : option asn_strtoimax_lim_result := 
    match dist with
    | O => match (Mem.storev Mptr m'' (vptr fin) (vptr str)) with
          | Some m' => 
            Some {| return_type := ASN_STRTOX_OK;
                    value := Some (mult_sign s value);
                    str_pointer := Some str;
                    memory := Some m'' |}
          | None => None
          end
    | S n => match load_addr Mint8signed m'' str with
            | Some (Vint i) =>
              if is_digit i
              (* if *str >= 0x30 && *str <= 0x39 *)
              then let d := int_to_int64 (i - zero_char)%int in
                   (* int d = *str - '0' *)
                   if value < upper_boundary
                   then asn_strtoimax_lim_loop (str++) fin intp
                        (value * (Int64.repr 10) + d) s last_digit n m
                        (* value = value * 10 + d; next iteration *)
                   else if (value == upper_boundary) && (d <= last_digit_max)
                        (* firstly check if str < *end, and if so, return *)
                        then let value' := digit_to_num s i value in
                             let s' := match s with 
                                       | Signed => Unsigned 
                                       | _ => Unsigned 
                                       end in
                             match (Mem.loadv Mptr m'' (vptr fin)) with
                             | Some (Vptr b fin') =>
                               match addr_lt m'' (str++) (b, fin') with
                               | Some true => match (load_addr Mint8signed m'' 
                                                              (str++)) with
                                          | Some (Vint i') =>
                                            if is_digit i'
                                            then Some {|
                                                     return_type := ASN_STRTOX_ERROR_RANGE;
                                                     value := None;
                                                     str_pointer := None;
                                                     memory := (Mem.storev Mptr m'' 
                                                                           (vptr (b, fin')) 
                                                                           (vptr (str++))) |}
                                            else match Mem.storev Mptr m'' (vptr (b, fin'))
                                                                              (vptr (str++)) with
                                                 | Some m' => 
                                                   Some {| 
                                                       return_type := ASN_STRTOX_EXTRA_DATA; 
                                                       value := Some (mult_sign s' value');
                                                       str_pointer := Some str;
                                                       memory := Mem.storev Mint64 m' (vptr intp)
                                                                  (Vlong (mult_sign s' value')) |}
                                                 | _ => None
                                                 end
                                          | _ => None
                                          end
                               | _ => None
                               end
                             | _ => None
                             end
                        else match (Mem.storev Mptr m'' (vptr fin) (vptr str)) with
                             | Some m' => 
                               Some {| return_type := ASN_STRTOX_ERROR_RANGE;
                                       value := None;
                                       str_pointer := None;
                                       memory := Some m' |}
                             | None => None
                             end                          
              else match (Mem.storev Mptr m'' (vptr fin) (vptr str)) with
                   | Some m' => Some {| return_type := ASN_STRTOX_EXTRA_DATA;
                                        value := Some (mult_sign s value);
                                        str_pointer := Some str;
                                       memory := Mem.storev Mint64 m' (vptr intp) 
                                                            (Vlong (mult_sign s value)) |}
                   | None => None
                   end
            | _ => None                
            end
    end.

Definition store_result s fin intp res :=
  match res with
  | Some {| return_type := ASN_STRTOX_OK;
            value := Some val;
            str_pointer := Some str;
            memory := Some m'; |} =>
    match (Mem.storev Mptr m' (vptr fin) (vptr str)) with
    | Some m'' =>
      Some {| return_type := ASN_STRTOX_OK;
              value := Some (mult_sign s val);
              str_pointer := Some str;
              memory := Mem.storev Mint64 m'' (vptr intp)
                                   (Vlong (mult_sign s val)) |}
    | None => None
    end
  | _ => res
  end.

Definition asn_strtoimax_lim (str fin intp : addr) : option asn_strtoimax_lim_result :=
  match load_addr Mptr m fin with (* derefencing **fin *)
  | Some (Vptr b ofs) =>
    match addr_ge m str (b, ofs) with (* compare str and *fin *)
    | Some true => Some {| return_type := ASN_STRTOX_ERROR_INVAL;
                           value := None;
                           str_pointer := None;
                           memory := Some m; |}
    | Some false => match distance m str (b,ofs) with 
                   | Some dist => 
                     match load_addr Mint8signed m str with 
                     | Some (Vint i) => 
                       if (i == minus_char)%int || (i == plus_char)%int 
                       then match addr_ge m (str++) (b,ofs) with 
                            | Some true => 
                              Some {| return_type := ASN_STRTOX_EXPECT_MORE; 
                                      value := None; 
                                      str_pointer := Some str; 
                                      memory := (Mem.storev Mptr m 
                                                            (vptr fin) 
                                                            (vptr (str++))); |} 
                            | Some false => store_result (sign i) fin intp 
                                                        (asn_strtoimax_lim_loop 
                                                           (str++) fin intp 0 (sign i) 
                                                           (max_sign (sign i)) (dist - 1)%nat m) 
                            | None => None 
                            end 
                       else store_result Unsigned fin intp 
                                         (asn_strtoimax_lim_loop str fin intp 0 
                                                                 Unsigned last_digit_max dist m) 
                     | _ => None (* fail of memory load on str: wrong type or not enough permission *) 
                     end
                   | None => None
                   end
    | None => None (* error in pointer comparison *)
    end
  | _ => None (* fail of pointer to fin *)
  end.

End Spec.
