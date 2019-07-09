From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.
Local Open Scope Z_scope.
Import ListNotations.

Delimit Scope IntScope with int.
Infix "==" := Int.eq (at level 70) : IntScope.
Notation "x ~= y" := (negb Int.eq x y) (at level 70) : IntScope.
Notation "x >> y" := (Int.shru x y) (at level 70) : IntScope.
Notation "0" := Int.zero : IntScope.
Notation "1" := Int.one : IntScope.
Infix "+" := Int.add : IntScope.
Infix "-" := Int.sub : IntScope.
Infix "*" := Int.mul : IntScope.
Infix "<" := Int.lt : IntScope.
Notation "x <= y" := (negb (Int.lt y x)) (at level 70) : IntScope.
Infix "%" := Int.mods (at level 70) : IntScope.
Infix "//" := Int.divs (at level 70) : IntScope.
Local Open Scope IntScope.


(* Functional specification of INTEGER.asn_strtoimax_lim
 
 Parse the number in the given string until the given end position,
  returning the position after the last parsed character back using the
  same (end) pointer. WARNING: This behavior is different from the standard strtol/strtoimax(3). *)

(* Output type of asn_strtoimax_lim *)

Inductive asn_strtox_result_e :=
  | ASN_STRTOX_ERROR_RANGE (* Input outside of supported numeric range *)
  | ASN_STRTOX_ERROR_INVAL (* Invalid data encountered (e.g., "+-") *)
  | ASN_STRTOX_EXPECT_MORE (* More data expected (e.g. "+") *)
  | ASN_STRTOX_EXTRA_DATA (* Conversion succeded, but the string has extra stuff *)
  | ASN_STRTOX_OK. (* Conversion succeded, number ends at (end) *) 

Definition asn_strtox_result_e_to_int (s : asn_strtox_result_e) : int :=
  match s with
    | ASN_STRTOX_ERROR_RANGE => Int.repr (-1)  
    | ASN_STRTOX_ERROR_INVAL => Int.repr (-3)
    | ASN_STRTOX_EXPECT_MORE => Int.repr (-2)
    | ASN_STRTOX_EXTRA_DATA => Int.repr 1 
    | ASN_STRTOX_OK => Int.repr 0
  end.

Definition addr : Type := (block*ptrofs).

(* Predicate stating that there is a C string of length n at address a1 
Inductive Cstring (m : mem) (b : block) (ofs : ptrofs) : nat -> Prop :=
| EmptyString: Mem.loadv Mint8signed m (Vptr b ofs) = Some (Vint Int.zero) -> Cstring m b ofs O
| SuccString: forall n c, Mem.loadv Mint8signed m (Vptr b ofs)  = Some (Vint c) ->
                        c <> Int.zero ->
                        Cstring m b (Ptrofs.add ofs Ptrofs.one) n ->
                        Cstring m b ofs (S n). *)
  
(* Formalize intmax_t and uintmax_t ??? Maybe use module types? *)

(* /* Largest integral types.  */
#if __WORDSIZE == 64
typedef long int		intmax_t;
typedef unsigned long int	uintmax_t;
#else
__extension__
typedef long long int		intmax_t;
__extension__
typedef unsigned long long int	uintmax_t;
#endif 
*)

Inductive intsize : Type :=
  | I8: intsize
  | I32: intsize
  | I64 : intsize.

Definition intmax_t (s : intsize) := match s with | I64 => Int64.int | I32 => Int.int | I8 => Byte.int end.

(* Placeholder for pointer comparison *)
Hypothesis ptr_ge : addr -> addr -> bool.
Parameter m : mem.
(* we are reading a char type from the memory *)
Definition chunk := Mint8signed : memory_chunk.

Definition load_addr (m : mem) (a : addr) := match a with (b,ofs) =>  Mem.loadv chunk m (Vptr b ofs) end.
Definition next_addr (a : addr) := match a with (b,ofs) => (b, Ptrofs.add ofs Ptrofs.one) end.
Notation "a ++" := (next_addr a) (at level 20).
Notation minus_char := (Int.repr 45).
Notation plus_char := (Int.repr 43).
Notation zero_char := (Int.repr 48).


Definition ASN1_INTMAX_MAX :=(Int.not 0) >> 1.
Definition upper_boundary := ASN1_INTMAX_MAX // (Int.repr 10).
Definition last_digit_max_plus := ASN1_INTMAX_MAX % (Int.repr 10).
Definition last_digit_max_minus := (ASN1_INTMAX_MAX % (Int.repr 10)) + 1.
(* [0-9]*)
Definition digits := map Int.repr [48;49;50;51;52;53;54;55;56;57].

Definition distance (a1 a2 : addr) : nat :=
  ((Z.to_nat (Ptrofs.unsigned (snd a1))) - (Z.to_nat (Ptrofs.unsigned (snd a1))))%nat.

Program Fixpoint loop_spec (str : addr) (fin : addr) (value : int) (s: signedness) {measure (distance str fin) } : option (asn_strtox_result_e*addr*int*signedness)  :=
  if Nat.eq_dec (distance str fin) O then Some (ASN_STRTOX_OK, str, value, s) else
  match load_addr m str with
  | Some (Vint i) => if existsb (fun j => Int.eq i j) digits then
                      let d := i - zero_char in
                      let v := (value*(Int.repr 10) + d) in
                      if value < upper_boundary then loop_spec (str++) fin v s
                      else if (value == upper_boundary) && (d <= last_digit_max_plus)
                           then loop_spec (str++) fin v s
                           else Some (ASN_STRTOX_ERROR_RANGE,str,value,s) 
                      else Some (ASN_STRTOX_EXTRA_DATA, str,value,s)
  | _  => None (* fail of memory load: wrong type or not enough permission *)
  end.

(* Program Fixpoint asn_strtoimax_lim_spec (str : addr) (fin : addr) (value : int) (last_digit_max: int) : option (asn_strtox_result_e*addr*int*signedness) :=
  if ptr_ge str p_end then (Some ASN_STRTOX_ERROR_INVAL,None)
  else match load_addr m str with
       | Some (Vint i) =>
         if (Int.eq i minus_char)
         then asn_strtoimax_lim_spec m (str++) fin value last_digit_max_minus
         else if (Int.eq i minus_char) then
         asn_strtoimax_lim_spec m (str++) fin value last_digit_max_plus
       | _ => (None, None)(* do loop *)   
      end          
  end. *)



Variable valid_ptr: block -> Z -> bool.


Definition asn_strtoimax_lim_spec_64 (m : Mem.mem) (b_str : block) (ofs_str : ptrofs)
           (b_end : block) (ofs_end : ptrofs) : option (Int.int*val) :=
  
  let ASN1_INTMAX_MAX := Int64.shru (Int64.not Int64.zero) Int64.one in
  
  match  Val.cmpu_bool valid_ptr Cge (Vptr b_str ofs_str) (Vptr b_end ofs_str) with
    
  | Some true => Some (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_INVAL,  (Vptr b_end ofs_str))   
  | None => None (* failed comparison *)
        end.

Definition asn_strtoimax_lim_spec_INT_TYPE (s : intsize) (m : Mem.mem) (pstr : addr) (pend : addr) : option (Int.int*addr) :=
  match s with
  | I64 => asn_strtoimax_lim_spec_64 m pstr pend
  | _ =>  Some (Int.zero, pend)
  end.
  
  
Fact shift_pow2_div :  (Int64.shru (Int64.not Int64.zero) Int64.one) = Int64.repr (Int64.max_unsigned / 2).
  replace (Int64.not Int64.zero) with (Int64.repr Int64.max_unsigned) by (auto with ints).
  unfold Int64.shru.
  f_equal.
  Qed.
  
  
  




(* STRTOIMAX(3)               Linux Programmer's Manual              STRTOIMAX(3)

NAME
       strtoimax, strtoumax - convert string to integer

SYNOPSIS
       #include <inttypes.h>

       intmax_t strtoimax(const char *nptr, char **endptr, int base);
       uintmax_t strtoumax(const char *nptr, char **endptr, int base);

DESCRIPTION
       These  functions  are  just  like strtol(3) and strtoul(3), except that
       they return a value of type intmax_t and uintmax_t, respectively.

RETURN VALUE
       On success, the converted value is returned.  If nothing was  found  to
       convert, zero is returned.  On overflow or underflow INTMAX_MAX or INT‐
       MAX_MIN or UINTMAX_MAX is returned, and errno is set to ERANGE.
 *)

(* /* Largest integral types.  */
#if __WORDSIZE == 64
typedef long int		intmax_t;
typedef unsigned long int	uintmax_t;
#else
__extension__
typedef long long int		intmax_t;
__extension__
typedef unsigned long long int	uintmax_t;
#endif 

*)
