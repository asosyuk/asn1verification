From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.
Local Open Scope Z_scope.

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

Check Val.cmpu_bool.

Variable valid_ptr: block -> Z -> bool.

Definition asn_strtoimax_lim_spec_64 (m : Mem.mem) (b_str : block) (ofs_str : ptrofs)
           (b_end : block) (ofs_end : ptrofs) : option (Int.int*block*ptrofs) :=
  let ASN1_INTMAX_MAX := Int64.shru (Int64.not Int64.zero) Int64.one in
        match  Val.cmpu_bool valid_ptr Cge (Vptr b_str ofs_str) (Vptr b_end ofs_str) with
        | Some true => Some (asn_strtox_result_e_to_int ASN_STRTOX_ERROR_INVAL, b_end, ofs_end)            | _ => None
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
