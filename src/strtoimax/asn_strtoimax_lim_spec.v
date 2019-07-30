From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import IntNotations asn_strtoimax_lim IntLemmas Tactics.
Local Open Scope Int64Scope.

(* Functional specification of INTEGER.c/asn_strtoimax_lim *)

(* Informal spec:
 
 Parse the number in the given string until the given end position,
  returning the position after the last parsed character back using the
  same (end) pointer. WARNING: This behavior is different from the standard strtol/strtoimax(3). *)

(* Output type, see INTEGER.h  *)

Inductive asn_strtox_result_e :=
  | ASN_STRTOX_ERROR_RANGE (* Input outside of supported numeric range *)
  | ASN_STRTOX_ERROR_INVAL (* Invalid data encountered (e.g., "+-") *)
  | ASN_STRTOX_EXPECT_MORE (* More data expected (e.g. "+") *)
  | ASN_STRTOX_EXTRA_DATA (* Conversion succeded, but the string has extra stuff *)
  | ASN_STRTOX_OK. (* Conversion succeded, number ends at (end) *) 

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
(* Address [b,ofs] *)
Definition addr : Type := (block*ptrofs).
Definition vptr (a : addr) := match a with (b,ofs) => Vptr b ofs end.
Definition load_addr (chunk : memory_chunk) (m : mem) (a : addr) := match a with (b,ofs) =>  Mem.loadv chunk m (Vptr b ofs) end.
Definition next_addr (a : addr) := match a with (b,ofs) => (b, Ptrofs.add ofs Ptrofs.one) end.
Definition add_addr (a : addr) (i : ptrofs) := match a with (b,ofs) => (b, Ptrofs.add ofs i) end.
Notation "a ++" := (next_addr a) (at level 20).
Notation minus_char := (Int.repr 45).
Notation plus_char := (Int.repr 43).
Notation zero_char := (Int.repr 48).

(* Representing negative and positive int *)
Definition mult_sign s value :=
  match s with
  | Signed => Int64.neg value
  | Unsigned => value
  end.

(* Memory, global and local env are fixed *)
Parameter m : mem.
Parameter ge : genv.
Parameter e : env.

(* Pointer comparison *)
(* Abstract spec : [b1,ofs1] >= [b2,ofs2] *)
Definition ptr_ge_spec (b1 b2 : block) (ofs1 ofs2 : ptrofs) :=
  if eq_block b1 b2 then Some (ofs2 <=u ofs1)%ptrofs else None.
(* Spec using Compcert semantic values *)
Definition ptr_ge (b1 b2 : block) (ofs1 ofs2 : ptrofs) :=
  if Archi.ptr64
  then Val.cmplu_bool (Mem.valid_pointer m) Cge (Vptr b1 ofs1) (Vptr b2 ofs2)
  else Val.cmpu_bool (Mem.valid_pointer m) Cge (Vptr b1 ofs1) (Vptr b2 ofs2).

Definition addr_ge (a1 a2 : addr) := match a1, a2 with (b1,ofs1), (b2,ofs2) => ptr_ge b1 b2 ofs1 ofs2 end.

(* Both specs can be used interchangeably *)
Proposition ptr_ge_refine : forall (b1 b2 : block) (ofs1 ofs2 : ptrofs),
    Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
    Mem.weak_valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
    ptr_ge_spec b1 b2 ofs1 ofs2 = ptr_ge b1 b2 ofs1 ofs2.
Proof.
  intros.
  unfold ptr_ge.
  simpl; unfold Mem.weak_valid_pointer in *.
  destruct Archi.ptr64 eqn: A; simpl.
  all: rewrite H; rewrite H0; simpl;
    destruct (Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) &&
                                Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2)); auto.
Qed.

Definition ASN1_INTMAX_MAX :=(Int64.not 0) >> 1.

Fact shift_pow2_div :  (Int64.shru (Int64.not Int64.zero) Int64.one) = Int64.repr (Int64.max_unsigned / 2).
  replace (Int64.not Int64.zero) with (Int64.repr Int64.max_unsigned) by (auto with ints).
  unfold Int64.shru.
  f_equal.
  Qed.

Definition upper_boundary := ASN1_INTMAX_MAX // (Int64.repr 10).
Definition last_digit_max := ASN1_INTMAX_MAX % (Int64.repr 10).
Definition last_digit_max_minus := (ASN1_INTMAX_MAX % (Int64.repr 10)) + 1.

(* Representing negative and positive int *)
Definition max_sign s :=
  match s with
  | Signed => last_digit_max_minus 
  | Unsigned => last_digit_max
  end.
(* digits [0-9]*)
Definition digits := map Int.repr [48;49;50;51;52;53;54;55;56;57].
Definition is_digit (i : int) := existsb (fun j => Int.eq i j) digits.
(* distance between the addresses *)
Definition distance (a1 a2 : addr) : nat :=
  ((Z.to_nat (Ptrofs.unsigned (snd a2))) - (Z.to_nat (Ptrofs.unsigned (snd a1))))%nat.
Definition int_to_int64 (i : int) := Int64.repr (Int.unsigned i).

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
                 let v := (value*(Int64.repr 10) + d) in
                 if value < upper_boundary
                 then asn_strtoimax_lim_loop (str++) fin intp v s last_digit n m
                 else if (value == upper_boundary) && (d <= last_digit)
                      then asn_strtoimax_lim_loop (str++) fin intp v s last_digit n m
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


Definition asn_strtoimax_lim (str fin intp : addr) : option asn_strtoimax_lim_result :=
  match load_addr Mptr m fin with (* derefencing **fin *)
  | Some (Vptr b ofs) =>
    match addr_ge str (b, ofs) with (* compare str and *fin *)
    | Some true => Some {| return_type := ASN_STRTOX_ERROR_INVAL;
                                           value := None;
                                           intp := None;                        
                                           memory := None; |}
    | Some false => let dist := distance str (b, ofs) in
                   match load_addr Mint8signed m str with
                   | Some (Vint i) =>
                     let s := if (i == minus_char)%int then Signed else Unsigned in 
                     let ldm := if (i == minus_char)%int then last_digit_max_minus else last_digit_max in 
                     match addr_ge (str++) (b, ofs) with
                     | Some true => Some {| return_type := ASN_STRTOX_EXPECT_MORE;
                                           value := None;
                                           intp := None;                        
                                           memory := (Mem.storev Mptr m (vptr fin) (vptr (str++))); |}

                        | Some false => asn_strtoimax_lim_loop (str++) fin intp 0 s ldm (dist - 1)%nat m
                        | None => None
                     end
                   | _ => None (* fail of memory load on str: wrong type or not enough permission *)
                   end
    | None => None (* error in pointer comparison *)
    end
  | _ => None (* fail of pointer to fin *) 
  end.

(* TODO: move storev below *)
(* Fixpoint asn_strtoimax_lim_loop (str fin intp : addr) (value : int64) (s: signedness) (last_digit : int64) (dist : nat) (m' : mem) {struct dist} : option (asn_strtox_result_e*(option(int64*signedness*addr))*(option mem)) :=
  match (Mem.storev Mptr m (vptr fin) (vptr str)) with
    | Some m' =>
      match dist with
      | O => Some (ASN_STRTOX_OK, Some (value,s,str), Mem.storev Mint64 m' (vptr intp) (Vlong (mult_sign s value)))
      | S n => match load_addr Mint8signed m str with
              | Some (Vint i) =>
                if is_digit i
                then let d := int_to_int64 (i - zero_char)%int in
                     let v := (value*(Int64.repr 10) + d) in
                     if value < upper_boundary
                     then asn_strtoimax_lim_loop (str++) fin intp v s last_digit n m
                     else if (value == upper_boundary) && (d <= last_digit)
                       then asn_strtoimax_lim_loop (str++) fin intp v s last_digit n m
                       else Some (ASN_STRTOX_ERROR_RANGE, None, Some m') 
                else Some (ASN_STRTOX_EXTRA_DATA, Some (value,s,str), Mem.storev Mint64 m' (vptr intp) (Vlong (mult_sign s value)))
              | _ => None (* fail or undefined *)
              end

      end
    | _ => None
end.

(* Spec: *)
Definition asn_strtoimax_lim (str fin intp : addr) : option (asn_strtox_result_e*(option(int64*signedness*addr))*(option mem)) :=
  match load_addr Mptr m fin with (* derefencing **fin *)
  | Some (Vptr b ofs) =>
    match addr_ge str (b,ofs) with (* compare str and *fin *)
    | Some true => Some (ASN_STRTOX_ERROR_INVAL, None, None)
    | Some false => let dist := distance str (b,ofs) in
                   match load_addr Mint8signed m str with
                   | Some (Vint i) =>
                     if (i == minus_char)%int
                     then match addr_ge (str++) (b,ofs) with
                          | Some true => Some (ASN_STRTOX_EXPECT_MORE, None, (Mem.storev Mptr m (vptr fin) (vptr (str++))))
                          | Some false => asn_strtoimax_lim_loop (str++) fin intp 0 Signed last_digit_max_minus (dist - 1)%nat m
                          | None => None
                          end
                     else if (i == plus_char)%int
                          then match addr_ge (str++) (b,ofs) with
                               | Some true => Some (ASN_STRTOX_EXPECT_MORE, None, (Mem.storev Mptr m (vptr fin) (vptr (str++))))
                               | Some false => asn_strtoimax_lim_loop (str++) fin intp 0 Unsigned last_digit_max (dist - 1)%nat m
                               | None => None
                               end
                          else asn_strtoimax_lim_loop str fin intp 0 Unsigned last_digit_max dist m
                   | _ => None (* fail of memory load on str: wrong type or not enough permission *)
                   end
    | None => None (* error in pointer comparison *)
    end
  | _ => None (* fail of pointer to fin *) 
  end.
 *)
