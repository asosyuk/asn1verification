From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.
Local Open Scope Z_scope.
Import ListNotations.

(* Notations for integers *)

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
Parameter m : mem.
Parameter ge : genv.
Parameter e : env.
Parameter le : temp_env.

(* Pointer comparison *)
Definition ptr_ge (a1 a2: addr) : option bool :=
 match a1,a2 with (b1,ofs1), (b2,ofs2) =>
                  if Archi.ptr64                                                   then Val.cmplu_bool (Mem.valid_pointer m) Cge (Vptr b1 ofs1) (Vptr b2 ofs2)                                                       else Val.cmpu_bool (Mem.valid_pointer m) Cge (Vptr b1 ofs1) (Vptr b2 ofs2)
 end.

Definition _end : ident := 152%positive.
Definition _str : ident := 151%positive.
Definition _t'6 : ident := 165%positive.

Definition f_ptr_ge := (Sifthenelse (Ebinop Oge (Etempvar _str (tptr tschar))
                         (Etempvar _end (tptr tschar)) tint)
            (Sreturn (Some (Econst_int (Int.repr (-2)) tint)))
            Sskip).

(** [break_if] finds instances of [if _ then _ else _] in your goal or
    context, and destructs the discriminee, while retaining the
    information about the discriminee's value leading to the branch
    being taken. *)
Ltac break_if :=
  match goal with
    | [ |- context [ if ?X then _ else _ ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
    | [ H : context [ if ?X then _ else _ ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

(** [break_let] breaks a destructuring [let] for a pair. *)
Ltac break_let :=
  match goal with
    | [ H : context [ (let (_,_) := ?X in _) ] |- _ ] => destruct X eqn:?
    | [ |- context [ (let (_,_) := ?X in _) ] ] => destruct X eqn:?
end.

Ltac break_match_hyp :=
  match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

Proposition ptr_ge_corr : forall a1 a2, ptr_ge a1 a2 = Some true -> exists t le',
      le!_str = Some (Vptr (fst a1) (snd a1)) ->
      le!_end = Some (Vptr (fst a2) (snd a2)) ->                  
      exec_stmt ge e le m f_ptr_ge t le' m (Out_return (Some (Vint (Int.repr (-2)),tint))).
Proof.
  intros str fin Spec.
   unfold ptr_ge in Spec.
  (*assert (Archi.ptr64 = false) as A by (simpl; auto); rewrite A in Spec. *)
  repeat break_let.
  (* repeat break_if. subst. *)
  repeat eexists.
  intros Fin Str.
  repeat econstructor.
  apply Fin.
  apply Str.
  simpl.
  unfold sem_cmp.
  simpl.
  unfold cmp_ptr.
  pose (option_map Val.of_bool (if Archi.ptr64
          then
           Val.cmplu_bool (Mem.valid_pointer m) Cge 
             (Vptr b i) (Vptr b0 i0)
          else
           Val.cmpu_bool (Mem.valid_pointer m) Cge 
             (Vptr b i) (Vptr b0 i0))).
    assert ( (option_map Val.of_bool (if Archi.ptr64
          then
           Val.cmplu_bool (Mem.valid_pointer m) Cge 
             (Vptr b i) (Vptr b0 i0)
          else
           Val.cmpu_bool (Mem.valid_pointer m) Cge 
                         (Vptr b i) (Vptr b0 i0))) = (option_map Val.of_bool (Some true))).
    f_equal.
    assumption.
    eapply H.
    simpl.
    econstructor.
    econstructor.
    econstructor.
    Qed.
    
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

(* The spec close to C code *)

Program Fixpoint asn_strtoimax_lim_loop (str : addr) (fin : addr) (value : int) (s: signedness) (last_digit_m : int) {measure (distance str fin) } : option (asn_strtox_result_e*addr*int*signedness)  :=
  if Nat.eq_dec (distance str fin) O then Some (ASN_STRTOX_OK, str, value, s) else
  match load_addr m str with
  | Some (Vint i) => if existsb (fun j => Int.eq i j) digits then
                      let d := i - zero_char in
                      let v := (value*(Int.repr 10) + d) in
                      if value < upper_boundary then asn_strtoimax_lim_loop (str++) fin v s last_digit_m
                      else if (value == upper_boundary) && (d <= last_digit_m)
                           then  asn_strtoimax_lim_loop (str++) fin v s last_digit_m
                           else Some (ASN_STRTOX_ERROR_RANGE,str,value,s) 
                      else Some (ASN_STRTOX_EXTRA_DATA, str,value,s)
  | _  => None (* fail of memory load: wrong type or not enough permission *)
  end.
Admit Obligations.

Definition asn_strtoimax_lim (str fin : addr) (last_digit_max: int) : option (asn_strtox_result_e*addr*int*signedness) :=
  match ptr_ge str fin with
  | Some true => None (* error *)
  | Some false => match load_addr m str with
                 | Some (Vint i) =>
                   if (i == minus_char)
                   then asn_strtoimax_lim_loop (str++) fin 0 Signed (last_digit_max + 1)
                   else if (i == plus_char)
                        then asn_strtoimax_lim_loop (str++) fin 0 Unsigned last_digit_max
                        else asn_strtoimax_lim_loop str fin 0 Unsigned last_digit_max                      
                 | _ => None (* fail of memory load: wrong type or not enough permission *)
                 end
  | None => None (* error in pointer comparison *)
  end.


  
Fact shift_pow2_div :  (Int64.shru (Int64.not Int64.zero) Int64.one) = Int64.repr (Int64.max_unsigned / 2).
  replace (Int64.not Int64.zero) with (Int64.repr Int64.max_unsigned) by (auto with ints).
  unfold Int64.shru.
  f_equal.
  Qed.


