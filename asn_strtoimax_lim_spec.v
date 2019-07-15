From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.
Local Open Scope Z_scope.
Import ListNotations.
Require Import StructTact.StructTactics.


(* Notations for integers and ptrofs *)

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
Notation "x <= y" := (negb (Int.ltu y x)) (at level 70) : IntScope.
Infix "%" := Int.mods (at level 70) : IntScope.
Infix "//" := Int.divs (at level 70) : IntScope.

Delimit Scope PtrofsScope with ptrofs.
Infix "==" := Ptrofs.eq (at level 70) : PtrofsScope.
Notation "x ~= y" := (negb Ptrofs.eq x y) (at level 70) : PtrofsScope.
Notation "x >> y" := (Ptrofs.shru x y) (at level 70) : PtrofsScope.
Notation "0" := Ptrofs.zero : PtrofsScope.
Notation "1" := Ptrofs.one : PtrofsScope.
Infix "+" := Ptrofs.add : PtrofsScope.
Infix "-" := Ptrofs.sub : PtrofsScope.
Infix "*" := Ptrofs.mul : PtrofsScope.
Infix "<" := Ptrofs.lt : PtrofsScope.
Notation "x <= y" := (negb (Ptrofs.ltu y x)) (at level 70) : PtrofsScope.
Infix "%" := Ptrofs.mods (at level 70) : PtrofsScope.
Infix "//" := Ptrofs.divs (at level 70) : PtrofsScope.

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

(* Abstract spec *)

(* [b1,ofs1] >= [b2,ofs2] *)
Definition ptr_ge_spec (b1 b2 : block) (ofs1 ofs2 : ptrofs) :=
  if eq_block b1 b2 then Some (ofs2 <= ofs1)%ptrofs else None.

(* Concrete spec using Compcert semantic values *)

Definition ptr_ge (b1 b2 : block) (ofs1 ofs2 : ptrofs) := if Archi.ptr64
  then Val.cmplu_bool (Mem.valid_pointer m) Cge (Vptr b1 ofs1) (Vptr b2 ofs2)                        else Val.cmpu_bool (Mem.valid_pointer m) Cge (Vptr b1 ofs1) (Vptr b2 ofs2).


Proposition ptr_ge_refine : forall (b1 b2 : block) (ofs1 ofs2 : ptrofs),
    Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
    Mem.weak_valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
    
    ptr_ge_spec b1 b2 ofs1 ofs2 = ptr_ge b1 b2 ofs1 ofs2.
Proof.
  intros.
  unfold ptr_ge.
  simpl; unfold Mem.weak_valid_pointer in *.
  destruct Archi.ptr64 eqn: A; simpl.
  all: rewrite H;
    rewrite H0;
    simpl;
    destruct (Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) &&
                                Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2));
    auto.
Qed.



Definition addr_ge (a1 a2 : addr) := match a1, a2 with (b1,ofs1), (b2,ofs2) => ptr_ge b1 b2 ofs1 ofs2 end.

Definition _end : ident := 152%positive.
Definition _str : ident := 151%positive.
Definition _t'6 : ident := 165%positive.

Definition f_ptr_ge := (Sifthenelse (Ebinop Oge (Etempvar _str (tptr tschar))
                         (Etempvar _end (tptr tschar)) tint)
            (Sreturn (Some (Econst_int (Int.repr (-2)) tint)))
            Sskip).

Proposition ptr_ge_corr : forall b1 b2 ofs1 ofs2, ptr_ge b1 b2 ofs1 ofs2 = Some true ->
                                             exists t le', le!_str = Some (Vptr b1 ofs1) ->
                                                      le!_end = Some (Vptr b2 ofs2) ->                  
      exec_stmt ge e le m f_ptr_ge t le' m (Out_return (Some (Vint (Int.repr (-2)),tint))).
Proof.
  intros until ofs2; intro Spec.
  unfold ptr_ge in Spec.
  repeat eexists.
  intros Fin Str.
  repeat econstructor.
  apply Fin.
  apply Str.
  simpl.
  unfold sem_cmp.
  simpl.
  unfold cmp_ptr.
  assert (option_map Val.of_bool
    (if Archi.ptr64
     then Val.cmplu_bool (Mem.valid_pointer m) Cge (Vptr b1 ofs1) (Vptr b2 ofs2)
     else Val.cmpu_bool (Mem.valid_pointer m) Cge (Vptr b1 ofs1) (Vptr b2 ofs2)) = (option_map Val.of_bool (Some true))).
  f_equal.
  assumption.
    eapply H.
    simpl.
    econstructor.
    econstructor.
    econstructor.
    Qed.
    
(* We are reading a char type from the memory *)
Definition chunk := Mint8signed : memory_chunk.
Definition load_addr (m : mem) (a : addr) := match a with (b,ofs) =>  Mem.loadv chunk m (Vptr b ofs) end.
Definition next_addr (a : addr) := match a with (b,ofs) => (b, Ptrofs.add ofs Ptrofs.one) end.
Notation "a ++" := (next_addr a) (at level 20).
Notation minus_char := (Int.repr 45).
Notation plus_char := (Int.repr 43).
Notation zero_char := (Int.repr 48).

Definition ASN1_INTMAX_MAX :=(Int.not 0) >> 1.

Fact shift_pow2_div :  (Int64.shru (Int64.not Int64.zero) Int64.one) = Int64.repr (Int64.max_unsigned / 2).
  replace (Int64.not Int64.zero) with (Int64.repr Int64.max_unsigned) by (auto with ints).
  unfold Int64.shru.
  f_equal.
  Qed.

Definition upper_boundary := ASN1_INTMAX_MAX // (Int.repr 10).
Definition last_digit_max_plus := ASN1_INTMAX_MAX % (Int.repr 10).
Definition last_digit_max_minus := (ASN1_INTMAX_MAX % (Int.repr 10)) + 1.
(* [0-9]*)
Definition digits := map Int.repr [48;49;50;51;52;53;54;55;56;57].

Definition distance (a1 a2 : addr) : nat :=
  ((Z.to_nat (Ptrofs.unsigned (snd a1))) - (Z.to_nat (Ptrofs.unsigned (snd a1))))%nat.

(* Functional spec *)

Fixpoint asn_strtoimax_lim_loop (str : addr) (fin : addr) (value : int) (s: signedness) (last_digit : int) (dist : nat) {struct dist} : option (asn_strtox_result_e*option (addr*int*signedness))  :=
   match dist with
   | O => Some (ASN_STRTOX_OK, Some (str, value, s))
   | S n => match load_addr m str with
           | Some (Vint i) => if existsb (fun j => Int.eq i j) digits then
                      let d := i - zero_char in
                      let v := (value*(Int.repr 10) + d) in
                      if value < upper_boundary
                      then asn_strtoimax_lim_loop (str++) fin v s last_digit n
                      else if (value == upper_boundary) && (d <= last_digit)
                           then asn_strtoimax_lim_loop (str++) fin v s last_digit n
                           else Some (ASN_STRTOX_ERROR_RANGE, Some (str,value,s)) 
                      else Some (ASN_STRTOX_EXTRA_DATA, Some (str,value,s))
           | _  => None (* fail of memory load: wrong type or not enough permission *)
            end
  end.

Definition asn_strtoimax_lim (str fin : addr) : option (asn_strtox_result_e*(option(addr*int*signedness))) :=
  match addr_ge str fin with (* compare str and fin *)
  | Some true => Some (ASN_STRTOX_ERROR_INVAL, None)
  | Some false => let dist := distance str fin in
                 match load_addr m str with
                 | Some (Vint i) =>
                   if (i == minus_char)
                   then asn_strtoimax_lim_loop (str++) fin 0 Signed last_digit_max_minus dist
                   else if (i == plus_char)
                        then asn_strtoimax_lim_loop (str++) fin 0 Unsigned last_digit_max_plus dist
                        else asn_strtoimax_lim_loop str fin 0 Unsigned last_digit_max_plus dist
                 | _ => None (* fail of memory load on str: wrong type or not enough permission *)
                 end
  | None => None (* error in pointer comparison *)
  end.

Definition _last_digit_max : ident := 155%positive.
Definition _upper_boundary : ident := 155%positive.
Definition _value : ident := 29%positive.
Definition _t'1 : ident := 160%positive.
Definition _t'2 : ident := 161%positive.
Definition _t'3 : ident := 162%positive.
Definition _t'4 : ident := 163%positive.
Definition _t'5 : ident := 164%positive.
Definition _sign : ident := 168%positive.
Definition _intp : ident := 169%positive.
Definition _d : ident := 170%positive.


Definition f_asn_strtoimax_lim := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: (_end, (tptr (tptr tschar))) ::
                (_intp, (tptr tlong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_sign, tint) :: (_value, tlong) ::
               (_upper_boundary, tlong) :: (_last_digit_max, tlong) ::
               (_d, tint) :: (_t'6, (tptr tschar)) ::
               (_t'5, (tptr tschar)) :: (_t'4, tschar) ::
               (_t'3, (tptr tschar)) :: (_t'2, tschar) :: (_t'1, tschar) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _sign (Econst_int (Int.repr 1) tint))
  (Ssequence
    (Sset _upper_boundary
      (Ebinop Odiv
        (Ebinop Oshr
          (Eunop Onotint (Ecast (Econst_int (Int.repr 0) tint) tulong)
            tulong) (Econst_int (Int.repr 1) tint) tulong)
        (Econst_int (Int.repr 10) tint) tulong))
    (Ssequence
      (Sset _last_digit_max
        (Ebinop Omod
          (Ebinop Oshr
            (Eunop Onotint (Ecast (Econst_int (Int.repr 0) tint) tulong)
              tulong) (Econst_int (Int.repr 1) tint) tulong)
          (Econst_int (Int.repr 10) tint) tulong))
      (Ssequence
        (Ssequence
          (Sset _t'6
            (Ederef (Etempvar _end (tptr (tptr tschar))) (tptr tschar)))
          (Sifthenelse (Ebinop Oge (Etempvar _str (tptr tschar))
                         (Etempvar _t'6 (tptr tschar)) tint)
            (Sreturn (Some (Econst_int (Int.repr (-2)) tint)))
            Sskip))
        (Ssequence
          (Ssequence
            (Sset _t'4 (Ederef (Etempvar _str (tptr tschar)) tschar))
            (Sswitch (Ederef (Etempvar _str (tptr tschar)) tschar)
              (LScons (Some 45)
                (Ssequence
                  (Sset _last_digit_max
                    (Ebinop Oadd (Etempvar _last_digit_max tlong)
                      (Econst_int (Int.repr 1) tint) tlong))
                  (Sset _sign
                    (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
                (LScons (Some 43)
                  (Ssequence
                    (Sset _str
                      (Ebinop Oadd (Etempvar _str (tptr tschar))
                        (Econst_int (Int.repr 1) tint) (tptr tschar)))
                    (Ssequence
                      (Sset _t'5
                        (Ederef (Etempvar _end (tptr (tptr tschar)))
                          (tptr tschar)))
                      (Sifthenelse (Ebinop Oge (Etempvar _str (tptr tschar))
                                     (Etempvar _t'5 (tptr tschar)) tint)
                        (Ssequence
                          (Sassign
                            (Ederef (Etempvar _end (tptr (tptr tschar)))
                              (tptr tschar)) (Etempvar _str (tptr tschar)))
                          (Sreturn (Some (Econst_int (Int.repr (-1)) tint))))
                        Sskip)))
                  LSnil))))
          (Ssequence
            (Ssequence
              (Sset _value (Ecast (Econst_int (Int.repr 0) tint) tlong))
              (Sloop
                (Ssequence
                  (Ssequence
                    (Sset _t'3
                      (Ederef (Etempvar _end (tptr (tptr tschar)))
                        (tptr tschar)))
                    (Sifthenelse (Ebinop Olt (Etempvar _str (tptr tschar))
                                   (Etempvar _t'3 (tptr tschar)) tint)
                      Sskip
                      Sbreak))
                  (Ssequence
                    (Sset _t'1 (Ederef (Etempvar _str (tptr tschar)) tschar))
                    (Sswitch (Ederef (Etempvar _str (tptr tschar)) tschar)
                      (LScons (Some 48)
                        Sskip
                        (LScons (Some 49)
                          Sskip
                          (LScons (Some 50)
                            Sskip
                            (LScons (Some 51)
                              Sskip
                              (LScons (Some 52)
                                Sskip
                                (LScons (Some 53)
                                  Sskip
                                  (LScons (Some 54)
                                    Sskip
                                    (LScons (Some 55)
                                      Sskip
                                      (LScons (Some 56)
                                        Sskip
                                        (LScons (Some 57)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'2
                                                (Ederef
                                                  (Etempvar _str (tptr tschar))
                                                  tschar))
                                              (Sset _d
                                                (Ebinop Osub
                                                  (Etempvar _t'2 tschar)
                                                  (Econst_int (Int.repr 48) tint)
                                                  tint)))
                                            (Ssequence
                                              (Sifthenelse (Ebinop Olt
                                                             (Etempvar _value tlong)
                                                             (Etempvar _upper_boundary tlong)
                                                             tint)
                                                (Sset _value
                                                  (Ebinop Oadd
                                                    (Ebinop Omul
                                                      (Etempvar _value tlong)
                                                      (Econst_int (Int.repr 10) tint)
                                                      tlong)
                                                    (Etempvar _d tint) tlong))
                                                (Sifthenelse (Ebinop Oeq
                                                               (Etempvar _value tlong)
                                                               (Etempvar _upper_boundary tlong)
                                                               tint)
                                                  (Sifthenelse (Ebinop Ole
                                                                 (Etempvar _d tint)
                                                                 (Etempvar _last_digit_max tlong)
                                                                 tint)
                                                    (Sifthenelse (Ebinop Ogt
                                                                   (Etempvar _sign tint)
                                                                   (Econst_int (Int.repr 0) tint)
                                                                   tint)
                                                      (Sset _value
                                                        (Ebinop Oadd
                                                          (Ebinop Omul
                                                            (Etempvar _value tlong)
                                                            (Econst_int (Int.repr 10) tint)
                                                            tlong)
                                                          (Etempvar _d tint)
                                                          tlong))
                                                      (Ssequence
                                                        (Sset _sign
                                                          (Econst_int (Int.repr 1) tint))
                                                        (Sset _value
                                                          (Ebinop Osub
                                                            (Ebinop Omul
                                                              (Eunop Oneg
                                                                (Etempvar _value tlong)
                                                                tlong)
                                                              (Econst_int (Int.repr 10) tint)
                                                              tlong)
                                                            (Etempvar _d tint)
                                                            tlong))))
                                                    (Ssequence
                                                      (Sassign
                                                        (Ederef
                                                          (Etempvar _end (tptr (tptr tschar)))
                                                          (tptr tschar))
                                                        (Etempvar _str (tptr tschar)))
                                                      (Sreturn (Some (Econst_int (Int.repr (-3)) tint)))))
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Etempvar _end (tptr (tptr tschar)))
                                                        (tptr tschar))
                                                      (Etempvar _str (tptr tschar)))
                                                    (Sreturn (Some (Econst_int (Int.repr (-3)) tint))))))
                                              Scontinue))
                                          (LScons None
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Etempvar _end (tptr (tptr tschar)))
                                                  (tptr tschar))
                                                (Etempvar _str (tptr tschar)))
                                              (Ssequence
                                                (Sassign
                                                  (Ederef
                                                    (Etempvar _intp (tptr tlong))
                                                    tlong)
                                                  (Ebinop Omul
                                                    (Etempvar _sign tint)
                                                    (Etempvar _value tlong)
                                                    tlong))
                                                (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
                                            LSnil))))))))))))))
                (Sset _str
                  (Ebinop Oadd (Etempvar _str (tptr tschar))
                    (Econst_int (Int.repr 1) tint) (tptr tschar)))))
            (Ssequence
              (Sassign
                (Ederef (Etempvar _end (tptr (tptr tschar))) (tptr tschar))
                (Etempvar _str (tptr tschar)))
              (Ssequence
                (Sassign (Ederef (Etempvar _intp (tptr tlong)) tlong)
                  (Ebinop Omul (Etempvar _sign tint) (Etempvar _value tlong)
                    tlong))
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))
                                 |}.

Definition vptr (a : addr) := match a with (b,ofs) => Vptr b ofs end.

Theorem asn_strtoimax_lim_correct : forall str fin value, 
    asn_strtoimax_lim str fin = Some (ASN_STRTOX_OK, Some (str, value, Unsigned)) ->
    exists t le', le!_str = Some (vptr str)  ->
             le!_end = Some (vptr fin) ->
      
             exec_stmt ge e le m f_asn_strtoimax_lim.(fn_body) t le' m (Out_return (Some (Vint (asn_strtox_result_e_to_int ASN_STRTOX_OK), tint)))
             /\ le'!_intp = Some (Vint value)
             /\ le'!_end = Some (vptr str).
  
              




