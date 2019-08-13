Require Import Core.Core Core.Tactics.
Require Import Core.PtrLemmas.
Require Import StructTact.StructTactics.

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
  Definition digits := map Int.repr [48;49;50;51;52;53;54;55;56;57].
  Definition is_digit (i : int) := existsb (fun j => Int.eq i j) digits.
  
  (* Executable spec *)

  (* Return type *)
  Record asn_strtoimax_lim_result :=
    { return_type : asn_strtox_result_e ;
      value : option int64 ;
      memory : option mem ; 
      }.
  
  Fixpoint asn_strtoimax_lim_loop (str fin intp : addr) (value : int64) (s: signedness) (last_digit : int64) (dist : nat) (m'' : mem) {struct dist} : option asn_strtoimax_lim_result :=
    match dist with
    | O => match (Mem.storev Mptr m'' (vptr fin) (vptr str)) with
          | Some m' => 
            Some {| return_type := ASN_STRTOX_OK;
                    value := Some (mult_sign s value);
                    memory := Mem.storev Mint64 m' (vptr intp) (Vlong (mult_sign s value)) |}
          | None => None
          end        
    | S n => match load_addr Mint8signed m'' str with
            | Some (Vint i) =>
              if is_digit i
              then let d := int_to_int64 (i - zero_char)%int in
                   if value < upper_boundary
                   then asn_strtoimax_lim_loop (str++) fin intp
                        (value * (Int64.repr 10) + d) s last_digit n m
                   else if (value == upper_boundary) && (d <= last_digit)
                        then  asn_strtoimax_lim_loop (str++) fin intp
                                   (digit_to_num s i value) s last_digit n m
                        else match (Mem.storev Mptr m'' (vptr fin) (vptr str)) with
                             | Some m' => 
                               Some {| return_type := ASN_STRTOX_ERROR_RANGE;
                                       value := None;
                                       memory := Some m' |}
                             | None => None
                             end                          
              else match (Mem.storev Mptr m'' (vptr fin) (vptr str)) with
                   | Some m' => Some {| return_type := ASN_STRTOX_EXTRA_DATA;
                                       value := Some (mult_sign s value);
                                       memory := Mem.storev Mint64 m' (vptr intp) (Vlong (mult_sign s value)) |}
                   | None => None
                   end
            | _ => None                
            end
    end.

  Definition asn_strtoimax_lim (str fin intp : addr) : option asn_strtoimax_lim_result :=
    match load_addr Mptr m fin with (* derefencing **fin *)
    | Some (Vptr b ofs) =>
      match addr_ge m str (b, ofs) with (* compare str and *fin *)
      | Some true => Some {| return_type := ASN_STRTOX_ERROR_INVAL;
                                             value := None;
                                             memory := Some m; |}
      | Some false => let dist := distance str (b,ofs) in
                     match load_addr Mint8signed m str with
                     | Some (Vint i) =>
                       if (i == minus_char)%int || (i == plus_char)%int
                       then match addr_ge m (str++) (b,ofs) with
                            | Some true =>  Some {| return_type := ASN_STRTOX_EXPECT_MORE;
                                             value := None;
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

(* Abstract specification *)
(* Z or int? *)
Definition Z_of_ascii c := Z.of_nat (Ascii.nat_of_ascii c).

Definition digit_to_Z s i v :=
  match s with
  | Signed => (-v* 10 - ((Z_of_ascii i) - 48))%Z
  | Unsigned => (v * 10 - ((Z_of_ascii i) - 48))%Z
  end.

Definition long_of_ascii c := Int64.repr (Z.of_nat (Ascii.nat_of_ascii c)).
Definition ascii_of_long i := Ascii.ascii_of_nat (Z.to_nat (Int64.unsigned i)).

(* Let abstract string be a list of int *)
Definition string_to_int (s : list int) (sign : signedness) :
  (option int64*asn_strtox_result_e) :=
  let
    fix string_to_int_loop (s : list int) (sign : signedness) (v : int64) :=
    match s with
    | nil => (Some v, ASN_STRTOX_OK)
    | char :: tl => if is_digit char
                  then string_to_int_loop tl sign
                                          (digit_to_num sign char v)
                  else (Some (digit_to_num sign char v),
                        ASN_STRTOX_EXTRA_DATA)                      
    end
  in string_to_int_loop s sign 0.

Definition addr_add (a : addr) (i : ptrofs) := match a with (b,ofs) => (b,(ofs+i)%ptrofs) end.

Fixpoint string_at_address (s : list int) str dist : option (list int) :=
  match dist with
  | O => Some s
  | S n => match load_addr Mint8signed m str with
          | Some (Vint i) => string_at_address (i::s) (str++)  n
          | _ => None
          end
  end.
    
Proposition asn_strtoimax_lim_fun_correct :
  forall dist str_b str_ofs fin_b fin_ofs intp_b intp_ofs m' val sign s,
      dist = distance (str_b, str_ofs) (fin_b, fin_ofs) ->
      string_at_address nil (str_b, str_ofs) dist = Some s ->
      string_to_int s sign = val ->
      m' = Mem.store Mint64 m intp_b (Ptrofs.unsigned intp_ofs)
                     (Vlong (mult_sign sign val)) ->
      
    asn_strtoimax_lim_loop (str_b, str_ofs) (fin_b, fin_ofs) (intp_b, intp_ofs)
                           0 sign (max_sign sign) dist m =
    Some {| return_type := ASN_STRTOX_OK ;
            value := Some (mult_sign sign val) ;
            memory := m' |}.
Proof.
  induction dist; intros.
  simpl in *.
  inversion  H0.
  rewrite <- H4 in H1.
  destruct sign0.
  unfold string_to_int in H1.
  break_match.
  rewrite <- H1.
  econstructor.
    
  unfold asn_strtoimax_lim.
  repeat break_match; try congruence.
  intros.
  split.
  - intro.
    unfold  asn_strtoimax_lim in H.
    repeat break_match; try congruence.
  Admitted.

End Spec.
