Require Import Clight.INTEGER Core.Notations.
Require Import Coq.Program.Basics.
Require Import Core.Core Core.Tactics Core.PtrLemmas Core.Notations.
Require Import StructTact.StructTactics.
Import ListNotations.

Section AbstractSpec.

  Definition minus_char := Byte.repr 45.
  Definition plus_char := Byte.repr 43.
  Definition zero_char := Byte.repr 48.
  Definition nine_char := Byte.repr 57.

  Definition is_digit (i : byte) : bool :=
    ((zero_char <= i) && (i <= nine_char))%byte.

  Definition Z_of_char (b : byte) : Z :=
    Byte.signed b - Byte.signed zero_char.

  Definition is_sign (b : byte) : bool :=
    ((b == plus_char) || (b == minus_char))%byte.

  Definition sign_of_char (b : byte) : Z :=
    if (b == plus_char)%byte then 1
    else if (b == minus_char)%byte then (- 1)
         else 0.

  Definition bounded (n : Z) : bool :=
    andb (Int.min_signed <=? n) (n <=? Int.max_signed).

  Inductive asn_strtox_result_e :=
  | ASN_STRTOX_ERROR_RANGE (* Input outside of supported numeric range *)
  | ASN_STRTOX_ERROR_INVAL (* Invalid data encountered (e.g., "+-") *)
  | ASN_STRTOX_EXPECT_MORE (* More data expected (e.g. "+") *)
  | ASN_STRTOX_EXTRA_DATA  (* Conversion succeded, but the string has extra stuff *)
  | ASN_STRTOX_OK.         (* Conversion succeded, number ends at (end) *)

  (* C light outputs int *)

  Definition asn_strtox_result_e_to_int (s : asn_strtox_result_e) : int :=
    match s with
    | ASN_STRTOX_ERROR_RANGE => Int.repr (-3)
    | ASN_STRTOX_ERROR_INVAL => Int.repr (-2)
    | ASN_STRTOX_EXPECT_MORE => Int.repr (-1)
    | ASN_STRTOX_EXTRA_DATA => Int.repr 1
    | ASN_STRTOX_OK => Int.repr 0
    end.

  Record Z_of_string_result :=
  { res : asn_strtox_result_e ; 
    value : Z ;
    index : Z ;
  }.

  Definition Z_of_string (s : list byte) : Z_of_string_result :=
    let fix Z_of_string_loop s v i :=
        match s with
        | [] => {| res := ASN_STRTOX_OK ;
                   value := v ;
                   index := i |}
        | c :: tl =>
          let i' := Zlength s - Zlength tl - 1 in (* index of c in s *)
          if is_digit c
          then let v1 := v * 10 + (Z_of_char c) in
               if bounded v1
               then Z_of_string_loop tl v1 i
               else {| res := ASN_STRTOX_ERROR_RANGE ;
                       value := v ;
                       index := i' ; |}      
          else {| res := ASN_STRTOX_EXTRA_DATA ;
                  value := v ;
                  index := i' ; |}              
        end
    in match s with
       |  nil => {| res := ASN_STRTOX_ERROR_INVAL ;
                    value := 0 ;
                    index := 0 ; |} 
       | [ch] => if is_sign ch 
                 then {| res := ASN_STRTOX_EXPECT_MORE ;
                         value := 0 ;
                         index := 1 ; |} 
                 else Z_of_string_loop s 0 0
       |  ch :: tl => let result := Z_of_string_loop tl 0 0 in
                     if (ch == plus_char)%byte
                     then result
                     else if (ch == minus_char)%byte
                          then {| res := ASN_STRTOX_OK ;
                                  value := Z.opp (value result) ;
                                  index := index result ; |}
                          else Z_of_string_loop s 0 0
       end.

End AbstractSpec.
