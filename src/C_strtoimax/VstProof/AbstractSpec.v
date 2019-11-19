Require Import Clight.INTEGER Core.Notations.
Require Import Coq.Program.Basics.
Require Import Core.Core Core.Tactics Core.PtrLemmas Core.Notations.
Require Import StructTact.StructTactics.
Import ListNotations.

Section AbstractSpec.

  Definition minus_char := 45.
  Definition plus_char := 43.
  Definition zero_char := 48.
  Definition nine_char := 57.

  Definition is_digit (i : byte) : bool :=
    (zero_char <=? Byte.signed i) && (Byte.signed i <=? nine_char).

  Definition Z_of_char (b : byte) : Z :=
    Byte.signed b - 48.

  Definition is_sign (b : byte) : bool :=
    (Byte.signed b =? plus_char) || (Byte.signed b =? minus_char).

  Definition bounded (n : Z) : bool :=
    andb (Int64.min_signed <=? n) (n <=? Int64.max_signed).

  Inductive asn_strtox_result_e :=
  | ERROR_RANGE (* Input outside of supported numeric range *)
  | ERROR_INVAL (* Invalid data encountered (e.g., "+-") *)
  | EXPECT_MORE (* More data expected (e.g. "+") *)
  | EXTRA_DATA  (* Conversion succeded, but the string has extra stuff *)
  | OK.         (* Conversion succeded, number ends at (end) *)

  (* C light outputs int *)

  Definition asn_strtox_result_e_to_int (s : asn_strtox_result_e) : int :=
    match s with
    | ERROR_RANGE => Int.repr (-3)
    | ERROR_INVAL => Int.repr (-2)
    | EXPECT_MORE => Int.repr (-1)
    | EXTRA_DATA => Int.repr 1
    | OK => Int.repr 0
    end.

  Record Z_of_string_result :=
  { res : asn_strtox_result_e ; 
    value : Z ;
    index : Z ;
  }.
  
  Fixpoint Z_of_string_loop (s : list byte) (v i : Z) := 
    match s with 
    | [] => {| res := OK ; 
              value := v ; 
              index := i |}
    | c :: tl => 
      if is_digit c
      then let v1 := v * 10 + (Z_of_char c) in 
           if bounded v1
           then Z_of_string_loop tl v1 (i + 1)
           else {| res := ERROR_RANGE ;
                   value := v1 ;
                   index := i ; |}      
      else {| res := EXTRA_DATA ;
              value := v ;
              index := i ; |}              
    end.


  Definition Z_of_string (s : list byte) : Z_of_string_result := 
      match s with 
      |  nil => {| res := ERROR_INVAL ; 
                  value := 0 ;
                  index := 0 ; |} 
      | [ch] => if is_sign ch 
                then {| res := EXPECT_MORE ;
                        value := 0 ;
                        index := 1 ; |} 
                else Z_of_string_loop s 0 0
      |  ch :: tl => let result := Z_of_string_loop tl 0 1 in
                    if (Byte.signed ch =? plus_char)
                    then result
                    else if (Byte.signed ch =? minus_char)
                         then {| res := res result ;
                                 value := -1 * (value result) ;
                                 index := index result ; |}
                         else Z_of_string_loop s 0 0
      end.

End AbstractSpec.
