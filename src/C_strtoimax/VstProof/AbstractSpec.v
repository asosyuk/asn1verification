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

Section ClikeSpec.

Definition ASN1_INTMAX_MAX := Int64.max_signed.
Definition upper_boundary := Z.div ASN1_INTMAX_MAX 10.
Definition last_digit_max := Zmod ASN1_INTMAX_MAX 10.
Definition last_digit_max_minus := last_digit_max + 1.

Definition app_char (b : bool) v c := 
  if b then  v * 10 + (Z_of_char c) else -v * 10 - (Z_of_char c).

Definition last_digit (b : bool) := 
  if b then last_digit_max else last_digit_max_minus.

Fixpoint Z_of_string_loop_C (s : list byte) (v i : Z) (b : bool):= 
    match s with 
    | [] => {| res := OK ; 
              value := v ; 
              index := i |}
    | c :: tl => 
      if is_digit c
      then let d := (Z_of_char c) in 
           if (v <? upper_boundary) 
           then Z_of_string_loop_C tl (v * 10 + d) (i + 1) b
           else if ((v =? upper_boundary)&&(d <=? (last_digit b)))%bool
                then let v1 := app_char b v c in
                     match tl with
                     | [] => {| res := OK ; 
                               value := v1 ; 
                               index := (i + 1) |}
                     | c :: tl => if is_digit c
                                 then {| res := ERROR_RANGE ;
                                         value := v1;
                                         index := (i + 1) ; |}
                                 else {| res := EXTRA_DATA;
                                         value := v1 ;
                                         index := (i + 1) ; |}
                     end
                else {| res := ERROR_RANGE ;
                        value := v ;
                        index := i ; |}      
      else {| res := EXTRA_DATA ;
              value := v ;
              index := i ; |}              
    end.

Definition Z_of_string_C (s : list byte) : Z_of_string_result := 
  match s with 
  |  nil => {| res := ERROR_INVAL ; 
              value := 0 ;
              index := 0 ; |} 
  | [ch] => if is_sign ch 
           then {| res := EXPECT_MORE ;
                   value := 0 ;
                   index := 1 ; |} 
           else Z_of_string_loop_C s 0 0 true
  |  ch :: tl => let result := Z_of_string_loop_C tl 0 1 true in
               if (Byte.signed ch =? plus_char)
               then result
               else if (Byte.signed ch =? minus_char)
                    then let v := value (Z_of_string_loop_C tl 0 1 false) in 
                         {| res := res result ;
                            value := if 0 <? v then (-1*v) else v  ;
                            index := index result ; |}
                    else Z_of_string_loop_C s 0 0 true
  end.

End ClikeSpec.

Section AbstractSpec''.

 Fixpoint Z_of_string_loop'' (s : list byte) (v i : Z) (b : bool) := 
    match s with 
    | [] => {| res := OK ; 
              value := v ; 
              index := i |}
    | c :: tl => 
      if is_digit c
      then let v1 := app_char b v c in 
           if bounded v1
           then Z_of_string_loop'' tl v1 (i + 1) b
           else {| res := ERROR_RANGE ;
                   value := v ;
                   index := i ; |}      
      else {| res := EXTRA_DATA ;
              value := v ;
              index := i ; |}              
    end.


  Definition Z_of_string'' (s : list byte) : Z_of_string_result := 
      match s with 
      |  nil => {| res := ERROR_INVAL ; 
                  value := 0 ;
                  index := 0 ; |} 
      | [ch] => if is_sign ch 
                then {| res := EXPECT_MORE ;
                        value := 0 ;
                        index := 1 ; |} 
                else Z_of_string_loop'' s 0 0 true
      |  ch :: tl => if (Byte.signed ch =? plus_char)
                    then  Z_of_string_loop'' tl 0 1 true
                    else if (Byte.signed ch =? minus_char)
                         then Z_of_string_loop'' tl 0 1 false
                         else Z_of_string_loop'' s 0 0 true
      end.

End AbstractSpec''.


Section AbstractSpec'.

  (* true plus, false minus bound *)
  Definition bounded' (b : bool) (n : Z) : bool :=
    if b 
    then andb (0 <=? n) (n <=? Int64.max_signed) 
    else andb (0 <=? n) (n <=? Int64.max_signed + 1).

  Fixpoint Z_of_string_loop' (s : list byte) (v i : Z) (b : bool):= 
    match s with 
    | [] => {| res := OK ; 
              value := v ; 
              index := i |}
    | c :: tl => 
      if is_digit c
      then let v1 := v * 10 + (Z_of_char c) in 
           if bounded' b v1
           then Z_of_string_loop' tl v1 (i + 1) b
           else {| res := ERROR_RANGE ;
                   value := v ;
                   index := i ; |}      
      else {| res := EXTRA_DATA ;
              value := v ;
              index := i ; |}              
    end.


  Definition Z_of_string' (s : list byte) : Z_of_string_result := 
      match s with 
      |  nil => {| res := ERROR_INVAL ; 
                  value := 0 ;
                  index := 0 ; |} 
      | [ch] => if is_sign ch 
                then {| res := EXPECT_MORE ;
                        value := 0 ;
                        index := 1 ; |} 
                else Z_of_string_loop' s 0 0 true
      |  ch :: tl => let result := Z_of_string_loop' tl 0 1 true in
                    if (Byte.signed ch =? plus_char)
                    then result
                    else if (Byte.signed ch =? minus_char)
                         then {| res := res result ;
                                 value := -1* value (Z_of_string_loop' tl 0 1 false)  ;
                                 index := index result ; |}
                         else Z_of_string_loop' s 0 0 true
      end.

End AbstractSpec'.

Lemma aux : forall ls v i, Z_of_string_loop'' ls v i true = 
                      Z_of_string_loop_C ls v i true.
  Proof.
    induction ls.
    - intuition.
    - simpl.
      intros.
      repeat break_if;
        try eapply IHls.
      break_match.
      -- intuition.
      -- break_if.
         simpl.
         bool_rewrite.
         break_if.
         (* contrdiction *)
         admit.
         intuition.
         simpl.
         bool_rewrite.
         intuition.
      --(* contradiction *)
        admit.
      -- (* contradiction *)
        admit.
      -- break_match.
         * (* contradiction *)
           admit.
         * (* contradiction *)
           admit.
Admitted.


Lemma aux' : forall ls v i, Z_of_string_loop' ls v i true = 
                      Z_of_string_loop_C ls v i true.
  Proof.
    induction ls.
    - intuition.
    - simpl.
      intros.
      repeat break_if;
        try eapply IHls.
      break_match.
      -- intuition.
      -- break_if.
         simpl.
         bool_rewrite.
         break_if.
         (* contrdiction *)
         admit.
         intuition.
         simpl.
         bool_rewrite.
         intuition.
      -- (* contradiction *)
        admit.
      -- (* contradiction *)
        admit.
      -- break_match.
         * (* contradiction *)
           admit.
         * (* contradiction *)
           admit.
Admitted.

Ltac Zbool_to_Prop := try (rewrite Z.leb_le ||
                           rewrite Z.leb_gt ||
                           rewrite Z.eqb_eq ||
                           rewrite Z.eqb_neq).

Lemma is_digit_to_Z : forall c, is_digit c = true -> 0 <= Z_of_char c <= 9.
Proof.
  unfold is_digit, Z_of_char.
  intro.
  rewrite andb_true_iff in *.
  repeat Zbool_to_Prop.
  unfold zero_char, nine_char.
  nia.
Qed.

Lemma loop_non_neg : forall ls v i, 0 <= v -> 0 <= value (Z_of_string_loop' ls v i false).
Proof.
  induction ls.
  - intuition.
  - intros.
    simpl.
      repeat break_if;
    simpl; try congruence;
       eapply is_digit_to_Z in Heqb.
    eapply IHls.
    all: nia.
Qed.


  Lemma aux_false : forall ls v i, 
      0 <= v ->
      0 <= value (Z_of_string_loop' ls v i false) ->
      value (Z_of_string_loop' ls v i false) = 
      Z.abs (value (Z_of_string_loop_C ls v i false)).
  Proof.
    induction ls.
    - simpl.
      intros.
      auto with zarith.
      erewrite Z.abs_eq;
        try nia.
    - simpl.
      intros.
      repeat break_if;
        try eapply IHls.
       eapply is_digit_to_Z in Heqb.
       nia.
      eapply loop_non_neg.
        eapply is_digit_to_Z in Heqb.
       nia.
      break_match.
      -- simpl. 
         assert (0 <= v * 10 + Z_of_char a).
         eapply is_digit_to_Z in Heqb.
         nia.
         replace (- v * 10 - Z_of_char a) with
           (- (v * 10 + Z_of_char a))
                 by auto with zarith.
          Search Z.abs Z.opp.
          erewrite Z.abs_opp.
          edestruct  Z.abs_spec with (n :=  v * 10 + Z_of_char a).
          inversion H2.
          nia.
          inversion H2.
          nia.
      -- break_if.
         simpl.
         bool_rewrite.
         break_if.
         (* contrdiction *)
         admit.
         admit.
         simpl.
         bool_rewrite.
         simpl.
          assert (0 <= v * 10 + Z_of_char a).
         eapply is_digit_to_Z in Heqb.
         nia.
         replace (- v * 10 - Z_of_char a) with
           (- (v * 10 + Z_of_char a))
                 by auto with zarith.
          Search Z.abs Z.opp.
          erewrite Z.abs_opp.
          edestruct  Z.abs_spec with (n :=  v * 10 + Z_of_char a).
          inversion H2.
          nia.
          inversion H2.
          nia.
      -- (* contradiction *)
        admit.
      -- (* contradiction *)
        admit.
      --  (* contradiction *)
        admit.
Admitted. 

Lemma Clike_corr : forall ls, Z_of_string' ls = Z_of_string_C ls.
  Proof.
    destruct ls.
    - intuition.
    - simpl.
      repeat break_if;
        try congruence; try eapply aux'.
        simpl. (* contradiction *) admit.
        replace (Z_of_string_loop_C (i0 :: l) 0 1 true) with
            (Z_of_string_loop' (i0 :: l) 0 1 true).
        replace (value (Z_of_string_loop' (i0 :: l) 0 1 false))
                with (Z.abs (value (Z_of_string_loop_C (i0 :: l) 0 1 false))).
        admit.
        erewrite  aux_false.
        auto.
        nia.
        admit.
        eapply aux'.
        erewrite aux_false.
        admit.
        nia.
        admit.
        admit.
Admitted.
                

      
  
