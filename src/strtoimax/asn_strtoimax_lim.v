From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.

(* f_asn_strtoimax_lim C light AST *)

Definition _end : ident := 152%positive.
Definition _str : ident := 151%positive.
Definition _t'6 : ident := 165%positive.    
Definition _last_digit_max : ident := 155%positive.
Definition _upper_boundary : ident := 159%positive.
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

Definition f_asn_strtoimax_lim_loop :=
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
                          (Econst_int (Int.repr 1) tint) (tptr tschar)))).


Notation set_vars_switch_body := (Ssequence
                                              (Sset _t'2
                                                (Ederef
                                                  (Etempvar _str (tptr tschar))
                                                  tschar))
                                              (Sset _d
                                                (Ebinop Osub
                                                  (Etempvar _t'2 tschar)
                                                  (Econst_int (Int.repr 48) tint)
                                                  tint))).

Notation if_then_else_bound := (Sifthenelse (Ebinop Olt
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
                                                    (Sreturn (Some (Econst_int (Int.repr (-3)) tint)))))).

Notation switch_body := (Ssequence
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
                                              Scontinue)). 
Notation switch_default :=
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
                                                (Sreturn (Some (Econst_int (Int.repr 1) tint))))).

Definition pre_loop s2 s3 := (Ssequence
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
                  LSnil)))) (Ssequence
            (Ssequence
              (Sset _value (Ecast (Econst_int (Int.repr 0) tint) tlong)) s2 ) s3)))))).
