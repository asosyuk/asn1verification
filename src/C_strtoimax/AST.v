Require Import Core.Core.
Require Export Clight.INTEGER.

Definition f_asn_strtoimax_lim_loop :=
  (Sloop
                  (Ssequence
                    (Ssequence
                      (Sset _t'9
                        (Ederef (Etempvar _end (tptr (tptr tschar)))
                          (tptr tschar)))
                      (Sifthenelse (Ebinop Olt (Etempvar _str (tptr tschar))
                                     (Etempvar _t'9 (tptr tschar)) tint)
                        Sskip
                        Sbreak))
                    (Ssequence
                      (Ssequence
                        (Sset _t'7
                          (Ederef (Etempvar _str (tptr tschar)) tschar))
                        (Sifthenelse (Ebinop Oge (Etempvar _t'7 tschar)
                                       (Econst_int (Int.repr 48) tint) tint)
                          (Ssequence
                            (Sset _t'8
                              (Ederef (Etempvar _str (tptr tschar)) tschar))
                            (Sset _t'2
                              (Ecast
                                (Ebinop Ole (Etempvar _t'8 tschar)
                                  (Econst_int (Int.repr 57) tint) tint)
                                tbool)))
                          (Sset _t'2 (Econst_int (Int.repr 0) tint))))
                      (Sifthenelse (Etempvar _t'2 tint)
                        (Ssequence
                          (Ssequence
                            (Sset _t'6
                              (Ederef (Etempvar _str (tptr tschar)) tschar))
                            (Sset _d
                              (Ebinop Osub (Etempvar _t'6 tschar)
                                (Econst_int (Int.repr 48) tint) tint)))
                          (Sifthenelse (Ebinop Olt (Etempvar _value tlong)
                                         (Etempvar _upper_boundary tlong)
                                         tint)
                            (Sset _value
                              (Ebinop Oadd
                                (Ebinop Omul (Etempvar _value tlong)
                                  (Econst_int (Int.repr 10) tint) tlong)
                                (Etempvar _d tint) tlong))
                            (Sifthenelse (Ebinop Oeq (Etempvar _value tlong)
                                           (Etempvar _upper_boundary tlong)
                                           tint)
                              (Sifthenelse (Ebinop Ole (Etempvar _d tint)
                                             (Etempvar _last_digit_max tlong)
                                             tint)
                                (Ssequence
                                  (Sifthenelse (Ebinop Ogt
                                                 (Etempvar _sign tint)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    (Sset _value
                                      (Ebinop Oadd
                                        (Ebinop Omul (Etempvar _value tlong)
                                          (Econst_int (Int.repr 10) tint)
                                          tlong) (Etempvar _d tint) tlong))
                                    (Ssequence
                                      (Sset _sign
                                        (Econst_int (Int.repr 1) tint))
                                      (Sset _value
                                        (Ebinop Osub
                                          (Ebinop Omul
                                            (Eunop Oneg
                                              (Etempvar _value tlong) tlong)
                                            (Econst_int (Int.repr 10) tint)
                                            tlong) (Etempvar _d tint) tlong))))
                                  (Ssequence
                                    (Sset _str
                                      (Ebinop Oadd
                                        (Etempvar _str (tptr tschar))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr tschar)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'3
                                          (Ederef
                                            (Etempvar _end (tptr (tptr tschar)))
                                            (tptr tschar)))
                                        (Sifthenelse (Ebinop Olt
                                                       (Etempvar _str (tptr tschar))
                                                       (Etempvar _t'3 (tptr tschar))
                                                       tint)
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Etempvar _end (tptr (tptr tschar)))
                                                (tptr tschar))
                                              (Etempvar _str (tptr tschar)))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'4
                                                  (Ederef
                                                    (Etempvar _str (tptr tschar))
                                                    tschar))
                                                (Sifthenelse (Ebinop Oge
                                                               (Etempvar _t'4 tschar)
                                                               (Econst_int (Int.repr 48) tint)
                                                               tint)
                                                  (Ssequence
                                                    (Sset _t'5
                                                      (Ederef
                                                        (Etempvar _str (tptr tschar))
                                                        tschar))
                                                    (Sset _t'1
                                                      (Ecast
                                                        (Ebinop Ole
                                                          (Etempvar _t'5 tschar)
                                                          (Econst_int (Int.repr 57) tint)
                                                          tint) tbool)))
                                                  (Sset _t'1
                                                    (Econst_int (Int.repr 0) tint))))
                                              (Sifthenelse (Etempvar _t'1 tint)
                                                (Sreturn (Some (Econst_int (Int.repr (-3)) tint)))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Etempvar _intp (tptr tlong))
                                                      tlong)
                                                    (Ebinop Omul
                                                      (Etempvar _sign tint)
                                                      (Etempvar _value tlong)
                                                      tlong))
                                                  (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))
                                          Sskip))
                                      Sbreak)))
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
                                (Sreturn (Some (Econst_int (Int.repr (-3)) tint)))))))
                        (Ssequence
                          (Sassign
                            (Ederef (Etempvar _end (tptr (tptr tschar)))
                              (tptr tschar)) (Etempvar _str (tptr tschar)))
                          (Ssequence
                            (Sassign
                              (Ederef (Etempvar _intp (tptr tlong)) tlong)
                              (Ebinop Omul (Etempvar _sign tint)
                                (Etempvar _value tlong) tlong))
                            (Sreturn (Some (Econst_int (Int.repr 1) tint))))))))
                  (Sset _str
                    (Ebinop Oadd (Etempvar _str (tptr tschar))
                      (Econst_int (Int.repr 1) tint) (tptr tschar)))).


Notation set_vars_switch_body :=
  (Ssequence
    (Sset _t'2
      (Ederef
        (Etempvar _str (tptr tschar))
        tschar))
    (Sset _d
      (Ebinop Osub
        (Etempvar _t'2 tschar)
        (Econst_int (Int.repr 48) tint)
        tint))).

Notation if_then_else_bound :=
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
        (Sreturn (Some (Econst_int (Int.repr (-3)) tint)))))).

Notation switch_body :=
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
    (Sset _asn1_intmax_max
      (Ebinop Oshr
        (Eunop Onotint (Ecast (Econst_int (Int.repr 0) tint) tulong) tulong)
        (Econst_int (Int.repr 1) tint) tulong))
    (Ssequence
      (Sset _upper_boundary
        (Ebinop Odiv (Etempvar _asn1_intmax_max tlong)
          (Econst_int (Int.repr 10) tint) tlong))
      (Ssequence
        (Sset _last_digit_max
          (Ebinop Omod (Etempvar _asn1_intmax_max tlong)
            (Econst_int (Int.repr 10) tint) tlong))
        (Ssequence
          (Ssequence
            (Sset _t'12
              (Ederef (Etempvar _end (tptr (tptr tschar))) (tptr tschar)))
            (Sifthenelse (Ebinop Oge (Etempvar _str (tptr tschar))
                           (Etempvar _t'12 (tptr tschar)) tint)
              (Sreturn (Some (Econst_int (Int.repr (-2)) tint)))
              Sskip))
          (Ssequence
            (Ssequence
              (Sset _t'10 (Ederef (Etempvar _str (tptr tschar)) tschar))
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
                        (Sset _t'11
                          (Ederef (Etempvar _end (tptr (tptr tschar)))
                            (tptr tschar)))
                        (Sifthenelse (Ebinop Oge
                                       (Etempvar _str (tptr tschar))
                                       (Etempvar _t'11 (tptr tschar)) tint)
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
               s2)
            s3))))))).
