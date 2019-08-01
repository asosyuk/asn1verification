eapply exec_loop.
      eassumption.
      eapply Heqo0.
      eassumption.
      exists ((_value <~ Vlong (cast_int_long Signed (Int.repr 0)))
           ((_t'5 <~ Vptr fin_b fin_ofs)
              ((_str <~
                     Vptr str_b
                     (str_ofs + Ptrofs.repr (sizeof ge tschar) * ptrofs_of_int Signed (Int.repr 1))%ptrofs)
                 ((_sign <~ Vint ( (Int.repr 1)))
                    ((_last_digit_max <~
                                      Vlong
                                      (Int64.modu
                                         (Int64.not (cast_int_long Signed (Int.repr 0)) >>
                                                  Int64.repr (Int.unsigned (Int.repr 1)))
                                         (cast_int_long Signed (Int.repr 10)) +
                                       cast_int_long Signed (Int.repr 1)))
                       ((_t'4 <~ Vint minus_char)
                          ((_t'6 <~ Vptr fin_b fin_ofs)
                             ((_last_digit_max <~
                                               Vlong
                                               (Int64.modu
                                                  (Int64.not (cast_int_long Signed (Int.repr 0)) >>
                                                           Int64.repr (Int.unsigned (Int.repr 1)))
                                                  (cast_int_long Signed (Int.repr 10))))
                                ((_upper_boundary <~
                                                  Vlong
                                                  (Int64.divu
                                                     (Int64.not (cast_int_long Signed (Int.repr 0)) >>
                                                              Int64.repr (Int.unsigned (Int.repr 1)))
                                                     (cast_int_long Signed (Int.repr 10))))
                                   ((_sign <~ Vint (Int.repr 1)) le)))))))))).
      eapply asn_strtoimax_lim_loop_ASN_STRTOX_ERROR_RANGE_correct.
      unfold vptr.
      all: repeat env_assumption.
      all: repeat env_assumption.
      repeat econstructor.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      replace (Ptrofs.repr (sizeof ge tschar) * ptrofs_of_int Signed (Int.repr 1))%ptrofs with 1%ptrofs.
      replace (cast_int_long Signed (Int.repr 0)) with  0%int64.
      instantiate (4 := Unsigned).
      simpl.
      replace (distance (str_b, (str_ofs + 1)%ptrofs) (b, i)) with  (distance (str_b, str_ofs) (b, i) - 1)%nat.
      eassumption.
      unfold distance.
      simpl.
      admit.
      simpl.
      auto with ints.
      simpl.
      auto with ptrofs.
