Require Import Core.Core Core.StructNormalizer
        VstLib ErrorWithWriter BCT.Exec.
Require Import VST.floyd.proofauto Lib.Forward Core.VstTactics.
Require Import Clight.ber_decoder.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Definition ASN__STACK_OVERFLOW_CHECK_spec : ident * funspec :=
  DECLARE _ASN__STACK_OVERFLOW_CHECK
    WITH ctx_p : val, max_stack_size : Z
    PRE [tptr (Tstruct _asn_codec_ctx_s noattr)]
      PROP ()
      PARAMS (ctx_p)
      GLOBALS ()
      SEP (data_at Tsh (Tstruct _asn_codec_ctx_s noattr)
                   (Vint (Int.repr max_stack_size)) ctx_p)
    POST [tint]
      PROP ()
      LOCAL (temp ret_temp 
               (Vint
                  (Int.repr 
                     (if eq_dec ctx_p nullval 
                      then 0
                      else ASN__STACK_OVERFLOW_CHECK 0 max_stack_size ))))
      SEP (data_at Tsh (Tstruct _asn_codec_ctx_s noattr) 
                   (Vint (Int.repr max_stack_size)) ctx_p).

Definition Gprog := ltac:(with_library prog [ASN__STACK_OVERFLOW_CHECK_spec]).

Theorem bool_der_encode :
  semax_body Vprog Gprog 
             (normalize_function f_ASN__STACK_OVERFLOW_CHECK composites) 
             ASN__STACK_OVERFLOW_CHECK_spec.
Proof.
  (*
  start_function.
  repeat forward.
  forward_if (temp _t'1 (Vint (Int.repr (if eq_dec ctx_p nullval  
                                         then 0 
                                         else (if eq_dec max_stack_size 0 
                                               then 0 
                                               else 1))))). 
  - repeat forward.
    entailer!.
    unfold isptr in H.
    destruct ctx_p; try contradiction.
    unfold nullval.
    break_if.
    generalize e. break_if; try congruence.
    destruct (Int.eq (Int.repr max_stack_size) Int.zero) eqn : N.
    eapply int_eq_e in N.
    break_if; auto; try rep_omega.  
    admit. 
    eapply int_eq_false_e in N.
    break_if; auto.
    erewrite e in *.
    contradiction.
  - forward.
    entailer!.
  - forward_if True.
    + forward.
      forward.
      entailer!.
      unfold denote_tc_samebase.
      admit.
      forward_if (temp _usedstack 
                       (force_val (sem_unary_operation Oneg tint 
                       (force_val (sem_sub_pp tschar ctx_p v_ctx))))).
      * forward.
        entailer!.
        admit.
        entailer!.
      * forward.
        entailer!.
        admit.
      * forward.
        forward.
        forward_if.
        entailer!. admit.
        forward_empty_loop. *)
Admitted.

    

  


