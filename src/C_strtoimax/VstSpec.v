(* VST specification of asn_strtoimax_lim *)
Require Import Clight.INTEGER.


Require Import Spec Automaton AbstractSpec AutomatonExecSpecEquiv.
Require Import Core.Core Core.Tactics Core.PtrLemmas.
Require Import StructTact.StructTactics.
Require Import VST.floyd.proofauto.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Section VstStrtoimaxSpec.

  Parameter m : mem.

  (* Placeholder for abstract spec for OK an EXTRA_DATA cases only *)
  Definition Z_of_string_OK (s : list byte) : Z :=
    let fix Z_of_string_loop s v  :=
        match s with
        | [] => v
        | c :: tl =>
        if is_digit c
        then Z_of_string_loop tl v 
        else v              
      end
  in match s with
     |  nil => 0 (* non-nil guaranteed *)
     |  sign::tl =>
        let res := (Z_of_string_loop tl 0%Z) in
            if Byte.eq sign plus_char
            then res
            else if Byte.eq sign minus_char 
                 then Z.opp res
                 else (Z_of_string_loop s 0%Z)
     end.

  Locate tschar.
   
  
Definition asn_strtoimax_lim_vst_spec : ident * funspec :=
  DECLARE _asn_strtoimax_lim
    WITH str_b : block, str_ofs : ptrofs,
         end_b : block, end_ofs : ptrofs,
         end'_b : block, end'_ofs : ptrofs,
         intp_b : block, intp_ofs : ptrofs,
         sh : share, sh' : share,
         contents : list byte,
         chars : list char,
         blen : nat,
         res_state : strtoimax_state
    PRE [_str OF (tptr tschar), _end OF (tptr (tptr tschar)), _intp OF (tptr tlong)]
      PROP (readable_share sh; writable_share sh';
            str_b = end'_b;
            map char_of_byte contents = chars;
            Zlength contents = Z.max 0 (Ptrofs.signed (Ptrofs.sub end_ofs str_ofs));
            fsa_run (strtoimax_fsa blen) chars res_state)
      LOCAL (temp _str (Vptr str_b str_ofs);
             temp _end (Vptr end_b end_ofs); 
             temp _intp (Vptr intp_b intp_ofs) )
      SEP ( valid_pointer (Vptr end'_b end'_ofs) && 
             data_at sh (tarray tschar (Zlength contents))
                   (map Vbyte contents) (Vptr str_b str_ofs);
             data_at sh' (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs) )
    POST [tint]
      PROP()
      LOCAL (temp ret_temp (Vint (asn_strtox_result_e_to_int (result_of_state res_state))))
      SEP ( test_order_ptrs (Vptr end'_b str_ofs) (Vptr end'_b end'_ofs);
                                                                        data_at sh (tarray tschar (Zlength contents))
                   (map Vbyte contents) (Vptr str_b str_ofs);
           data_at sh' (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs)).
End VstStrtoimaxSpec.

Print HintDb saturate_local.
Print HintDb valid_pointer.

Lemma sizeof_tarray_tschar : forall (n : Z), 
    0 <= n -> sizeof (tarray tschar n) = n.
Proof.
  intros.
  unfold tarray.
  unfold tschar.
  induction n.
  simpl; reflexivity.
  simpl; reflexivity.
  contradiction.
Qed.

Definition Gprog := ltac:(with_library prog [asn_strtoimax_lim_vst_spec]).

Lemma body_asn_strtoimax_lim : semax_body Vprog Gprog f_asn_strtoimax_lim  asn_strtoimax_lim_vst_spec.
Proof.
  start_function.  
  forward.
  forward.
  forward.
  entailer!;
       inversion H;
       inversion H5.
  forward.
  entailer!;
       inversion H;
       inversion H5.
  forward.

  forward_if.
  
  unfold test_order_ptrs.
  unfold sameblock.
  destruct peq; [simpl|contradiction].
  entailer!.

  Search (_ |-- ?P && ?Q ).
  eapply andp_right.
  eapply H3.
  
  Search (_ && _ |-- _).
  eapply andp_left1.
  rewrite <-sepcon_corable_corable.
  (* first part of subgoal *)
  pose proof readable_nonidentity SH.
  assert (0 <= Zlength contents). { rewrite H1; apply Z.le_max_l. }
  pose proof sizeof_tarray_tschar (Zlength contents) H0.
  apply Z_le_lt_eq_dec in H0.
  destruct H0.
  assert (sizeof (tarray tschar (Zlength contents)) > 0). { rewrite H9; lia. }
  pose proof data_at_valid_ptr sh (tarray tschar (Zlength contents)) 
       (map Vbyte contents) (Vptr end'_b str_ofs) H H0.
  admit.
  admit.
  unfold corable.
  Locate weak_valid_pointer.
  (* what is corable??? WHERE ARE DOCS *)
  (* The problem is that Zlength contents >= 0, but if we can prove this, then we can move forward *)
  (* if we can prove statement above, and the same statement for the second case *)
  (* then we can use [cancel1_last] tactic to prove whole subgoal *)

Admitted.
  

  
             
             
