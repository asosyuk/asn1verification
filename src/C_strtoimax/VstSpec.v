(* VST specification of asn_strtoimax_lim *)
Require Import Clight.INTEGER.

Require Import Spec Automaton AbstractSpec AutomatonExecSpecEquiv.
Require Import Core.Core Core.Tactics Core.PtrLemmas.

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

Definition asn_strtoimax_lim_vst_spec : ident * funspec :=
  DECLARE _asn_strtoimax_lim
    WITH str : addr, fin : addr, fin' : addr, intp : addr,
         sh : share, sh' : share,
         str_contents : list byte,
         chars : list char,
         dist : nat,
         blen : nat,
         res_state : strtoimax_state
    PRE [_str OF (tptr tschar), _end OF (tptr (tptr tschar)), _intp OF (tptr tlong)]
      PROP (readable_share sh; writable_share sh';
            fsa_run (strtoimax_fsa blen) chars res_state;
            map char_of_byte str_contents = chars;
            distance m str fin = Some dist)
      LOCAL (temp _str (vptr str);
             temp _end (vptr fin); 
             temp _intp (vptr intp))
      SEP (data_at sh (tarray tschar (Z.of_nat dist)) (map Vbyte str_contents) (vptr str);
           data_at sh (tptr tschar) (vptr fin') (vptr fin))
    POST [tint]
      PROP()
      LOCAL (temp ret_temp (Vint (asn_strtox_result_e_to_int (result_of_state res_state))))
      SEP (data_at sh (tarray tschar (Z.of_nat dist)) (map Vbyte str_contents) (vptr str);
          imp (!! (result_of_state res_state = ASN_STRTOX_OK)) 
              (data_at sh' (tlong)
                       (Vlong (Int64.repr (Z_of_string_OK str_contents))) 
                       (vptr intp));
           imp (!! (result_of_state res_state = ASN_STRTOX_EXTRA_DATA)) 
              (data_at sh' (tlong)
                       (Vlong (Int64.repr (Z_of_string_OK str_contents))) 
                       (vptr intp))).
End VstStrtoimaxSpec.

Definition Gprog := ltac:(with_library prog [asn_strtoimax_lim_vst_spec]).

Lemma body_sumarray: semax_body Vprog Gprog f_asn_strtoimax_lim  asn_strtoimax_lim_vst_spec.
Proof.
  start_function.  
  repeat forward.
  1-2: entailer!;
       inversion H0;
       inversion H11.
  
  entailer!.
  all: autorewrite with sublist in *|-.
  admit. (* is_pointer_or_null (vptr fin') *)

  forward_if.
  hint.
  autorewrite with sublist in *|-.
  hint.
  entailer!.
  (* separation logic statement :
     data_at sh (tarray tschar (Z.of_nat dist)) (map Vbyte str_contents) (vptr str) *
  data_at sh (tptr tschar) (vptr fin') (vptr fin) |-- denote_tc_test_order (vptr str) (vptr fin') 
  *) admit.

  forward.
  autorewrite with sublist in *|-. (* why entailer doesn't work without this?? *)
  entailer!.
  (* Vint (Int.repr (-2)) = Vint (asn_strtox_result_e_to_int (result_of_state res_state)) *)
  admit.
  hint.
  autorewrite with sublist in *|-.
  entailer!.
  (* reached identical state *)
  admit.
  forward.
  Admitted.
  

  
             
             
