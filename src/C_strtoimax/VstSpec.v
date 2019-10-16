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
            fsa_run (strtoimax_fsa blen) chars res_state)
      LOCAL (temp _str (Vptr str_b str_ofs);
             temp _end (Vptr end_b end_ofs); 
             temp _intp (Vptr intp_b intp_ofs))
      SEP (data_at sh (tarray tschar (Zlength contents))
                   (map Vbyte contents) (Vptr str_b str_ofs);
           data_at sh' (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs))
    POST [tint]
      PROP()
      LOCAL (temp ret_temp (Vint (asn_strtox_result_e_to_int (result_of_state res_state))))
      SEP (data_at sh (tarray tschar (Zlength contents))
                   (map Vbyte contents) (Vptr str_b str_ofs);
           data_at sh' (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs)
          (* ; imp (!! (result_of_state res_state = ASN_STRTOX_OK)) 
              (data_at sh' (tlong)
                       (Vlong (Int64.repr (Z_of_string_OK contents))) 
                       (Vptr intp_b intp_ofs));
           imp (!! (result_of_state res_state = ASN_STRTOX_EXTRA_DATA)) 
              (data_at sh' (tlong)
                       (Vlong (Int64.repr (Z_of_string_OK contents))) 
                       (Vptr intp_b intp_ofs)) *)).
End VstStrtoimaxSpec.

Definition Gprog := ltac:(with_library prog [asn_strtoimax_lim_vst_spec]).

Lemma body_asn_strtoimax_lim : semax_body Vprog Gprog f_asn_strtoimax_lim  asn_strtoimax_lim_vst_spec.
Proof.
  start_function.  
  forward.
  forward.
  forward.
  normalize.
  entailer!;
       inversion H;
       inversion H7.
  forward.
  normalize.
  entailer!;
       inversion H;
       inversion H7.
  forward.
  normalize.
  forward_if.
  Admitted.
  

  
             
             
