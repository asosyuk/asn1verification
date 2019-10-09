(* VST specification of asn_strtoimax_lim *)
Require Import VST.floyd.proofauto.
Require Import Clight.INTEGER.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Require Import Automaton AbstractSpec AutomatonExecSpecEquiv Spec.
Require Import Core.Core Core.Tactics Core.PtrLemmas.

Section VstStrtoimaxSpec.

Parameter m : mem.
(* Placeholder for abstract spec for OK case only *)
Definition Z_of_string_OK (s : list int) : Z :=
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
            if Int.eq sign plus_char
            then res
            else if Int.eq sign minus_char 
                 then Z.opp res
                 else (Z_of_string_loop s 0%Z)
     end.

Definition int_of_byte i := Int.repr (Byte.signed i).

Definition asn_strtoimax_lim_vst_spec : ident * funspec :=
  DECLARE _asn_strtoimax_lim
    WITH str : addr, fin : addr, fin' : addr, intp : addr,
         sh : share, sh' : share,
         str_contents : list byte,
         chars : list char,
         dist : nat,
         blen : nat,
         value : Z,
         P : Prop,
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
                       (Vlong (Int64.repr (Z_of_string_OK (map int_of_byte str_contents)))) 
                       (vptr intp))).
      
             
             
