(* VST specification of asn_strtoimax_lim *)
Require Import VST.floyd.proofauto.
Require Import Clight.INTEGER.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Require Import Core AbstractSpec Spec.
Require Import Core.Core Core.Tactics Core.PtrLemmas.

Section VstStrtoimaxSpec.

Parameter m : mem.

Definition asn_strtoimax_lim_vst_spec : ident * funspec :=
  DECLARE _asn_strtoimax_lim
    WITH str : addr, fin : addr, intp : addr,
         sh : share, sh' : share,
         str_contents : list int,
         dist : nat
    PRE [_str OF (tptr tschar), _end OF (tptr (tptr tschar)), _intp OF (tptr tlong)]
      PROP (readable_share sh; writable_share sh';
            distance m str fin = Some dist)
      LOCAL (temp _str (vptr str);
           temp _end (vptr fin); 
           temp _intp (vptr intp))
      SEP (data_at sh (tarray tschar (Z.of_nat dist)) (map Vint str_contents) (vptr str))
    POST [tint]
      PROP()
      LOCAL (temp ret_temp Vzero)
      SEP (data_at sh (tarray tschar (Z.of_nat dist)) (map Vint str_contents) (vptr str)).
      
             
             
