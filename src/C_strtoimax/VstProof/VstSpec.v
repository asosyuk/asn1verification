(* VST specification of asn_strtoimax_lim *)
Require Import Clight.INTEGER.
Require Import Core.Core.
Require Import VST.floyd.proofauto.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Require Import AbstractSpec.

Definition asn_strtoimax_lim_vst_spec : ident * funspec :=
  DECLARE _asn_strtoimax_lim
    (* WITH: binds variables in Pre- and Postconditions *)
    WITH (* start of the string str *)
         str_b : block, str_ofs : ptrofs,
         (* end of the string *end *)
         end'_b : block, end'_ofs : ptrofs,
         (* stores address of the end of the string end *)
         end_b : block, end_ofs : ptrofs,
         (* stores result intp *)
         intp_b : block, intp_ofs : ptrofs,
         (* permission shares, cf. Verifiable C book (p.73) *)
         sh_str : share, sh_end : share, sh_intp : share,
         (* input string *)
         ls : list byte,
         (* ls of intp *)
         v : val
    (* Preconditions *)
    (* Type declaration for parameters of the function *)
    PRE [ _str OF (tptr tschar),
          _end OF (tptr (tptr tschar)),
          _intp OF (tptr tlong) ]
    (* PROP: Propositions (of type Prop) that should hold
       before executing the function. ; is conjuction *)
    
    PROP ( (* Permissions for memory access *)
          readable_share sh_str;  (* str points to readable memory *)
          writable_share sh_end;  (* end points to writable memory *)
          writable_share sh_intp; (* intp points to writable memory *)

          (* str and end' should point to the same object, 
           otherwise incomparable by C standard *)
          str_b = end'_b;

          (* length of ls = distance between str and end' *)
          Zlength ls =
          Z.max 0 (Ptrofs.unsigned end'_ofs - Ptrofs.unsigned str_ofs);

         (* No pointer overflow occurs *)
         Ptrofs.unsigned str_ofs + Zlength ls < Ptrofs.modulus        
                
      )
      (* LOCAL: connects C light prameter identifiers and declared variables *)
      LOCAL (temp _str (Vptr str_b str_ofs);
             temp _end (Vptr end_b end_ofs); 
             temp _intp (Vptr intp_b intp_ofs))
      (* SEP: Propositions about memory (of type mem -> Prop (mpred)) that 
         should hold before executing the function. 
         ; (and * ) is separating conjunction, && is ordinary conjuction *)
                     
      SEP ((* str and end' are comparable, i.e. point within the same object *)
        valid_pointer (Vptr end'_b (Ptrofs.add str_ofs (Ptrofs.repr
                                                          (Zlength ls)))) ;
           valid_pointer (Vptr end'_b end'_ofs) ;
           valid_pointer (Vptr str_b str_ofs) ;
           (* str points to ls with readable permission *)
           data_at sh_str (tarray tschar (Zlength ls)) 
                   (map Vbyte ls) (Vptr str_b str_ofs) ; 
           (* end points to end' with writable permission *)
           data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs) 
                   (Vptr end_b end_ofs);
           (* intp points to some value v  *)
           data_at sh_intp (tlong) v (Vptr intp_b intp_ofs))     
    (* Postconditions *)
    (* Type declaration for return value of the function *)
    POST [tint]
      (* No new propositions hold after executing the function *)
      PROP()
      (* Return value of the function corresponds to the result 
         of abstract spec on ls *)
      LOCAL (temp ret_temp (Vint (asn_strtox_result_e_to_int 
                                   (res 
                                      (Z_of_string ls)))))
      (* Propositions about memory that hold after executing the function *)
      SEP( (* this part didn't change after execution *) 
           
           valid_pointer (Vptr end'_b end'_ofs) ;
           valid_pointer (Vptr str_b str_ofs) ;
           data_at sh_str (tarray tschar (Zlength ls)) 
                   (map Vbyte ls) (Vptr str_b str_ofs) ;
           let r := res (Z_of_string ls) in
            (* in 3 cases intp stays unchanged,
              otherwise store the end value of Z_of_string *)
            match r with 
              | ERROR_RANGE 
              | ERROR_INVAL 
              | EXPECT_MORE => 
                data_at sh_intp (tlong) v (Vptr intp_b intp_ofs)
              | _ => data_at sh_intp (tlong) 
                         (Vlong (Int64.repr (value (Z_of_string ls))))
                         (Vptr intp_b intp_ofs) 
            end ;
           (* if str >= end, end doesn't change, 
              otherwise store the address of the last char read 
              (before going out of range, reading extra data 
              or successfully terminating) *)
            let i := index (Z_of_string ls) in
            if (Ptrofs.unsigned str_ofs <? Ptrofs.unsigned end'_ofs)
            then data_at sh_end (tptr tschar) 
                         (Vptr str_b (Ptrofs.add str_ofs (Ptrofs.repr i))) 
                         (Vptr end_b end_ofs)
            else data_at sh_end (tptr tschar) (Vptr end'_b end'_ofs) 
                         (Vptr end_b end_ofs)).


Definition Gprog := ltac:(with_library prog [asn_strtoimax_lim_vst_spec]).

