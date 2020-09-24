(* VST specification of as *)
Require Import Clight.asn_codecs_prim.
Require Import Core.Core Core.StructNormalizer Lib.Lib Lib.VstLib.
Require Import VST.floyd.proofauto.
Require Import IntExecSpec.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section PrimitiveParser.

(* Decoding fails : 
   1) when calloc fails to allocate memory for the output structure sptr (FAIL) SEP spec
   2) if ber_check_tags return FAIL (when?) or MORE (?) - executable spec
   3) if not enough data according to length read (MORE) - executable spec
   4) expected length doesn't fit into size (FAIL) ?

        st->size = (int)length;
	/* The following better be optimized away. */
	if(sizeof(st->size) != sizeof(length)
			&& (ber_tlv_len_t)st->size != length) {
		st->size = 0;
		ASN__DECODE_FAILED;
	}

   5) malloc buf allocation fails (FAIL) SEP spec
 *)


Definition ber_decode_primitive_spec : ident * funspec :=
  DECLARE _ber_decode_primitive
    WITH (* pointer to the decoded structure *)
         sptr_b : block, sptr_ofs : ptrofs,
         (* double pointer to the DEF table for the type decoded *)
         td_b : block, td_ofs : ptrofs,
         td'_b : block, td'_ofs : ptrofs,
         (* pointer to  the input buffer *)
         buf_b : block, buf_ofs : ptrofs,
         (* pointer to the return struct dec_rval *)                         
         res_b : block, res_ofs : ptrofs,
         (* codec context: stores max_stack_size for the decoder routines *)
         ctx : val,
         (* memory permissions for each pointer *)
         sh_sptr : share, sh_td : share, sh_buf : share, sh_td' : share,
         sh_res : share,                                                         
         (* input *)
         buf : list byte,
         td : TYPE_descriptor,
         size : int,
         tag_mode : int  
    PRE  [         
 (* added by clightgen - since returning structs is not supported *) 
          __res OF (tptr (Tstruct _asn_dec_rval_s noattr)),
          _opt_codec_ctx OF (tptr (Tstruct _asn_codec_ctx_s noattr)),
          _td OF (tptr (Tstruct _asn_TYPE_descriptor_s noattr)),
          _sptr OF (tptr (tptr tvoid)),
          _buf_ptr OF (tptr tvoid),
          _size OF tuint,
          _tag_mode OF tint ]
    PROP ( writable_share sh_sptr; 
           writable_share sh_res; 
           readable_share sh_td;
           readable_share sh_buf )
    LOCAL ( temp _opt_codec_ctx ctx;
            temp _td (Vptr td_b td_ofs);
            temp _sptr (Vptr sptr_b sptr_ofs);
            temp _buf_ptr (Vptr buf_b buf_ofs);
            temp _size (Vint size);
            temp _tag_mode (Vint tag_mode))        
    SEP ((* td points to td with readable permission *)
           data_at sh_td (tptr (Tstruct _asn_TYPE_descriptor_s noattr)) 
                   (Vptr td'_b td'_ofs) (Vptr td_b td_ofs);
           data_at sh_td' (Tstruct _asn_TYPE_descriptor_s noattr) 
                   (TYPE_descriptor_rep td) (Vptr td'_b td'_ofs) ; 
           (* buf points to data ls *)
           data_at sh_buf (tarray tschar (Zlength buf)) (map Vbyte buf) 
                   (Vptr buf_b buf_ofs))
    POST [tvoid]
      PROP()
      LOCAL ()
      SEP( (* Unchanged by the execution : *)
           data_at sh_td (tptr (Tstruct _asn_TYPE_descriptor_s noattr)) 
                   (Vptr td'_b td'_ofs) (Vptr td_b td_ofs);
           data_at sh_td' (Tstruct _asn_TYPE_descriptor_s noattr) 
                   (TYPE_descriptor_rep td) (Vptr td'_b td'_ofs) ; 
           data_at sh_buf (tarray tschar (Zlength buf)) (map Vbyte buf) 
                   (Vptr buf_b buf_ofs)
           (* Changed after execution *)         
           (* data_at sh_sptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)
                   (PRIMITIVE_TYPE_rep (int_decoder td buf))
                                       (Vptr sptr_b sptr_ofs); 
           data_at sh_res (Tstruct _asn_dec_rval_s noattr)
                   (dec_rval_rep (int_decoder td buf)) (Vptr res_b res_ofs) *)).


Definition Gprog := ltac:(with_library prog [ber_decode_primitive_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog
           (normalize_function f_ber_decode_primitive composites)
           ber_decode_primitive_spec.
  Proof.
  start_function.
  unfold MORE_COMMANDS.
  unfold abbreviate.

Admitted.

End PrimitiveParser.
