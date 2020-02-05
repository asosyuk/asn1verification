(* VST specification of as *)
Require Import Clight.asn_codecs_prim.
Require Import Core.Core.
Require Import VST.floyd.proofauto.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Inductive dec_rval_code := OK | FAIL | MORE.

Record dec_rval := rval { code : dec_rval_code ;
                          consumed : Z }.

Inductive TYPE_descriptor :=
  DEF { tags : list Z ;
        elements : list TYPE_descriptor 
      }.

Section PrimitiveParser.

Record PRIMITIVE_TYPE := prim_type { buf : list byte;
                                     size : Z }.

Definition ZeroChar := Byte.repr 48.
Definition prim_decode_failed := rval FAIL 0.
Definition prim_decode_starved := rval MORE 0. 

Definition primitive_decoder (ls : list byte) : list byte :=
  ls ++ [ZeroChar].
  
(* memory representation of TYPE_descriptor tree *)
Parameter TYPE_descriptor_rep : TYPE_descriptor
                                -> reptype (Tstruct _asn_TYPE_descriptor_s noattr). 
Parameter PRIMITIVE_TYPE_rep : PRIMITIVE_TYPE 
                               -> reptype  (Tstruct _ASN__PRIMITIVE_TYPE_s noattr).
Parameter dec_rval_rep : dec_rval -> reptype (Tstruct _asn_dec_rval_s noattr).

Definition _ber_decode_primitive_spec : ident * funspec :=
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
                   (Vptr buf_b buf_ofs);
           (* OK case *)
           data_at sh_sptr (Tstruct _ASN__PRIMITIVE_TYPE_s noattr)
                   (PRIMITIVE_TYPE_rep (prim_type (primitive_decoder buf)
                                                  (Zlength buf + 1)))
                                       (Vptr sptr_b sptr_ofs);
           data_at sh_res (Tstruct _asn_dec_rval_s noattr)
                   (dec_rval_rep (rval OK (Zlength buf))) (Vptr res_b res_ofs)).

End PrimitiveParser.
