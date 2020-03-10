(* VST specification of as *)
Require Import Clight.BOOLEAN.
Require Import Core.Core Lib.
Require Import VST.floyd.proofauto Psatz.
Require Import BooleanExecSpec.
Require Import ErrorWithWriter.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section Boolean_der_encode_primitive.

Definition cb_type := (Tfunction 
                          (Tcons (tptr tvoid) 
                                 (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint 
                          cc_default).

Definition bool_der_encode_spec : ident * funspec :=
  DECLARE _BOOLEAN_encode_der
    WITH (* pointer to the decoded structure *)
         sptr_b : block, sptr_ofs : ptrofs, sptr_val : Z, sh_sptr : share,
         (* pointer to the DEF table for the type decoded *)
         td_b : block, td_ofs : ptrofs, sh_td : share,
         td : TYPE_descriptor,
         tag_mode : Z, tag_class : Z,
         (* callback pointer *)
         cb_b : block, cb_ofs : ptrofs, cb_val : val, sh_cb : share,
         (* callback argument pointer *)
         app_key_b : block, app_key_ofs : ptrofs,
         app_key_val : val, sh_app_key : share
    PRE  [         
      (* added by clightgen - since returning structs is not supported *) 
          __res OF (tptr (Tstruct _asn_enc_rval_s noattr)),
          _td OF (tptr (Tstruct _asn_TYPE_descriptor_s noattr)),
          _sptr OF (tptr tvoid), _tag_mode OF tint,
          _tag OF tuint,
          _cb OF (tptr cb_type),
          _app_key OF (tptr tvoid)
           ]
    PROP ( readable_share sh_td;
           writable_share sh_sptr; 
           readable_share sh_cb;
           readable_share sh_app_key )
    LOCAL ( temp _td (Vptr td_b td_ofs);
            temp _sptr (Vptr sptr_b sptr_ofs);
            temp _tag_mode (Vint (Int.repr tag_mode));
            temp _tag (Vint (Int.repr tag_class));
            temp _cb (Vptr cb_b cb_ofs);
            temp _app_key (Vptr app_key_b app_key_ofs))        
    SEP ((* td points to td with readable permission *)
           data_at sh_td (Tstruct _asn_TYPE_descriptor_s noattr) 
                   (TYPE_descriptor_rep td) (Vptr td_b td_ofs) ; 
           data_at sh_sptr (tvoid) (tt) (Vptr sptr_b sptr_ofs) ;
           data_at sh_app_key (tvoid) (tt) 
                   (Vptr app_key_b app_key_ofs) ;
           data_at sh_cb (cb_type) (tt) (Vptr cb_b cb_ofs))
    POST [tvoid]
      PROP()
      LOCAL ()
      SEP( (* Unchanged by the execution : *)
           data_at sh_td (Tstruct _asn_TYPE_descriptor_s noattr) 
                   (TYPE_descriptor_rep td) (Vptr td_b td_ofs) ; 
           data_at sh_sptr (tvoid) (tt) (Vptr sptr_b sptr_ofs) ;
           data_at sh_app_key (tvoid) (tt) 
                   (Vptr app_key_b app_key_ofs) ;
           data_at sh_cb (cb_type) (tt) (Vptr cb_b cb_ofs)).

Definition Gprog1 := ltac:(with_library prog [bool_der_encode_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog1 f_BOOLEAN_encode_der
                                     bool_der_encode_spec.
Admitted.

End Boolean_der_encode_primitive.

Section Boolean_der_decode_primitive.

Definition bool_ber_decode_spec : ident * funspec :=
  DECLARE _BOOLEAN_decode_ber
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
           (* Changed after execution *)         
           data_at sh_sptr (Tstruct _asn_TYPE_descriptor_s noattr) 
                   (bool_prim_decoder td buf) (Vptr sptr_b sptr_ofs); 
           data_at sh_res (Tstruct _asn_dec_rval_s noattr)
                   (dec_rval_rep (bool_prim_decoder td buf)) (Vptr res_b res_ofs)).

Definition Gprog2 := ltac:(with_library prog [bool_ber_decode_spec]).

Theorem bool_ber_decode : semax_body Vprog Gprog2 f_BOOLEAN_decode_ber
                                     bool_ber_decode_spec.
Admitted.

End Boolean_der_decode_primitive.
