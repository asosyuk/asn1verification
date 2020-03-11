(* VST specification of as *)
Require Import Clight.BOOLEAN.
Require Import Core.Core Lib.
Require Import VST.floyd.proofauto Psatz.
Require Import BooleanExecSpec.
Require Import ErrorWithWriter.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.


Section Boolean_der_decode_primitive.

Definition bool_ber_decode_spec : ident * funspec :=
  DECLARE _BOOLEAN_decode_ber
    WITH (* Context pointer *)
         sh_ctx : share, ctx_b : block, ctx_ofs : ptrofs, ctx : val,
         (* Type Descriptor pointer *)
         sh_td : share, td_b : block, td_ofs : ptrofs, td : TYPE_descriptor,
         (* Value double pointer *)
         sh_val' : share, val_b' : block, val_ofs' : ptrofs,
         sh_val : share, val_b : block, val_ofs : ptrofs,
         (* Buffer pointer *)
         sh_buf : share, buf_b : block, buf_ofs : ptrofs, buf : list byte,
         size : Z, tag_mode : Z
    PRE  [         
         (* added by clightgen - since returning structs is not supported *) 
         __res OF (tptr (Tstruct _asn_dec_rval_s noattr)),
         _opt_codec_ctx OF (tptr (Tstruct _asn_codec_ctx_s noattr)),
         _td OF (tptr (Tstruct _asn_TYPE_descriptor_s noattr)),
         _bool_value OF (tptr (tptr tvoid)),
         _buf_ptr OF (tptr tvoid),
         _size OF tuint,
         _tag_mode OF tint]
    PROP ( readable_share sh_ctx; 
           readable_share sh_td; 
           readable_share sh_val';
           readable_share sh_val;
           readable_share sh_buf )
    LOCAL ( temp _opt_codec_ctx ctx;
            temp _td (Vptr td_b td_ofs);
            temp _bool_value (Vptr val_b' val_ofs');
            temp _buf_ptr (Vptr buf_b buf_ofs);
            temp _size (Vint (Int.repr size));
            temp _tag_mode (Vint (Int.repr tag_mode)))
    SEP (
           data_at sh_ctx (tptr (Tstruct _asn_codec_ctx_s noattr))
                   (Vptr ctx_b ctx_ofs) (ctx);
           data_at sh_td (Tstruct _asn_TYPE_descriptor_s noattr)
                   (TYPE_descriptor_rep td) (Vptr td_b td_ofs);
           (* val double pointer *)
           data_at sh_val' (tptr (tptr tuchar)) (Vptr val_b val_ofs)
                   (Vptr val_b' val_ofs');
           data_at sh_val (tptr tuchar) (default_val (tptr tuchar)) (Vptr val_b val_ofs);
           (* buf points to data ls *)
           data_at sh_buf (tarray tschar (Zlength buf)) (map Vbyte buf) 
                   (Vptr buf_b buf_ofs))
    POST [tvoid]
      PROP()
      LOCAL ()
      SEP( 
           (* Unchanged by the execution : *)
           data_at sh_ctx (tptr (Tstruct _asn_codec_ctx_s noattr))
                   (Vptr ctx_b ctx_ofs) (ctx);
           data_at sh_td (Tstruct _asn_TYPE_descriptor_s noattr) 
                   (TYPE_descriptor_rep td) (Vptr td_b td_ofs);
           data_at sh_buf (tarray tschar (Zlength buf)) (map Vbyte buf) 
                   (Vptr buf_b buf_ofs);
           data_at sh_val' (tptr (tptr tuchar)) (Vptr val_b val_ofs) 
                   (Vptr val_b' val_ofs');
           (* Changed after execution *)
           let res := bool_decoder td buf in
           match res with
           | Some r => data_at sh_val (tptr tuchar) (Vbyte r) (Vptr val_b val_ofs)
           | None => data_at sh_val (tptr tuchar) (default_val (tptr tuchar)) (Vptr val_b val_ofs)
           end).

Definition Gprog2 := ltac:(with_library prog [bool_ber_decode_spec]).

Theorem bool_ber_decode : semax_body Vprog Gprog2 f_BOOLEAN_decode_ber
                                     bool_ber_decode_spec.
Admitted.

End Boolean_der_decode_primitive.
