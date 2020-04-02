(* VST specification of as *)
Require Import Core.Core VstLib Lib BooleanExecSpec ErrorWithWriter.
Require Import VST.floyd.proofauto Psatz.
Require Import Clight.BOOLEAN.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section Boolean_ber_decode.

Notation _asn_dec_rval_s_struct := (Tstruct _asn_dec_rval_s noattr).

Definition asn_dec_rval_rep sh v code cons :=  
 (field_at sh _asn_dec_rval_s_struct 
           [StructField _code]
           (Vint (Int.repr code)) v *
  field_at sh _asn_dec_rval_s_struct 
           [StructField _consumed] 
           (Vint (Int.repr cons)) v)%logic. 

Definition bool_ber_decode_spec : ident * funspec :=
  DECLARE _BOOLEAN_decode_ber
    WITH (* Context pointer *)
         sh_ctx : share, ctx_b : block, ctx_ofs : ptrofs, ctx : val,
         (* Type Descriptor pointer *)
         sh_td : share, td_b : block, td_ofs : ptrofs, td : TYPE_descriptor,
         (* Value double pointer *)
         sh_val: share, bool_value : val, (* pointer can be null *)
         (* Buffer pointer *)
         sh_buf : share, buf_b : block, buf_ofs : ptrofs, buf : list byte,
         (* pointer to the return struct dec_rval *)                        
         sh_res : share, res_b : block, res_ofs : ptrofs,
         size : Z, tag_mode : Z
    PRE  [
         __res OF (tptr (Tstruct _asn_dec_rval_s noattr)),
         _opt_codec_ctx OF (tptr (Tstruct _asn_codec_ctx_s noattr)),
         _td OF (tptr (Tstruct _asn_TYPE_descriptor_s noattr)),
         _bool_value OF (tptr (tptr tvoid)),
         _buf_ptr OF (tptr tvoid),
         _size OF tuint,
         _tag_mode OF tint]
    PROP ( readable_share sh_ctx; 
           readable_share sh_td; 
           readable_share sh_buf;
           writable_share sh_res;
           is_pointer_or_null bool_value
            )
    LOCAL ( temp _opt_codec_ctx ctx;
            temp _td (Vptr td_b td_ofs);
            temp _bool_value bool_value;
            temp _buf_ptr (Vptr buf_b buf_ofs);
            temp _size (Vint (Int.repr size));
            temp _tag_mode (Vint (Int.repr tag_mode));
            temp _st bool_value)
    SEP (data_at sh_ctx (tptr (Tstruct _asn_codec_ctx_s noattr))
                   (Vptr ctx_b ctx_ofs) ctx;
         data_at sh_td (Tstruct _asn_TYPE_descriptor_s noattr)
                   (TYPE_descriptor_rep td) (Vptr td_b td_ofs);
         data_at sh_buf (tarray tschar (Zlength buf)) (map Vbyte buf) 
                   (Vptr buf_b buf_ofs))
    POST [tvoid]
      PROP()
      LOCAL ()
      SEP( (* Unchanged by the execution : *)
           data_at sh_ctx (tptr (Tstruct _asn_codec_ctx_s noattr))
                   (Vptr ctx_b ctx_ofs) ctx;
           data_at sh_td (Tstruct _asn_TYPE_descriptor_s noattr) 
                   (TYPE_descriptor_rep td) (Vptr td_b td_ofs);
           data_at sh_buf (tarray tschar (Zlength buf)) (map Vbyte buf) 
                   (Vptr buf_b buf_ofs);
           (* Changes according to the exec spec *)
           let RC_FAIL := asn_dec_rval_rep sh_res (Vptr res_b res_ofs) 2 0 in
           if Val.eq bool_value Vnullptr 
           then RC_FAIL
           else let res := bool_decoder td buf in
           match res with
           | Some (r, c) => asn_dec_rval_rep sh_res (Vptr res_b res_ofs) 0 c * 
                            data_at sh_val (tptr tuchar) (Vbyte r) bool_value
           | None => RC_FAIL *
                     data_at sh_val (tptr tuchar)
                             (default_val (tptr tuchar)) bool_value
           end).
           

Definition Gprog2 := ltac:(with_library prog [bool_ber_decode_spec]).

Require Import StructNormalizer.

Eval simpl in struct_normalize (fn_body f_BOOLEAN_decode_ber) composites.
Eval simpl in (fn_body f_BOOLEAN_encode_der).

Definition normalize_function f :=
  mkfunction (fn_return f) (fn_callconv f) (fn_params f) (fn_vars f) (fn_temps f)
             (struct_normalize (fn_body f) composites).

Theorem bool_der_encode : semax_body Vprog Gprog2 (normalize_function f_BOOLEAN_decode_ber)
                                     bool_ber_decode_spec.
  start_function.
Admitted.

End Boolean_ber_decode.
