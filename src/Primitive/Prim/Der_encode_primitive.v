Require Import Core.Core Lib.Lib Core.StructNormalizer 
        VstLib Prim.Exec Lib.Callback.Dummy Lib.DWT.Vst.
Require Import VST.floyd.proofauto.
Require Import Clight.dummy Clight.asn_codecs_prim.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Section Der_encode_primitive.

Definition prim_enc_rval td li sptr_p := 
  match evalErrW (primitive_encoder td li) [] with
  | Some v => mk_enc_rval (encoded v) Vzero
  | None => mk_enc_rval (-1) sptr_p
  end.

Definition prim_enc_res td li := 
  match execErrW (primitive_encoder td li) [] with
  | Some v => v
  | None => []
  end.

Definition prim_type_s := (Tstruct _ASN__PRIMITIVE_TYPE_s noattr).
Definition mk_prim_type_s (buf_p : val) size := (buf_p, Vint (Int.repr size)).

Definition der_primitive_encoder_spec : ident * funspec :=
  DECLARE _der_encode_primitive
    WITH res_p : val,  
         sptr_p : val, buf_b : block, buf_ofs : ptrofs, 
         size : Z, data : list byte,
         td_p : val, td : TYPE_descriptor,
         tag_mode : Z, tag : Z,
         cb_p : val, app_key_p : val
    PRE [tptr enc_rval_s, tptr type_descriptor_s, tptr tvoid, tint, tuint, 
          tptr cb_type, tptr tvoid]
      PROP ()
      PARAMS (res_p; td_p; sptr_p; Vint (Int.repr tag_mode);
              Vint (Int.repr tag); cb_p; app_key_p)
      GLOBALS ()
      SEP (data_at_ Tsh enc_rval_s res_p;
           data_at_ Tsh type_descriptor_s td_p; 
           (* sptr *)
           valid_pointer (Vptr buf_b buf_ofs);
           if Val.eq (Vptr buf_b buf_ofs) nullval 
           then emp
           else data_at Tsh (tarray tuchar size) (map Vubyte data) (Vptr buf_b buf_ofs);
           field_at Tsh prim_type_s (DOT _buf) (Vptr buf_b buf_ofs) sptr_p;
           field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p;
           (* Callback *)
           data_at_ Tsh enc_key_s app_key_p;
           valid_pointer cb_p)
    POST [tvoid]
      PROP ()
      LOCAL ()
      SEP (data_at_ Tsh type_descriptor_s td_p;
           (* sptr *)
           valid_pointer (Vptr buf_b buf_ofs);
           if Val.eq (Vptr buf_b buf_ofs) nullval 
           then emp
           else data_at Tsh (tarray tuchar size) (map Vubyte (prim_enc_res td data)) 
                        (Vptr buf_b buf_ofs);
           data_at Tsh prim_type_s (mk_prim_type_s (Vptr buf_b buf_ofs) size) sptr_p;
           (* Result *)
           data_at Tsh enc_rval_s (prim_enc_rval td data sptr_p) res_p;
           (* Callback *)
           valid_pointer cb_p;
           data_at_ Tsh enc_key_s app_key_p;
           func_ptr' dummy_callback_spec cb_p).

Definition Gprog := ltac:(with_library prog [der_primitive_encoder_spec]).

Ltac forward_empty_loop :=
      match goal with
      | [ _ : _ |- semax _ ?Pre (Ssequence (Sloop Sskip Sbreak) _) _ ] =>
          forward_loop Pre break: Pre; try forward ; try entailer! 
      end. 

Theorem der_encode_primitive : semax_body Vprog Gprog 
                                          (normalize_function f_der_encode_primitive 
                                                              composites) 
                                          der_primitive_encoder_spec.
Proof.
  start_function. 
  forward.
  forward_empty_loop.
  forward_call (gv, td_p, td, 1, tag_mode, 0, tag, app_key_p, buf_b, buf_ofs, 
                buf_size, computed_size, mem_size).

Admitted.

End Der_encode_primitive.

