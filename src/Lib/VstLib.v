Require Import Core.Core.
Require Import VST.floyd.proofauto.
Require Import Clight.asn_codecs_prim Clight.asn_application.
Require Import Lib.

Require Export Lib.

Definition cb_type := (Tfunction 
                          (Tcons (tptr tvoid) 
                                 (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint 
                          cc_default).
Definition type_descriptor_s := Tstruct _asn_TYPE_descriptor_s noattr.
Definition asn_codec_ctx_s := Tstruct _asn_codec_ctx_s noattr.

(* Encoder return struct *)
Definition enc_rval_s := Tstruct _asn_enc_rval_s noattr.
Definition mk_enc_rval encoded (td sptr : val) := 
  (Vint (Int.repr encoded), (td, sptr)).

(* Decoder return struct *)
Definition asn_dec_rval_s := Tstruct _asn_dec_rval_s noattr.
Definition mk_dec_rval code consumed := 
  (Vint (Int.repr code), Vint (Int.repr consumed)).

(* Overrun callback key *)
Definition enc_key_s := Tstruct _overrun_encoder_key noattr.
Definition mk_enc_key (buf : val) size comp_size := 
  (buf, (Vint (Int.repr size), Vint (Int.repr comp_size))). 
