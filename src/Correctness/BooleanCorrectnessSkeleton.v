Require Import Core.Core Core.StructNormalizer VstLib Callback.Dummy
        Boolean.Exec ErrorWithWriter DWT.Vst.
Require Import VST.floyd.proofauto.
Require Import Clight.dummy Clight.BOOLEAN.
Require Import Core.Notations. 
Require Import Boolean.Exec AbstractSpec Lib Prim.Exec.
Require Import Clight.dummy Clight.BOOLEAN.

Hypothesis der_encoder_correctness : forall td b ls z,
  decoder_type td = BOOLEAN_t ->
  bool_encoder td b [] = inr (ls, z) ->
  DER (BOOLEAN b) ls.

Hypothesis ber_decoder_correctness : forall td ls b z,
    decoder_type td = BOOLEAN_t ->
    bool_decoder td ls = Some (b, z) ->
    BER (BOOLEAN b) ls.

Hypothesis boolean_roundtrip : forall td ls b z,
    decoder_type td = BOOLEAN_t ->
    bool_encoder td b [] = inr (ls, z) ->
    bool_decoder td ls = Some (b, z).

Definition bool_der_encode_spec : ident * funspec :=
  DECLARE _BOOLEAN_encode_der
    (* parameters *)
    WITH res: val,  sptr_p : val, sptr_val : int, 
         td_p : val, td : TYPE_descriptor,
         tag_mode : Z, tag : Z,
         app_key_p : val,
         buf_b : block, buf_ofs : ptrofs, cb_p : val
    (* PRECONDITION *)
    PRE [tptr enc_rval_s, tptr type_descriptor_s, tptr tvoid, tint, 
         tuint, tptr cb_type, tptr tvoid]
      PROP (decoder_type td = BOOLEAN_t;
            isptr (Vptr buf_b buf_ofs))
      PARAMS (res; td_p; sptr_p; Vint (Int.repr tag_mode);
              Vint (Int.repr tag); cb_p; app_key_p)
      GLOBALS ()
      SEP (data_at_ Tsh enc_rval_s res;
           data_at_ Tsh type_descriptor_s td_p; 
           data_at Tsh tint (Vint sptr_val) sptr_p;
           data_at_ Tsh tvoid app_key_p;
           valid_pointer cb_p)
    (* POSTCONDITION *)
    POST [tvoid]
      PROP ()
      LOCAL ()
      let res_val := 
          match evalErrW (bool_encoder td (bool_of_int sptr_val)) [] with 
                     | Some v => mk_enc_rval v Vzero 
                     | None => mk_enc_rval (-1) sptr_p end in
      SEP (data_at Tsh enc_rval_s res_val res;
           data_at_ Tsh type_descriptor_s td_p; 
           data_at Tsh tint (Vint sptr_val) sptr_p;
           data_at_ Tsh tvoid app_key_p;
           valid_pointer cb_p).

(* We are proving: forall x in parameters, 
   the separation logic triple 
   PRECONDITION {f_BOOLEAN_encode_der} POSTCONDITION
   holds *)

Hypothesis bool_der_encode :
  semax_body Vprog Gprog (normalize_function f_BOOLEAN_encode_der composites)
             bool_der_encode_spec.

Definition bool_ber_decode_spec : ident * funspec :=
  DECLARE _BOOLEAN_decode_ber
    (* parameters *)
    WITH ctx_p : val, ctx : val, td_p : val, td : TYPE_descriptor,
         bv_pp : val, buf_p : val, buf : list byte,
         res_p : val, size : Z, tag_mode : Z, bv_p : val
    (* PRECONDITION *)
    PRE [tptr asn_dec_rval_s, tptr asn_codec_ctx_s, tptr type_descriptor_s,
          tptr (tptr tvoid), tptr tvoid, tuint, tint] 
      PROP (is_pointer_or_null bv_p; decoder_type td = BOOLEAN_t; 
            0 <= size <= Int.max_signed;
            Zlength buf = size)
      PARAMS (res_p; ctx_p; td_p; bv_pp; buf_p; Vint (Int.repr size);
                Vint (Int.repr tag_mode))
      GLOBALS ()
      SEP (valid_pointer bv_p;
           if eq_dec bv_p nullval 
           then emp
           else data_at_ Ews tint bv_p ; 
           data_at Tsh asn_codec_ctx_s ctx ctx_p;
           data_at_ Tsh type_descriptor_s td_p;
           data_at Tsh (tarray tuchar (Zlength buf)) (map Vubyte buf) buf_p;
           data_at Tsh (tptr tvoid) bv_p bv_pp;
           data_at_ Tsh asn_dec_rval_s res_p)
    (* POSTCONDITION *)
    POST [tvoid] 
      PROP ()
      LOCAL ()
      SEP (valid_pointer bv_p;
           data_at Tsh asn_codec_ctx_s ctx ctx_p;
           data_at_ Tsh type_descriptor_s td_p;
           data_at Tsh (tarray tuchar (len buf)) (map Vubyte buf) buf_p;
           let res_val := match bool_decoder td buf with
                          | Some (r, c) => ((Vzero, Vint (Int.repr c)),
                                           (Vubyte (byte_of_bool r)))
                          | None => ((Vint (Int.repr 2), Vzero), Vone)
                          end in
           EX v : val,
                  EX ls : list val, data_at Tsh (tptr tvoid) v bv_pp *
                                    if eq_dec v nullval 
                                    then data_at Tsh asn_dec_rval_s
                                                 (Vint (Int.repr 2), Vzero) res_p
                                    else data_at Tsh asn_dec_rval_s
                                                 (fst res_val) res_p *
                                         data_at Ews tint (snd res_val) v).
                                    
(* We are proving: forall x in parameters, 
   the separation logic triple 
   PRECONDITION {f_BOOLEAN_decode_ber} POSTCONDITION
   holds *)

Hypothesis bool_ber_decode_correctness : 
  semax_body Vprog Gprog (normalize_function f_BOOLEAN_decode_ber composites) 
             bool_ber_decode_spec.
