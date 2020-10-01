Require Import Core.Core Core.StructNormalizer VstLib Callback.Dummy
        Boolean.Exec ErrorWithWriter DWT.Vst.
Require Import VST.floyd.proofauto.
Require Import Clight.dummy Clight.BOOLEAN Clight.der_encoder.
Require Import Core.Notations. 
Require Import Boolean.Exec AbstractSpec Lib PrimExec.
Require Import Clight.dummy Clight.BOOLEAN Lib.Stdlib.
Require Import Clight.ber_decoder.
Require Import Lib.BCT.Vst.

Hypothesis der_encoder_correctness : forall td b ls z,
  decoder_type td = BOOLEAN_t ->
  bool_encoder td b [] = inr (ls, z) ->
  DER (BOOLEAN b) ls.

(* Need Exec.der_fetch_tags correctness *)

Hypothesis ber_decoder_correctness : forall td ls b z,
    decoder_type td = BOOLEAN_t ->
    bool_decoder td ls = Some (b, z) ->
    BER (BOOLEAN b) ls.

(* Need Exec.ber_check_tags correctness *)

Hypothesis boolean_roundtrip : forall td ls b z,
    decoder_type td = BOOLEAN_t ->
    bool_encoder td b [] = inr (ls, z) ->
    bool_decoder td ls = Some (b, z).

(* Need der_fetch_tags correctness *)

Definition bool_ber_decode_spec : ident * funspec :=
  DECLARE _BOOLEAN_decode_ber
    (* FORALL parameters *)
    WITH ctx_p : val, ctx : val, td_p : val, td : TYPE_descriptor,
         bv_pp : val, buf_p : val, buf : list byte,
         res_p : val, size : Z, tag_mode : Z
    (* PRECONDITION *)
    PRE [tptr asn_dec_rval_s, tptr asn_codec_ctx_s, tptr type_descriptor_s,
          tptr (tptr tvoid), tptr tvoid, tuint, tint] 
      PROP (decoder_type td = BOOLEAN_t; 
            0 <= size <= Int.max_signed;
            Zlength buf = size)
      PARAMS (res_p; ctx_p; td_p; bv_pp; buf_p; Vint (Int.repr size);
                Vint (Int.repr tag_mode))
      GLOBALS ()
      SEP (EX bv_p : val, 
              (data_at Tsh (tptr tvoid) bv_p bv_pp *
               valid_pointer bv_p *
               if eq_dec bv_p nullval 
               then emp
               else data_at_ Ews tint bv_p);
           data_at_ Tsh asn_dec_rval_s res_p;
                   
           data_at Tsh asn_codec_ctx_s ctx ctx_p;
           data_at_ Tsh type_descriptor_s td_p;
           data_at Tsh (tarray tuchar (len buf)) (map Vubyte buf) buf_p)
    (* POSTCONDITION *)
    POST [tvoid] 
      PROP ()
      LOCAL ()
      let res_val :=
          match bool_decoder td buf with
          | Some (r, c) => ((Vzero, Vint (Int.repr c)),
                           (Vubyte (byte_of_bool r)))
          | None => ((Vint (Int.repr 2), Vzero), Vone) end in
      SEP (EX bv_p : val, 
              valid_pointer bv_p *
              data_at Tsh (tptr tvoid) bv_p bv_pp *
              (* If allocation of memory fails, 
                 write the fail result *)
              if eq_dec bv_p nullval 
              then data_at Tsh asn_dec_rval_s (Vint (Int.repr 2), Vzero) res_p
              else (* Correspondence to the exec spec,
                      we write correct result in the memory *)
                data_at Tsh asn_dec_rval_s
                        (fst res_val) res_p *
                data_at Ews tint (snd res_val) bv_p;
             (* Unchanged memory *)
             data_at Tsh asn_codec_ctx_s ctx ctx_p;
             data_at_ Tsh type_descriptor_s td_p;
             data_at Tsh (tarray tuchar (len buf)) (map Vubyte buf) buf_p).
                                   
(* We are proving: forall x in parameters, 
   the separation logic triple 
   PRECONDITION {f_BOOLEAN_decode_ber} POSTCONDITION
   holds *)

Definition Vprog_dec : varspecs. mk_varspecs prog. Defined.

Definition Gprog_dec := ltac:(with_library prog [(_calloc, calloc_spec);
                                                   ber_check_tags_spec; 
                                                   bool_ber_decode_spec]).


(* BOOLEAN_decode_ber corresponds to bool_ber_decode_spec
   This means that BOOLEAN_decode_ber is correct, when auxiliary functions in the code
   satisfy the specs from Gprog *)

Hypothesis bool_ber_decode_correctness : 
  semax_body Vprog Gprog (normalize_function f_BOOLEAN_decode_ber composites) 
             bool_ber_decode_spec.

(* BOOLEAN_decode_ber fully corresponds to bool_ber_decode_spec 
   This means that BOOLEAN_decode_ber is correct and that selected
   auxiliary functions in the code
   satisfy the specs from Gprog *)       

Inductive full_correctness (f : function) (f_spec : ident * funspec) 
      (aux_fs : list function) (V : varspecs) (G : list (ident * funspec)) : Prop :=
| NoAuxCorr : aux_fs = [] -> 
          semax_body V G f f_spec ->
          full_correctness f f_spec aux_fs V G
| WithAuxCorr g fs V' G' g_spec: 
    aux_fs = g :: fs ->
    semax_body V G f f_spec ->
    (* all aux functions (aux_fs) correspond to the aux specs *)
    In g_spec G -> 
    g_spec <> f_spec ->
    full_correctness g g_spec fs V' G' ->
    full_correctness f f_spec aux_fs V G.

(* C implementation of calloc *)
Parameter f_calloc : function.

(* We assume f_calloc is correct *)
Hypothesis full_boolean_decoder_correctness :
  exists V G, semax_body V G f_calloc (_calloc, calloc_spec)  -> 
  full_correctness (normalize_function f_BOOLEAN_decode_ber composites)
                   bool_ber_decode_spec
                   [f_ber_check_tags]
                   Vprog_dec Gprog_dec.

Definition bool_der_encode_spec : ident * funspec :=
  DECLARE _BOOLEAN_encode_der
    (* FORALL parameters *)
    WITH res: val,  sptr_p : val, sptr_val : int, 
         td_p : val, td : TYPE_descriptor,
         tag_mode : Z, tag : Z,
         app_key_p : val,
         buf_b : block, buf_ofs : ptrofs, cb_p : val
    (* PRECONDITION *)
    PRE [tptr enc_rval_s, tptr type_descriptor_s, tptr tvoid, tint, 
         tuint, tptr cb_type, tptr tvoid]
      PROP (decoder_type td = BOOLEAN_t)
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
      SEP ((* Correspondence to the exec spec: 
              after executing the function on any input thats satisfies
              the precondition,
              we write the result of bool_encoder in the memory *)
          let res_val := 
              match evalErrW (bool_encoder td (bool_of_int sptr_val)) [] with 
              | Some v => mk_enc_rval v Vzero 
              | None => mk_enc_rval (-1) sptr_p end in
          data_at Tsh enc_rval_s res_val res;
          (* Unchanged memory:
             we didn't modify memory we were not supposed to *)
          data_at_ Tsh type_descriptor_s td_p; 
          data_at Tsh tint (Vint sptr_val) sptr_p;
          data_at_ Tsh tvoid app_key_p;
          valid_pointer cb_p).

(* We are proving: forall x in parameters, 
   the separation logic triple 
   PRECONDITION {f_BOOLEAN_encode_der} POSTCONDITION
   holds *)

Definition Vprog_enc : varspecs. mk_varspecs prog. Defined.

(* Note: we are proving correctness for _cb refering to f_dummy *)

Definition Gprog_enc := ltac:(with_library prog [der_write_tags_spec; 
                                                 (_cb, dummy_callback_spec); 
                                                 bool_der_encode_spec]).

Hypothesis bool_der_encode :
  semax_body Vprog_enc Gprog_enc (normalize_function f_BOOLEAN_encode_der composites)
             bool_der_encode_spec.

Hypothesis full_boolean_encode_correctness :
  full_correctness (normalize_function f_BOOLEAN_encode_der composites)
                   bool_der_encode_spec
                   [f_der_write_tags; f_dummy]
                   Vprog_dec Gprog_dec.



