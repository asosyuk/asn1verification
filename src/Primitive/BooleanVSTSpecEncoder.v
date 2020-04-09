Require Import Core.Core Core.StructNormalizer VstLib 
        BooleanExecSpec ErrorWithWriter DWTVSTSpec.
Require Import VST.floyd.proofauto Psatz.
Require Import Clight.BOOLEAN.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section Boolean_der_encode_primitive.

Definition bool_der_encode_spec : ident * funspec :=
  DECLARE _BOOLEAN_encode_der
    WITH sptr_p : val, sptr_val : Z,
         (* pointer to the DEF table for the type decoded *)
         td_p : val, td : TYPE_descriptor,
         tag_mode : Z, tag : Z,
         (* local defs *)
         b : bool, b_addr : val, v_erval : val, erval_addr : val,
         (* callback pointer *)
         cb_p : val, cb_val : val,
         (* callback argument pointer *)
         app_p : val, app_key_val : val
    PRE  [         
          (* added by clightgen - since returning structs is not supported *) 
          __res OF (tptr enc_rval_s),
          _td OF (tptr type_descriptor_s),
          _sptr OF (tptr tvoid), 
          _tag_mode OF tint,
          _tag OF tuint,
          _cb OF (tptr cb_type),
          _app_key OF (tptr tvoid)
           ]
    PROP ( )
    LOCAL ( temp _td td_p;
            temp _sptr sptr_p;
            temp _tag_mode (Vint (Int.repr tag_mode));
            temp _tag (Vint (Int.repr tag));
            temp _cb cb_p;
            temp _app_key app_p(*;
            lvar _bool_value tuchar (Vbyte (bool_to_byte b));
            lvar _erval enc_rval_s v_erval*))
    SEP ((* td points to td with readable permission *)
          data_at_ Tsh tuchar  b_addr;
          data_at_ Tsh enc_rval_s erval_addr ;
          data_at_ Tsh type_descriptor_s td_p ; 
          data_at Tsh tint (Vbyte (bool_to_byte b)) sptr_p ;
          data_at Tsh tvoid tt app_p ;
          data_at Tsh cb_type tt cb_p)
    POST [tvoid]
      PROP()
      LOCAL (lvar _bool_value tuchar b_addr;
             lvar _erval enc_rval_s erval_addr)
      SEP( (* Unchanged by the execution : *)
           data_at Tsh tuchar 
                   (Vbyte (match execErrW (bool_encoder td b) [] with
                    | Some v => last v (Byte.repr (-1))
                    | None => (Byte.repr (-1))
                    end)) b_addr ;
           data_at Tsh enc_rval_s 
                   (match evalErrW (bool_encoder td b) [] with
                    | Some v => construct_enc_rval (encoded v) td sptr_p
                    | None => construct_enc_rval (-1) td sptr_p
                    end) erval_addr ;
           data_at_ Tsh type_descriptor_s td_p ; 
           data_at Tsh tint (Vbyte (bool_to_byte b)) sptr_p ;
           data_at Tsh tvoid tt app_p ;
           data_at Tsh cb_type tt cb_p).

Definition Gprog := ltac:(with_library prog [der_write_tags_spec; 
                                               bool_der_encode_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog 
                                     (normalize_function 
                                        f_BOOLEAN_encode_der composites) 
                                     bool_der_encode_spec.
Proof.
  (*start_function.
  forward.
forward_call (td_p, td, 1, tag_mode, 0, tag, cb_p, cb_val, app_p, app_key_val). *)
Admitted.

End Boolean_der_encode_primitive.
