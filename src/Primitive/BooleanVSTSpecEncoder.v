Require Import Core.Core Core.StructNormalizer VstLib 
        BooleanExecSpec ErrorWithWriter DWTVSTSpec.
Require Import VST.floyd.proofauto Psatz.
Require Import Clight.BOOLEAN.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Instance Change1 : change_composite_env CompSpecs DWTVSTSpec.CompSpecs.
Proof. make_cs_preserve CompSpecs DWTVSTSpec.CompSpecs. Defined.
Instance Change2 : change_composite_env DWTVSTSpec.CompSpecs CompSpecs.
Proof. make_cs_preserve DWTVSTSpec.CompSpecs CompSpecs. Defined.

Open Scope Z.

Section Boolean_der_encode_primitive.

Definition int_of_bool (b : bool) := Int.repr (if b then 255 else 0).

Definition bool_der_encode_spec : ident * funspec :=
  DECLARE _BOOLEAN_encode_der
    WITH sptr_p : val, sptr_val : Z, gv : globals,
         (* pointer to the DEF table for the type decoded *)
         td_p : val, td : TYPE_descriptor,
         tag_mode : Z, tag : Z,
         (* local defs *)
         b : bool,
         (* callback pointer *)
         cb_p : val,
         (* callback argument pointer *)
         app_p : val, app_key_val : val
    PRE[(* added by clightgen - since returning structs is not supported *) 
        tptr enc_rval_s, tptr type_descriptor_s, tptr tvoid, tint, 
        tuint, tptr cb_type, tptr tvoid]
      PROP((* If I understood this correctly there is an implicit contract
              on this function, that is, type_descriptor equals bool type 
              if it was passed here, since there isn't any check on tags for it
              to be bool. Alternatively there may not be any implicit contract
              in which case it can lead to malformed output which needs to be
              checked somewhere. Maybe decoder checks for it... *)
           decoder_type td = BOOLEAN_t)
      PARAMS(Vundef; td_p; sptr_p; Vint (Int.repr tag_mode);
             Vint (Int.repr tag); cb_p; app_p)
      GLOBALS(gv)
      SEP((* td points to td with readable permission *) 
          data_at_ Tsh type_descriptor_s td_p; 
          data_at Tsh tint (Vint (int_of_bool b)) sptr_p;
          data_at_ Tsh tvoid app_p;
          valid_pointer cb_p; func_ptr cb_spec cb_p)
    POST [tvoid]
      PROP()
      LOCAL(lvar _bool_value tuchar (gv _bool_value);
            lvar _erval enc_rval_s (gv _erval))
      SEP((* Unchanged by the execution : *)
          data_at Tsh tuchar 
                  (Vbyte (match execErrW (bool_encoder td b) [] with
                   | Some v => last v (Byte.repr (-1))
                   | None => (Byte.repr (-1))
                   end)) (gv _bool_value) ;
          data_at Tsh enc_rval_s 
                  (match evalErrW (bool_encoder td b) [] with
                   | Some v => construct_enc_rval (encoded v) td sptr_p
                   | None => construct_enc_rval (-1) td sptr_p
                   end) (gv _erval) ;
          data_at_ Tsh type_descriptor_s td_p ; 
          data_at Tsh tint (Vbyte (bool_to_byte b)) sptr_p ;
          data_at_ Tsh tvoid app_p ;
          valid_pointer cb_p; func_ptr cb_spec cb_p).

Definition Gprog := ltac:(with_library prog [der_write_tags_spec; 
                                               bool_der_encode_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog 
                                     (normalize_function 
                                        f_BOOLEAN_encode_der composites) 
                                     bool_der_encode_spec.
Proof.
  start_function.
  forward.
  forward_call (td_p, td, 1, tag_mode, 0, tag, cb_p, app_p, app_key_val).
  rewrite DWTExecSpec.eval_dwt_boolean by assumption.
  unfold_data_at_ v_erval.
  unfold_data_at (data_at _ _ _ v_erval).
  forward.
  forward.
  forward_if; [contradiction|].
  forward_if (cb_p = nullval).
  * (* if(cb) = true *)
    forward.
    (* bool_value = *st ? 0xff : 0; /* 0xff mandated by DER */ *)
    forward_if (PROP(b = true \/ b = false)
                LOCAL(temp _t'2 (Vint (Int.repr (if b then 255 else 0))))
                SEP()).
    - (* if(b) = true *)
      forward.
      entailer!.
    - (* if(b) = false *)
      forward.
      entailer!.
    -
      Intros.
      destruct b eqn:B.
      admit.
      admit.
  * (* if(cb) = false *)
    forward.
    entailer!.
  *
    forward.
    forward.
    forward_loop 
      (PROP() LOCAL() SEP()) 
      (* This must be a postcondition of whole function *)
      break:(PROP() 
             LOCAL()
             SEP(field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _encoded) 
                          (Vint (Int.add (Int.repr 2) (Int.repr 1))) v_erval; 
                 field_at Tsh (Tstruct _asn_enc_rval_s noattr) (DOT _failed_type) 
                          (default_val 
                             (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) 
                          v_erval)).
    - entailer!.
    - admit.
    - admit.
     

  

End Boolean_der_encode_primitive.
