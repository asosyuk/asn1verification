Require Import Core.Core.
Require Import VST.floyd.proofauto.
Require Import Clight.asn_application.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section Encoder_callback.

Definition enc_key_s := Tstruct _overrun_encoder_key noattr.

Definition mk_enc_key buf size comp_size : reptype enc_key_s := 
  (buf, (Vint (Int.repr size), Vint (Int.repr comp_size))). 

Definition callback  : funspec :=
    WITH b : bool, data : list int, data_p : val, size : Z,
         app_key : val, app_key_p : val, 
         buf_b : block, buf_ofs : ptrofs,
         buf_size : Z, computed_size : Z
    PRE [tptr tvoid, tuint, tptr tvoid]
      PROP ()
      PARAMS (data_p; Vint (Int.repr size); app_key_p)
      GLOBALS ()
      SEP (data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) data_p;
           data_at Tsh enc_key_s 
                   (mk_enc_key (Vptr buf_b buf_ofs) buf_size computed_size) 
                   app_key_p;
           data_at_ Tsh tvoid (Vptr buf_b buf_ofs))
    POST [tint]
      PROP ()
      LOCAL (temp ret_temp Vzero)
      SEP (data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) data_p;
           data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) 
                   (Vptr buf_b (Ptrofs.add buf_ofs (Ptrofs.repr computed_size))); 
           data_at Tsh enc_key_s 
                  (mk_enc_key (Vptr buf_b buf_ofs) buf_size size) app_key_p).

Definition callback_overrun_spec : ident * funspec :=
  DECLARE _overrun_encoder_cb callback.

Definition Gprog := ltac:(with_library prog [callback_overrun_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog f_overrun_encoder_cb 
                                     callback_overrun_spec.
Admitted.

End Encoder_callback. 
