Require Import Core.Core.
Require Import VST.floyd.proofauto.
Require Import Clight.asn_application.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section Encoder_callback.

Definition enc_key := Tstruct _overrun_encoder_key noattr.

Definition constr_enc_key buf size comp_size : reptype enc_key := 
  (buf, (Vint (Int.repr size), Vint (Int.repr comp_size))).

Definition callback : funspec :=
    WITH data : list int, data_p : val, size : Z, key_p : val
    PRE[tptr tvoid, tuint, tptr tvoid]
      PROP()
      PARAMS(data_p; Vint (Int.repr size); key_p)
      GLOBALS()
      SEP((*data_at Tsh (tarray tint size) _ data_p;
          data_at Tsh enc_key (constr_enc_key) key_p; *))
    POST[tint]
      PROP()
      LOCAL(temp ret_temp (Vint (Int.repr 0)))
      SEP().

Definition callback_spec : ident * funspec :=
  DECLARE _overrun_encoder_cb callback.

Definition Gprog := ltac:(with_library prog [callback_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog f_overrun_encoder_cb 
                                     callback_spec.
Admitted.

End Encoder_callback.
