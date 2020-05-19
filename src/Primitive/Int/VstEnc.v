Require Import Core.Core Lib.Lib Core.StructNormalizer 
        VstLib Int.Exec Lib.Callback.Dummy Lib.DWT.Vst.
Require Import VST.floyd.proofauto.
Require Import Clight.dummy Clight.INTEGER.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Section Integer_der_encode.

Definition int_der_encode_spec : ident * funspec :=
  DECLARE _INTEGER_encode_der
    WITH res: val,  sptr_p : val, sptr_val : int, 
         td_p : val, td : TYPE_descriptor,
         tag_mode : Z, tag : Z,
         cb_p : val, app_key_p : val
    PRE [tptr enc_rval_s, tptr type_descriptor_s, tptr tvoid, tint, tuint, 
          tptr cb_type, tptr tvoid]
      PROP (decoder_type td = BOOLEAN_t)
      PARAMS (res; td_p; sptr_p; Vint (Int.repr tag_mode);
              Vint (Int.repr tag); cb_p; app_key_p)
      GLOBALS ()
      SEP ()
    POST [tvoid]
      PROP()
      LOCAL ()
      SEP().

Definition Gprog := ltac:(with_library prog [int_der_encode_spec]).

Theorem int_der_encode : semax_body Vprog Gprog 
                                     (normalize_function f_INTEGER_encode_der
                                                         composites)
                                     int_der_encode_spec.
Proof.
  Fail start_function. 
Admitted.

End Integer_der_encode.
