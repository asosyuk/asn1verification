Require Import Core.Core Core.StructNormalizer VstLib 
        BooleanExecSpec ErrorWithWriter DWTVSTSpec.
Require Import VST.floyd.proofauto Psatz.
Require Import Clight.BOOLEAN. (*Clight.der_encoder.*)

(*Definition prog : Clight.program := 
  mkprogram composites 
            (Clight.BOOLEAN.global_definitions ++ 
             Clight.der_encoder.global_definitions) 
            (Clight.BOOLEAN.public_idents ++ Clight.der_encoder.public_idents)
            _main Logic.I.*)

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section Boolean_der_encode_primitive.

Definition bool_der_encode_spec : ident * funspec :=
  DECLARE _BOOLEAN_encode_der
    WITH sptr_p : val, sptr_val : Z, sh_sptr : share,
         (* pointer to the DEF table for the type decoded *)
         td_p : val, sh_td : share, td : TYPE_descriptor,
         tag_mode : Z, tag : Z,
         (* callback pointer *)
         cb_p : val, cb_val : val, sh_cb : share,
         (* callback argument pointer *)
         app_p : val, app_key_val : val, sh_app_key : share
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
    PROP ( readable_share sh_td;
           writable_share sh_sptr; 
           readable_share sh_cb;
           readable_share sh_app_key )
    LOCAL ( temp _td td_p;
            temp _sptr sptr_p;
            temp _tag_mode (Vint (Int.repr tag_mode));
            temp _tag (Vint (Int.repr tag));
            temp _cb cb_p;
            temp _app_key app_p)
    SEP ((* td points to td with readable permission *)
           data_at sh_td type_descriptor_s (TYPE_descriptor_rep td) td_p ; 
           data_at sh_sptr (tvoid) (tt) sptr_p ;
           data_at sh_app_key (tvoid) (tt) app_p ;
           data_at sh_cb (cb_type) (tt) cb_p)
    POST [tvoid]
      PROP()
      LOCAL ()
      SEP( (* Unchanged by the execution : *)
           data_at sh_td type_descriptor_s (default_val type_descriptor_s) td_p ; 
           data_at sh_sptr (tvoid) (tt) sptr_p ;
           data_at sh_app_key (tvoid) (tt) app_p ;
           data_at sh_cb (cb_type) (tt) cb_p).

Definition Gprog := ltac:(with_library prog [der_write_tags_spec; 
                                               bool_der_encode_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog 
                                     (normalize_function 
                                        f_BOOLEAN_encode_der composites) 
                                     bool_der_encode_spec.
Proof.
  start_function.
  (*unfold fold_right; apply semax_frame;[lazy;auto|].*)
  forward.
  forward_call (td_p, td, sh_td, 1, tag_mode, 0, tag, cb_p, 
                cb_val, sh_cb, app_p, app_key_val, sh_app_key).
Admitted.

End Boolean_der_encode_primitive.
