Require Import Core.Core Lib.Lib Core.StructNormalizer 
        VstLib Prim.Exec Lib.Callback.Dummy Lib.DWT.VST.Der_write_tags.
Require Import VST.floyd.proofauto.
Require Import Clight.dummy Clight.asn_codecs_prim.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Section Der_encode_primitive.

Definition prim_enc_rval td sl buf_size li td_p sptr_p := 
  match evalErrW (primitive_encoder td sl buf_size li) [] with
  | Some v => mk_enc_rval v td_p Vzero
  | None => mk_enc_rval (-1) td_p sptr_p
  end.

Definition prim_enc_res td  sl buf_size li := 
  match execErrW (primitive_encoder td  sl buf_size li) [] with
  | Some v => v
  | None => []
  end.

Definition prim_type_s := (Tstruct _ASN__PRIMITIVE_TYPE_s noattr).
Definition mk_prim_type_s (buf_p : val) size := (buf_p, Vint (Int.repr size)).

Instance Change1 : change_composite_env Callback.Dummy.CompSpecs CompSpecs.
Proof. make_cs_preserve Dummy.CompSpecs CompSpecs. Defined.

Instance Change2 : change_composite_env CompSpecs Dummy.CompSpecs.
Proof. make_cs_preserve CompSpecs Dummy.CompSpecs. Defined.

Instance Change4 : change_composite_env CompSpecs Der_write_tags.CompSpecs.
Proof. make_cs_preserve CompSpecs Der_write_tags.CompSpecs. Defined.


Instance Change3 : change_composite_env Der_write_tags.CompSpecs CompSpecs.
Proof. make_cs_preserve Der_write_tags.CompSpecs CompSpecs. Defined.

Definition der_primitive_encoder_spec : ident * funspec :=
  DECLARE _der_encode_primitive
    WITH res_p : val,  
         sptr_p : val, buf_b : block, buf_ofs : ptrofs, 
         size : Z,
         td_p : val, td : TYPE_descriptor,
         tag_mode : Z,
         cb_p : val, app_key_p : val
    PRE [tptr enc_rval_s, tptr type_descriptor_s, tptr tvoid, tint, tuint, 
          tptr cb_type, tptr tvoid]
    PROP ( tag_mode = 0;
             1 = Zlength (tags td);
         0 <= size <= Int.max_unsigned)
      PARAMS (res_p; td_p; sptr_p; Vint (Int.repr tag_mode);
              Vint (Int.repr 0); cb_p; app_key_p)
      GLOBALS ()
      SEP (data_at_ Tsh enc_rval_s res_p;
           (* sptr *)
           field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr) 
                    (DOT der_encoder._tags) (Vptr buf_b buf_ofs) td_p;
           field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr)
                    (DOT der_encoder._tags_count) (Vint (Int.repr (Zlength (tags td)))) td_p;
           data_at Tsh (tarray tuint (Zlength (tags td))) (map Vint (map Int.repr (tags td)))
                   (Vptr buf_b buf_ofs);
           field_at Tsh prim_type_s (DOT _buf) (Vptr buf_b buf_ofs) sptr_p;
           field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p;
           (* Callback *)
           data_at_ Tsh enc_key_s app_key_p;
           func_ptr' dummy_callback_spec cb_p;
           valid_pointer cb_p)
    POST [tvoid]
    let buf_size := if eq_dec cb_p nullval then 0 else 32 in
      PROP ()
      LOCAL ()
      SEP (field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr) 
                    (DOT der_encoder._tags) (Vptr buf_b buf_ofs) td_p;
           field_at Tsh (Tstruct der_encoder._asn_TYPE_descriptor_s noattr)
                    (DOT der_encoder._tags_count) (Vint (Int.repr (Zlength (tags td)))) td_p;
           data_at Tsh  (tarray tuint (Zlength (tags td)))
                   (map Vint (map Int.repr (tags td)))
                   (Vptr buf_b buf_ofs);
           field_at Tsh prim_type_s (DOT _buf) (Vptr buf_b buf_ofs) sptr_p;
           field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p;
           (* Result *)
           data_at Tsh enc_rval_s (prim_enc_rval td size buf_size (map Int.repr (tags td))
                                                 td_p sptr_p ) res_p;
           (* Callback *)
           valid_pointer cb_p;
           data_at_ Tsh enc_key_s app_key_p;
           func_ptr' dummy_callback_spec cb_p).

Definition Gprog := ltac:(with_library prog [der_primitive_encoder_spec; der_write_tags_spec]).

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
  forward_call (td_p, td, size, 0, 0, cb_p, app_key_p, Vptr buf_b buf_ofs).
  entailer!.
  unfold Frame.
  instantiate (1 := [data_at_ Tsh (Tstruct _asn_enc_rval_s noattr) v_erval ;
                     data_at_ Tsh enc_rval_s res_p;
                     field_at Tsh prim_type_s (DOT _buf) (Vptr buf_b buf_ofs) sptr_p ;
                     field_at Tsh prim_type_s (DOT _size) (Vint (Int.repr size)) sptr_p ]).
  simpl.
  change_compspecs Der_write_tags.CompSpecs.
  entailer!.
  admit. (* change compspecs - same as in der_write_TL *)
  repeat split; auto; try lia.
  forward.
  forward_empty_loop.
  destruct (((Der_write_tags.der_write_tags td size 0 0 0
                   (if Val.eq cb_p nullval then 0 else 32)) []
              )) eqn : DWT. 
  unfold evalErrW.
  erewrite DWT.
  forward_if.
  - (* DWT returns -1 *)
    repeat forward.
    entailer!.
    assert ((Vint (Int.repr (-1)), (td_p, sptr_p))  =
            (prim_enc_rval td size (if eq_dec cb_p nullval then 0 else 32) 
           (map Int.repr (tags td)) td_p sptr_p)) as P.
    { unfold prim_enc_rval.
      unfold evalErrW.
      cbn.
      break_if.
      erewrite e0 in *.
      erewrite if_true in DWT by auto.
      erewrite DWT.
      auto.
      erewrite if_false in DWT by auto.
      erewrite DWT.
      auto. }
    erewrite P.
    entailer!.
    admit. (* change compspecs - same as in der_write_TL *)
  - discriminate.
  - (* DWT returns a *)
    unfold evalErrW.
    erewrite DWT.
    break_let.
    forward_if.
    admit. (* return not -1 - see lemma *) 
    forward_if  [temp _t'11 (Vptr buf_b buf_ofs);
                      temp _t'4 Vone].
    + (* isptr cb *)
      forward.
      forward.
      break_let.
      entailer!.
    + admit. (* cb_p = nullval *)
    + forward_if [temp _t'9 (Vptr buf_b buf_ofs);
                  temp _t'10  (Vint (Int.repr size));
                  temp _t'2  Vzero]; try congruence.
      *
      repeat forward.
      forward_call ((Vptr buf_b buf_ofs), size, app_key_p).
      replace (size <? 0) with false by admit.
      forward_if. congruence.
      forward.
      entailer!.
      * discriminate.
      *
      repeat forward.
      entailer!.
      (* Int.min_signed <= Int.signed (Int.repr (encoded a)) + Int.signed (Int.repr size) <=
  Int.max_signed *) admit.
       match goal with
      | [ _ : _ |- semax _ ?Pre _ _ ] =>
          forward_loop Pre break: Pre 
      end. 
       entailer!.
       repeat forward.
       entailer!.
       { admit. (* func correctness *) }
       admit.
Admitted.

End Der_encode_primitive.

