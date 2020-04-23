Require Import Core.Core.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Clight.asn_application Lib.Stdlib.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section Encoder_callback.

Definition enc_key_s := Tstruct _overrun_encoder_key noattr.

Definition mk_enc_key buf size comp_size : reptype enc_key_s := 
  (buf, (Vint (Int.repr size), Vint (Int.repr comp_size))). 

Definition callback  : funspec :=
    WITH data : list int, data_p : val, size : Z,
         app_key : val, app_key_p : val, 
         buf_b : block, buf_ofs : ptrofs,
         buf_size : Z, computed_size : Z
    PRE [tptr tvoid, tuint, tptr tvoid]
      PROP (size = Zlength data)
      PARAMS (data_p; Vint (Int.repr size); app_key_p)
      GLOBALS ()
      SEP (data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) data_p;
           data_at Tsh enc_key_s 
                   (mk_enc_key (Vptr buf_b buf_ofs) buf_size computed_size) 
                   app_key_p;
           memory_block Tsh buf_size (Vptr buf_b buf_ofs))
    POST [tint]
      PROP ()
      LOCAL (temp ret_temp Vzero)
      SEP (data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) data_p;
           if buf_size <? computed_size + size 
           then memory_block Tsh buf_size (Vptr buf_b buf_ofs) *
                data_at Tsh enc_key_s 
                   (mk_enc_key (Vptr buf_b buf_ofs) 0 computed_size) 
                   app_key_p
           else 
             (data_at Tsh 
                      (tarray tuchar size) (map Vint data) 
                      (Vptr buf_b (Ptrofs.add buf_ofs (Ptrofs.repr computed_size))) * 
              data_at Tsh enc_key_s 
                      (mk_enc_key (Vptr buf_b buf_ofs)
                                  buf_size (computed_size + size)) app_key_p)). 

Definition dummy_callback  : funspec :=
    WITH  data_p : val, size : Z,
         app_key_p : val
    PRE [tptr tvoid, tuint, tptr tvoid]
      PROP ()
      PARAMS (data_p; Vint (Int.repr size); app_key_p)
      GLOBALS ()
      SEP ()
    POST [tint]
      PROP ()
      LOCAL (temp ret_temp Vzero)
      SEP (). 

Definition callback_overrun_spec : ident * funspec :=
  DECLARE _overrun_encoder_cb callback.

Definition Gprog := ltac:(with_library prog [callback_overrun_spec; (_memcpy, memcpy_spec)]).

Theorem bool_der_encode : semax_body Vprog Gprog f_overrun_encoder_cb 
                                     callback_overrun_spec.
  Proof.
    start_function.
    repeat forward; simpl.
    unfold MORE_COMMANDS.
    unfold abbreviate.
    forward_if 
      (PROP ()
       LOCAL (temp _t'3 (Vint (Int.repr buf_size)); temp _t'2 (Vint (Int.repr computed_size));
              temp _key app_key_p; temp _data data_p; temp _size (Vint (Int.repr size));
              temp _keyp app_key_p)
       SEP (data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) data_p;
           if buf_size <? computed_size + size 
           then memory_block Tsh buf_size (Vptr buf_b buf_ofs) *
                data_at Tsh enc_key_s 
                   (mk_enc_key (Vptr buf_b buf_ofs) 0 computed_size) 
                   app_key_p
           else 
             (data_at Tsh 
                      (tarray tuchar size) (map Vint data) 
                      (Vptr buf_b (Ptrofs.add buf_ofs (Ptrofs.repr computed_size))) * 
              data_at Tsh enc_key_s 
                      (mk_enc_key (Vptr buf_b buf_ofs)
                                  buf_size (computed_size + size)) app_key_p))).
    forward.
    entailer!.
    admit.
    repeat forward.
    (* qsh : share, psh: share, p: val, q: val, n: Z, contents: list int *)
    forward_call (Tsh, Tsh, Vptr buf_b (Ptrofs.add buf_ofs (Ptrofs.repr computed_size)), data_p,
                  size, data).
    entailer!.
    simpl.
    admit.
    entailer!.
    admit.
    admit.
    entailer!.
    entailer!.
    admit. 
    break_if.
    Intros.
    repeat forward.
    entailer!.
    admit.
    Intros.
    repeat forward.
    entailer!.
    admit.
Admitted.

End Encoder_callback. 
