Require Import Core.Core Core.Tactics.
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
    WITH (* parameters *)
         data : list int, data_p : val, 
         size : Z,
         key : val, key_p : val, 
         (* overrun_encoder_key fields *)
         buf_b : block, buf_ofs : ptrofs,
         buf_size : Z, computed_size : Z
    PRE [tptr tvoid, tuint, tptr tvoid]
      PROP (size = Zlength data;
            0 <= buf_size <= Int.max_unsigned;
            0 <= computed_size <= Int.max_unsigned;
            0 <= size <= Int.max_unsigned;
            0 <= computed_size + size <= Int.max_unsigned)
      PARAMS (data_p; Vint (Int.repr size); key_p)
      GLOBALS ()
      SEP (data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) data_p;
           data_at Tsh enc_key_s 
                   (mk_enc_key (Vptr buf_b buf_ofs) buf_size computed_size) 
                   key_p;
           memory_block Tsh buf_size (Vptr buf_b buf_ofs))
    POST [tint]
      PROP ()
      LOCAL (temp ret_temp Vzero)
      SEP (data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) data_p;
           if buf_size <? computed_size + size 
           then memory_block Tsh buf_size (Vptr buf_b buf_ofs) *
                data_at Tsh enc_key_s 
                   (mk_enc_key (Vptr buf_b buf_ofs) 0 (computed_size + size))  
                   key_p
           else 
             (memory_block Tsh computed_size (Vptr buf_b buf_ofs) *
              data_at Tsh 
                      (tarray tuchar size) (map Vint data) 
                      (Vptr buf_b (Ptrofs.add buf_ofs
                                              (Ptrofs.repr computed_size))) *
              memory_block Tsh (buf_size - computed_size - size) 
                           (Vptr buf_b
                                 (Ptrofs.add buf_ofs
                                             (Ptrofs.repr 
                                                (computed_size + size)))) *
              data_at Tsh enc_key_s 
                      (mk_enc_key (Vptr buf_b buf_ofs)
                                  buf_size (computed_size + size)) key_p)). 

Definition dummy_callback  : funspec :=
    WITH  data_p : val, size : Z,
         key_p : val
    PRE [tptr tvoid, tuint, tptr tvoid]
      PROP ()
      PARAMS (data_p; Vint (Int.repr size); key_p)
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
    destruct (buf_size <? computed_size + size) eqn : Q.
    - 
    repeat forward.
    assert (buf_size < computed_size + size) by (Zbool_to_Prop; eassumption).
    forward_if 
      (PROP ()
       LOCAL (temp _t'3 (Vint (Int.repr buf_size)); 
              temp _t'2 (Vint (Int.repr computed_size));
              temp _key key_p; temp _data data_p; 
              temp _size (Vint (Int.repr size));
              temp _keyp key_p)
       SEP (data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) data_p;
            memory_block Tsh buf_size (Vptr buf_b buf_ofs) ;
            data_at Tsh enc_key_s 
                   (mk_enc_key (Vptr buf_b buf_ofs) 0 computed_size) 
                   key_p));
    repeat (forward || entailer! || nia). 
    - 
    assert (computed_size + size <= buf_size) by (Zbool_to_Prop; eassumption).
    repeat forward.
    simpl.
    forward_if
      (PROP ()
       LOCAL (
         temp _t'5 (Vint (Int.repr computed_size)); 
         temp _t'4 (Vptr buf_b buf_ofs);
         temp _t'3 (Vint (Int.repr buf_size)); 
         temp _t'2 (Vint (Int.repr computed_size));
         temp _key key_p; temp _data data_p; 
         temp _size (Vint (Int.repr size));
         temp _keyp key_p)
       SEP (data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) data_p;
            memory_block Tsh computed_size (Vptr buf_b buf_ofs);
              data_at Tsh 
                      (tarray tuchar size) (map Vint data) 
                      (Vptr buf_b (Ptrofs.add buf_ofs
                                              (Ptrofs.repr computed_size)));
              memory_block Tsh (buf_size - computed_size - size) 
                           (Vptr buf_b
                                 (Ptrofs.add buf_ofs
                                             (Ptrofs.repr 
                                                (computed_size + size))));
              data_at Tsh enc_key_s 
                      (mk_enc_key (Vptr buf_b buf_ofs)
                                  buf_size (computed_size + size)) key_p));
       repeat (forward || entailer! || nia). 
    (* qsh : share, psh: share, p: val, q: val, n: Z, contents: list int *)
    forward_call (Tsh, Tsh, Vptr buf_b (Ptrofs.add buf_ofs (Ptrofs.repr computed_size)), data_p,
                  size, data).
    admit.
    simpl.
    entailer!.
    entailer!.
    simpl.
    entailer!.
    (* copy of data_at data (buf + computed size) - why ? *)
    Intros.
    repeat forward.
    entailer!.
    simpl.
    entailer!.
    admit.
Admitted.

End Encoder_callback. 
