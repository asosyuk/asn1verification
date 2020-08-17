Require Import Core.Core Core.Tactics.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Clight.asn_application.
Require Import Lib.VstLib Lib.Stdlib.
Require Import Core.Notations.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Definition callback_int  : funspec :=
    WITH data : list int, data_p : val, 
         size : int,
         key : val, key_p : val, 
         buf_b : block, buf_ofs : ptrofs,
         buf_size : int, computed_size : int
    PRE [tptr tvoid, tuint, tptr tvoid]
      PROP ()
      PARAMS (data_p; Vint size; key_p)
      GLOBALS ()
      SEP 
      (data_at Tsh (tarray tuchar (Int.unsigned size)) (map Vint data) data_p;
       data_at Tsh enc_key_s 
               (Vptr buf_b buf_ofs, (Vint buf_size, Vint computed_size)) key_p;
       if (buf_size <u computed_size + size)%int 
       then emp
       else memory_block Tsh (Int.unsigned size)
                         (Vptr buf_b (Ptrofs.add buf_ofs 
                                                 (Ptrofs.of_int computed_size))))
      POST [tint]
      PROP ()
      LOCAL (temp ret_temp Vzero)
      SEP (data_at Tsh (tarray tuchar (Int.unsigned size)) (map Vint data) data_p;
           if (buf_size <u computed_size + size)%int 
           then data_at Tsh enc_key_s 
                   (Vptr buf_b buf_ofs, (Vzero, Vint (computed_size + size))%int)  
                   key_p
           else 
             (data_at Tsh (tarray tuchar (Int.unsigned size)) (map Vint data) 
                      (Vptr buf_b (Ptrofs.add
                                     buf_ofs
                                     (Ptrofs.of_int computed_size))) *
              data_at Tsh enc_key_s ((Vptr buf_b buf_ofs), 
                                     (Vint buf_size, 
                                     Vint (computed_size + size)%int)) key_p)). 

Definition callback_overrun_spec_int : ident * funspec :=
  DECLARE _overrun_encoder_cb callback_int.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition Gprog := ltac:(with_library prog [callback_overrun_spec_int; 
                                            (_memcpy, memcpy_spec)]).

Theorem bool_der_encode_int : semax_body Vprog Gprog f_overrun_encoder_cb 
                                     callback_overrun_spec_int.
Proof.
  start_function.
  destruct (buf_size <u computed_size + size)%int eqn : Q.
  - repeat forward.
    forward_if 
      (PROP ()
            LOCAL (temp _t'3 (Vint buf_size); 
                   temp _t'2 (Vint computed_size);
                   temp _key key_p; temp _data data_p; 
                   temp _size (Vint size);
                   temp _keyp key_p)
            SEP (data_at Tsh (tarray tuchar (Int.unsigned size)) (map Vint data) 
                         data_p;
                 data_at Tsh enc_key_s (Vptr buf_b buf_ofs, (Vzero, Vint computed_size)) 
                         key_p));
      repeat (forward || entailer! || congruence).  
  - repeat forward.
    forward_if
      (PROP ()
            LOCAL (
              temp _t'5 (Vint computed_size); 
              temp _t'4 (Vptr buf_b buf_ofs);
              temp _t'3 (Vint buf_size); 
              temp _t'2 (Vint computed_size);
              temp _key key_p; temp _data data_p; 
              temp _size (Vint size);
              temp _keyp key_p)
            SEP (data_at Tsh (tarray tuchar (Int.unsigned size)) (map Vint data) 
                         data_p;
                 data_at Tsh (tarray tuchar (Int.unsigned size)) (map Vint data) 
                         (Vptr buf_b (Ptrofs.add buf_ofs
                                                 (Ptrofs.of_int computed_size)));
                 data_at Tsh enc_key_s (Vptr buf_b buf_ofs,
                                        (Vint buf_size, Vint (computed_size))) key_p));
      repeat (forward || entailer! || congruence).
    assert (Int.repr (Int.unsigned size) = size) as II by auto with ints.
    forward_call (Tsh, Tsh, Vptr buf_b 
                                 (Ptrofs.add buf_ofs 
                                             (Ptrofs.of_int computed_size)), 
                  data_p, (Int.unsigned size), data);  
      auto with ints; 
      try rewrite II; entailer!.
Qed.
