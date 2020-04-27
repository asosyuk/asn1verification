Require Import Core.Core Core.Tactics.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Clight.asn_application Lib.Stdlib.
Require Import Core.Notations.

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
          if buf_size <? computed_size + size 
          then emp
          else memory_block Tsh size (Vptr buf_b (Ptrofs.add buf_ofs
                                      (Ptrofs.repr computed_size))))    
     POST [tint]
      PROP ()
      LOCAL (temp ret_temp Vzero)
      SEP (data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) data_p;
           if buf_size <? computed_size + size 
           then data_at Tsh enc_key_s 
                   (mk_enc_key (Vptr buf_b buf_ofs) 0 (computed_size + size))  
                   key_p
           else 
             (data_at Tsh (tarray tuchar size) (map Vint data) 
                      (Vptr buf_b (Ptrofs.add buf_ofs
                                              (Ptrofs.repr computed_size))) *
              data_at Tsh enc_key_s 
                      (mk_enc_key (Vptr buf_b buf_ofs)
                                  buf_size (computed_size + size)) key_p)). 

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
                         (Vptr buf_b (Ptrofs.add buf_ofs (Ptrofs.of_int computed_size))))    
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

Definition Gprog := ltac:(with_library prog [callback_overrun_spec_int; (_memcpy, memcpy_spec)]).

Theorem bool_der_encode_int : semax_body Vprog Gprog f_overrun_encoder_cb 
                                     callback_overrun_spec_int.
  Proof.
    start_function.
    destruct (buf_size <u computed_size + size)%int eqn : Q.
    - 
    repeat forward.
    forward_if 
      (PROP ()
       LOCAL (temp _t'3 (Vint buf_size); 
              temp _t'2 (Vint computed_size);
              temp _key key_p; temp _data data_p; 
              temp _size (Vint size);
              temp _keyp key_p)
       SEP (data_at Tsh (tarray tuchar (Int.unsigned size)) (map Vint data) data_p;
            data_at Tsh enc_key_s (Vptr buf_b buf_ofs, (Vzero, Vint computed_size)) 
                   key_p));
    repeat (forward || entailer! || congruence).  
    - 
    repeat forward.
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
       SEP (data_at Tsh (tarray tuchar (Int.unsigned size)) (map Vint data) data_p;
            data_at Tsh (tarray tuchar (Int.unsigned size)) (map Vint data) 
                      (Vptr buf_b (Ptrofs.add buf_ofs
                                              (Ptrofs.of_int computed_size)));
            data_at Tsh enc_key_s (Vptr buf_b buf_ofs,
                                   (Vint buf_size, Vint (computed_size))) key_p));
       repeat (forward || entailer! || congruence).
    assert (Int.repr (Int.unsigned size) = size) as II by auto with ints.
    forward_call (Tsh, Tsh, Vptr buf_b 
                 (Ptrofs.add buf_ofs (Ptrofs.of_int computed_size)), data_p,
                 (Int.unsigned size), data);  
      auto with ints; 
      try rewrite II; entailer!.
Qed.

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

Definition Gprog2 := ltac:(with_library prog [callback_overrun_spec; (_memcpy, memcpy_spec)]).

Theorem bool_der_encode : semax_body Vprog Gprog2 f_overrun_encoder_cb 
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
            data_at Tsh enc_key_s 
                   (mk_enc_key (Vptr buf_b buf_ofs) 0 computed_size) 
                   key_p));
    repeat (forward || entailer! || nia).    
    - 
    assert (computed_size + size <= buf_size) by (Zbool_to_Prop; eassumption).
    repeat forward.
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
            data_at Tsh (tarray tuchar size) (map Vint data) 
                      (Vptr buf_b (Ptrofs.add buf_ofs
                                              (Ptrofs.repr computed_size)));
            data_at Tsh enc_key_s 
                      (mk_enc_key (Vptr buf_b buf_ofs)
                                  buf_size (computed_size)) key_p));
       repeat (forward || entailer! || nia). 
    forward_call (Tsh, Tsh, Vptr buf_b (Ptrofs.add buf_ofs (Ptrofs.repr computed_size)), data_p,
                  size, data); entailer!.
    entailer!.
Qed.

End Encoder_callback. 
