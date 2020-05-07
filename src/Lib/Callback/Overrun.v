Require Import Core.Core Core.Tactics.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Clight.asn_application.
Require Import Lib.VstLib Lib.Stdlib.
Require Import Core.Notations.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Definition callback  : funspec :=
    WITH (* parameters *)
         data : list int, data_p : val, 
         size : Z,
         key_p : val, 
         (* overrun_encoder_key fields *)
         buf_p : val,
         buf_size : Z, computed_size : Z
    PRE [tptr tvoid, tuint, tptr tvoid]
      PROP (size = Zlength data;
            0 <= buf_size <= Int.max_unsigned;
            0 <= computed_size <= Int.max_unsigned;
            0 <= size <= Int.max_unsigned;
            0 <= computed_size + size <= Int.max_unsigned;
            isptr buf_p;
            if buf_size <? computed_size + size 
            then buf_size = 0 else True)
      PARAMS (data_p; Vint (Int.repr size); key_p)
      GLOBALS ()
      SEP (data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) data_p;
           data_at Tsh enc_key_s 
                   (mk_enc_key buf_p buf_size computed_size)
                   key_p;
          if buf_size <? computed_size + size
          then emp
          else memory_block Tsh size (offset_val computed_size buf_p))
     POST [tint]
      PROP ()
      LOCAL (temp ret_temp Vzero)
      SEP (data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) data_p;
           if buf_size <? computed_size + size 
           then data_at Tsh enc_key_s (mk_enc_key buf_p 0
                                                  (computed_size + size)) key_p
           else (data_at Tsh (tarray tuchar size) (map Vint data) 
                         (offset_val computed_size buf_p) * 
                 data_at Tsh enc_key_s (mk_enc_key buf_p buf_size 
                                                   (computed_size + size)) key_p)). 

Definition callback_overrun_spec : ident * funspec :=
  DECLARE _overrun_encoder_cb callback.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition Gprog := ltac:(with_library prog [callback_overrun_spec; 
                                             (_memcpy, memcpy_spec)]).

Theorem bool_der_encode : semax_body Vprog Gprog f_overrun_encoder_cb 
                                     callback_overrun_spec.
Proof.
  start_function.
  destruct (buf_size <? computed_size + size) eqn:S.
  - repeat forward. 
    assert (buf_size < computed_size + size) by (Zbool_to_Prop; eassumption).
    forward_if 
      (PROP ()
       LOCAL (temp _t'3 (Vint (Int.repr 0)); 
              temp _t'2 (Vint (Int.repr computed_size));
              temp _key key_p; temp _data data_p; 
              temp _size (Vint (Int.repr size));
              temp _keyp key_p)
       SEP (data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) data_p;
            data_at Tsh enc_key_s 
                    (mk_enc_key buf_p 0 computed_size) key_p));
      repeat (forward || entailer! || nia).    
  - assert (computed_size + size <= buf_size) by (Zbool_to_Prop; eassumption).
    repeat forward.
    unfold mk_enc_key.
    forward_if
      (PROP ()
            LOCAL (
              temp _t'5 (Vint (Int.repr computed_size)); 
              temp _t'4 buf_p;
              temp _t'3 (Vint (Int.repr buf_size)); 
              temp _t'2 (Vint (Int.repr computed_size));
              temp _key key_p; temp _data data_p; 
              temp _size (Vint (Int.repr size));
              temp _keyp key_p)
            SEP (data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) data_p;
                 data_at Tsh (tarray tuchar size) (map Vint data) 
                         (offset_val computed_size buf_p);
                 data_at Tsh enc_key_s 
                         (mk_enc_key buf_p buf_size (computed_size)) key_p));
      repeat (forward || entailer! || nia). 
    forward_call (Tsh, Tsh, offset_val computed_size buf_p, data_p, size, data);
      entailer!.
    cbn; entailer!.
Qed.
