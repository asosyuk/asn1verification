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
         buf_b : block, buf_ofs : ptrofs, 
         buf_size : Z, computed_size : Z
    PRE [tptr tvoid, tuint, tptr tvoid]
      PROP (size = Zlength data;
            0 <= buf_size <= Int.max_unsigned;
            0 <= computed_size <= Int.max_unsigned;
            0 <= size <= Int.max_unsigned;
            (* Implicit assumptions *)
            0 <= computed_size + size <= Int.max_unsigned;
            0 <= computed_size + size + Ptrofs.unsigned buf_ofs < Ptrofs.modulus;
            0 <= Ptrofs.unsigned buf_ofs + buf_size < Ptrofs.modulus)
      PARAMS (data_p; Vint (Int.repr size); key_p)
      GLOBALS ()
      SEP (data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) data_p;
           data_at Tsh enc_key_s 
                   (mk_enc_key (Vptr buf_b buf_ofs) buf_size computed_size)
                   key_p;
           memory_block Tsh buf_size  (Vptr buf_b buf_ofs))
     POST [tint]
      PROP ()
      LOCAL (temp ret_temp Vzero)
      SEP (data_at Tsh (tarray tuchar (Zlength data)) (map Vint data) data_p;
           if buf_size <? computed_size + size 
           then 
             (data_at Tsh enc_key_s
                      (mk_enc_key 
                         (Vptr buf_b buf_ofs) 0 (computed_size + size)) key_p *
                memory_block Tsh buf_size (Vptr buf_b buf_ofs))
           else 
             (memory_block Tsh computed_size (Vptr buf_b buf_ofs) *
              data_at Tsh (tarray tuchar size) (map Vint data) 
                      (offset_val computed_size (Vptr buf_b buf_ofs)) * 
              memory_block Tsh (buf_size - computed_size - len data)
                           (offset_val (computed_size + len data) 
                                       (Vptr buf_b buf_ofs)) *
              data_at Tsh enc_key_s 
                      (mk_enc_key  (Vptr buf_b buf_ofs) buf_size 
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
  remember  (Vptr buf_b buf_ofs) as buf_p.
  destruct (buf_size <? computed_size + size) eqn:S.
  - repeat forward. 
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
                    (mk_enc_key buf_p 0 computed_size) key_p;
      memory_block Tsh buf_size buf_p));
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
                         (mk_enc_key buf_p buf_size (computed_size)) key_p; 
       (memory_block Tsh computed_size buf_p) ;
                memory_block Tsh (buf_size - computed_size - len data)
                             (offset_val (computed_size + len data) buf_p))) ;
      repeat (forward || entailer! || nia). 
    forward_call (Tsh, Tsh, offset_val computed_size buf_p, data_p, size, data);
      entailer!.
    cbn; entailer!.
    replace buf_size with ((computed_size + len data)
                           + (buf_size - computed_size - len data)) at 1 by nia.
    unfold offset_val.
    replace buf_ofs with (Ptrofs.repr (Ptrofs.unsigned buf_ofs)).
    erewrite memory_block_split.
    erewrite memory_block_split.
    entailer!.
    all: try nia; rep_omega_setup;
    try rep_omega.
    rewrite Ptrofs.repr_unsigned; auto.
    cbn; entailer!.
Qed.
