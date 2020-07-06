Require Import Core.Core Core.VstTactics Core.StructNormalizer VstLib
        ErrorWithWriter.
Require Import Core.Tactics.
               
Require Import VST.floyd.proofauto.
Require Import Clight.der_encoder.
Require Import Core.Notations Core.SepLemmas.
Require Import Clight.dummy Lib.Callback.Dummy ExecBer_tlv_tag_serialize
        ExecBer_tlv_length_serialize.
Require Import VSTber_tlv_length_serialize
        VSTber_tlv_tag_serialize.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Instance Change1 : change_composite_env CompSpecs  VSTber_tlv_tag_serialize.CompSpecs.
Proof. make_cs_preserve CompSpecs  VSTber_tlv_tag_serialize.CompSpecs. Defined.

Instance Change2 : change_composite_env  VSTber_tlv_tag_serialize.CompSpecs CompSpecs.
Proof. make_cs_preserve  VSTber_tlv_tag_serialize.CompSpecs CompSpecs. Defined.

Open Scope Z.

Definition der_write_TL tag len size := 
  let (_, t) := ber_tlv_tag_serialize tag (Int.repr size) in
  let (_, l) := ber_tlv_length_serialize len (Int.repr size) in
  if ((t =? -1) || (t >? 32))%bool 
  then -1
  else if l =? -1 
       then -1 
       else let s := l + t in
            if s >? 32 
            then -1
            else s.


Lemma tag_serialize_bounds : forall t l, 0 <= snd (ber_tlv_tag_serialize t l) <= 32.
      { unfold ber_tlv_tag_serialize.
        intros.
        cbn.
        repeat break_if; autorewrite with norm; try nia. } 
Qed.
  
Definition der_write_TL_spec : ident * funspec :=
  DECLARE _der_write_TL
  WITH tag : int, len : int, cb : val, app_key : val, constructed : int
  PRE[tuint, tint, tptr cb_type, tptr tvoid, tint]
    PROP()
    PARAMS(Vint tag; Vint len; cb; app_key; Vint constructed)
    GLOBALS()
    SEP(data_at_ Tsh enc_key_s app_key;
        valid_pointer cb)
  POST[tint]
    let size := if Val.eq cb nullval then 0 else 32 in
    let r := der_write_TL tag len size in
    PROP() 
    LOCAL(temp ret_temp (Vint (Int.repr r)))
    SEP(data_at_ Tsh enc_key_s app_key;
        valid_pointer cb).

Definition Gprog := ltac:(with_library prog [der_write_TL_spec;
                         ber_tlv_tag_serialize_spec; der_tlv_length_serialize_spec]).

Open Scope Z.

Definition Z_of_val v := 
  match v with
  | Vptr b i => Ptrofs.unsigned i 
  | _ => 0
  end.

Theorem der_write_TL_serialize_correct : 
  semax_body Vprog Gprog (normalize_function f_der_write_TL composites)
             der_write_TL_spec.
Proof.
  start_function.
  forward.
  forward_if 
 (PROP (isptr v_buf;
        Z_of_val v_buf + 32 < Ptrofs.modulus)
  LOCAL (temp der_encoder._t'1 
              (if Val.eq cb nullval 
               then Vzero
               else (Vint (Int.repr (sizeof (tarray tuchar 32)))));
         temp der_encoder._size (Vint (Int.repr 0)); 
         lvar _buf (tarray tuchar 32) v_buf;
         temp _tag (Vint tag); temp _len (Vint len);
         temp _cb cb; temp _app_key app_key;
         temp _constructed (Vint constructed))
  SEP (data_at_ Tsh (tarray tuchar 32) v_buf;
       data_at_ Tsh enc_key_s app_key; valid_pointer cb)).
  - forward.
    unfold isptr in H.
    repeat break_match;
    entailer!.
    discriminate.
    edestruct HPv_buf.
    subst. cbv. auto.
  - forward.
    entailer!.
    edestruct HPv_buf.
    subst. cbv. auto.
  - repeat forward.
    unfold isptr in *.
    destruct v_buf; try contradiction.
    cbn in H.
    break_if.
    (* cb = nullval *)
    + forward_call (tag, b, i, 0%Z, 32).
      repeat split; try rep_omega.      
      remember (snd (ber_tlv_tag_serialize tag (Int.repr 0))) as z.
      forward_if ((temp _t'3 (if eq_dec (Int.repr z) (Int.repr (-1)) 
                    then Vint (Int.one)
                    else
           (force_val
         (sem_cast_i2bool
            (Val.of_bool
               (Int.repr 32 < Int.repr 
                                (snd (ber_tlv_tag_serialize tag (Int.repr 0))))%int)))))). 
      1-2: repeat forward;
           entailer!;
           rewrite_if_b;
           auto;
           break_if; entailer!. 
      assert (z = -1) as Z. 
      {  unfold ber_tlv_tag_serialize in *.
            break_if;
              rewrite_if_b; admit. (* SPEC *) }
      break_if; try congruence.
      forward_if.
      repeat forward.
      rewrite if_true.
      entailer!.
      unfold der_write_TL.
      repeat break_let.     
      cbn in Z. subst.
      do 2 f_equal.
      unfold ber_tlv_tag_serialize.
      break_if;
        rewrite_if_b;
        reflexivity.
      discriminate.
    + (* cb <> nullval *)
     pose proof (tag_serialize_bounds tag (Int.repr 32)) as TL.
     repeat forward.
     forward_call (tag, b, i, 32, 32).
     repeat split; try rep_omega.      
     remember (snd (ber_tlv_tag_serialize tag (Int.repr 32))) as z.
     forward_if ((temp _t'3 (if eq_dec (Int.repr z) (Int.repr (-1)) 
                    then Vint (Int.one)
                    else
           (force_val
         (sem_cast_i2bool
            (Val.of_bool
               (Int.repr 32 < Int.repr 
                                (snd (ber_tlv_tag_serialize tag (Int.repr 32))))%int)))))). 
      1-2: repeat forward;
           entailer!;
           rewrite_if_b;
           auto;
           break_if; entailer!. 
      rewrite if_false.
      forward_if.
      repeat forward.
      normalize in H0.
      eapply typed_true_of_bool in H0.
      clear H1.
      unfold Int.lt in H0.
      destruct zlt; try congruence.
      do 2 rewrite Int.signed_repr in l; try rep_omega.
      normalize in H0.
      eapply typed_false_of_bool in H0.
      unfold Int.lt in H0.
      destruct zlt; try congruence.
      do 2 rewrite Int.signed_repr in g; try rep_omega.
      normalize.
      rewrite if_false.
      repeat forward.
      normalize.
      forward_if (temp _t'4 (Vint (Int.repr (32 - z)))); try congruence.
      repeat forward.
      entailer!. 
      discriminate.
      forward_call (len, b, (i + Ptrofs.repr z)%ptrofs, (32 - z), (32 - z)).
      entailer!.
      normalize.
    (* unfold ber_tlv_tag_serialize.
      destruct (30 >=? Int.unsigned (tag >>u Int.repr 2)) eqn: Z.
      repeat rewrite_if_b.
      entailer!.
      admit. (* true *)
      repeat rewrite_if_b.
      entailer!.
      admit. (* true *)
      normalize.
      autorewrite with norm.
      repeat split; try rep_omega.
      rewrite Int.unsigned_repr; try rep_omega.
      (* need two buffers, each size 32 *)
      admit.
      admit. (* true *)
      repeat forward.
      forward_if.
      repeat forward.
      entailer!.
      unfold der_write_TL.
      repeat break_let.
      simpl in H0.
      inversion H0.
      cbn in H.
      cbn in H1.
      admit.
      entailer!. *)
Admitted.
   
        
