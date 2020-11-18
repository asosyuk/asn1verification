Require Import Core.Core Core.VstTactics Core.StructNormalizer VstLib
        ErrorWithWriter.
Require Import Core.Tactics 
        VST.floyd.proofauto Clight.der_encoder
        Core.Notations Core.SepLemmas.
Require Import Clight.dummy Lib.Callback.Dummy Exec.Der_write_TL_m.
Require Import Ber_tlv_length_serialize
        Ber_tlv_tag_serialize.
Require Import 
        Exec.Ber_tlv_length_serialize Exec.Ber_tlv_tag_serialize Types.

Definition composites :=
  composites ++ (match find_cs dummy._dummy dummy.composites with
                 | Some r => [r]
                 | None => []
                 end) ++ (match find_cs dummy._application_specific_key dummy.composites with
                 | Some r => [r]
                 | None => []
                 end) .

Definition Vprog : varspecs. 
Proof.
  set (cs := composites).
  set (gd := global_definitions).
  set (pi := public_idents).
  unfold composites in cs.
  simpl in cs.
  set (prog := Clightdefs.mkprogram cs gd pi _main Logic.I).
  mk_varspecs prog. 
Defined.

Instance CompSpecs : compspecs. 
Proof.
  set (cs := composites).
  set (gd := global_definitions).
  set (pi := public_idents).
  unfold composites in cs.
  simpl in cs.
  set (prog := Clightdefs.mkprogram cs gd pi _main Logic.I).
  make_compspecs prog.
Defined.

Instance Change1 : change_composite_env Callback.Dummy.CompSpecs CompSpecs.
Proof. make_cs_preserve Dummy.CompSpecs CompSpecs. Defined.

Instance Change2 : change_composite_env CompSpecs Dummy.CompSpecs.
Proof. make_cs_preserve CompSpecs Dummy.CompSpecs. Defined.

Instance Change3 : change_composite_env CompSpecs VST.Ber_tlv_tag_serialize.CompSpecs.
Proof. make_cs_preserve CompSpecs  Ber_tlv_tag_serialize.CompSpecs. Defined.

Instance Change4 : change_composite_env  Ber_tlv_tag_serialize.CompSpecs CompSpecs.
Proof. make_cs_preserve  Ber_tlv_tag_serialize.CompSpecs CompSpecs. Defined.

Instance Change5 : change_composite_env CompSpecs  Ber_tlv_length_serialize.CompSpecs.
Proof. make_cs_preserve CompSpecs Ber_tlv_length_serialize.CompSpecs. Defined.

Instance Change6 : change_composite_env Ber_tlv_length_serialize.CompSpecs CompSpecs.
Proof. make_cs_preserve  Ber_tlv_length_serialize.CompSpecs CompSpecs. Defined.

Definition der_write_TL_spec : ident * funspec :=
  DECLARE _der_write_TL
  WITH tag : int, l : int, 
       cb : val, app_key : val, constructed : int, init : list int
  PRE[tuint, tint, tptr cb_type, tptr tvoid, tint]
    PROP(constructed = 0%int)
    PARAMS(Vint tag; Vint l; cb; app_key; Vint constructed)
    GLOBALS()
    SEP(if Val.eq cb nullval 
        then emp
        else (func_ptr' dummy_callback_spec cb *
              data_at_ Tsh enc_key_s app_key);
              valid_pointer cb)
  POST[tint]
    let size := if Val.eq cb nullval then 0 else 32 in
    PROP() 
    LOCAL(temp ret_temp
               (Vint (Int.repr
              (match evalErrW (der_write_TL_m tag l size constructed) init with
                | Some v => match v with encode v => v end
                | None => -1
              end))))
    SEP(if Val.eq cb nullval 
        then emp
        else (func_ptr' dummy_callback_spec cb *
              data_at_ Tsh enc_key_s app_key);
              valid_pointer cb).

Definition Gprog := ltac:(with_library prog [der_write_TL_spec;
                                             ber_tlv_tag_serialize_spec; 
                                             der_tlv_length_serialize_spec;
                                             (_cb, dummy_callback_spec)]).

Open Scope Z.


Theorem der_write_TL_serialize_correct: 
  semax_body Vprog Gprog (normalize_function f_der_write_TL composites)
             der_write_TL_spec.
Proof.
  function_pointers.
  start_function.
  pose proof (tag_serialize_bounds tag (Int.repr 32)) as BT.
  pose proof
       (length_serialize_bounds l
       (Int.repr (32 - snd ((tag_serialize tag (Int.repr 32)))))) as BL.
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
         temp _tag (Vint tag); temp _len (Vint l);
         temp _cb cb; temp _app_key app_key;
         temp _constructed (Vint constructed))
  SEP (data_at_ Tsh (tarray tuchar 32) v_buf;   
       if Val.eq cb nullval 
       then emp
       else (data_at_ Tsh enc_key_s app_key *
            func_ptr' dummy_callback_spec cb) ; valid_pointer cb)).
  - forward.
    unfold isptr in H.
    repeat break_match; try contradiction.
    entailer!.
    entailer!.
    edestruct HPv_buf.    
    subst.
    cbv. auto.
  - forward.
    entailer!.
    edestruct HPv_buf.    
    subst.
    cbv. auto.
    repeat rewrite_if_b. auto.
  - repeat forward.
    unfold isptr in *.
    destruct v_buf; try contradiction.
    cbn in H.
    break_if.
    (* cb = nullval *)
    + (* destruct (tag_serialize tag (Int.repr (0))) as [tl zt] eqn : TS. *)
       assert (0 <= (snd (tag_serialize tag (Int.repr 0))) <= 32) as T.
      { unfold tag_serialize.
        pose proof (req_size_32 (tag >>u Int.repr 2)).
        repeat break_if; simpl; try lia. }
      destruct (tag_serialize tag (Int.repr (0))) as [tl zt] eqn : TS. 
      destruct (length_serialize l (Int.repr (0))) as [ll zl] eqn : LS. 
      assert ((snd (length_serialize l (Int.repr (0)))) = zl) as SLS
          by (unfold snd; break_let; inversion LS; auto).
      assert ((snd (tag_serialize tag (Int.repr 0)) = zt)) as TLS
          by (unfold snd; break_let; inversion TS; auto).
       assert ((fst (tag_serialize tag (Int.repr 0)) = tl)) as TLL
          by (unfold fst; break_let; inversion TS; auto).
       assert ((fst (length_serialize l (Int.repr (0)))) = ll) as LLL
           by (unfold fst; break_let; inversion LS; auto).
      pose proof (length_serialize_bounds l (Int.repr (0))) as L.
      pose proof (tag_serialize_bounds tag (Int.repr 0)) as TL.
      pose proof (req_size_32 (tag >>u Int.repr 2)) as R.
       pose proof (Ber_tlv_length_serialize.req_size_32 (l)) as RR.
       assert ((fst (tag_serialize tag (Int.repr 0)) = [])) as TLE.
       { unfold tag_serialize.
         repeat break_if; try contradiction; auto.
         Zbool_to_Prop. generalize Heqb1. strip_repr.
         intro. lia. }
        assert ((fst (length_serialize l (Int.repr 0)) = [])) as LLE.
       { unfold length_serialize.
         repeat break_if; try contradiction; auto.
         Zbool_to_Prop. generalize Heqb1. strip_repr.
         intro. lia. }
       erewrite TLE in *.
       erewrite <- TLL in *.
       simpl in T.
      forward_call (tag, b, i, 0%Z).
      unfold Frame.
      instantiate (1 := [(data_at_ Tsh (tarray tuchar 32) 
                                   (Vptr b i) * emp * valid_pointer cb)%logic]).
      simpl.
      erewrite data_at_zero_array_eq; auto.
      entailer!.      
      repeat split; try rep_omega.
      forward_if. lia.
      Intros.
      forward.
      forward_if (temp _t'3 Vzero). congruence.
      forward.
      erewrite TS. clear H2.
      unfold snd, fst.
      entailer!.
      erewrite TS.  unfold snd, fst.
      autorewrite with sublist.
      forward_call (l, b, (i + Ptrofs.repr zt)%ptrofs, 0).
      entailer!.
      unfold Frame.
      instantiate (1 := [(data_at_ Tsh (tarray tuchar 32) 
                                   (Vptr b i) * emp * valid_pointer cb)%logic]).
      simpl.
      erewrite data_at_zero_array_eq; auto.
      rewrite data_at_zero_array_eq; auto.
      entailer!.      
      split; auto. strip_repr.
      erewrite LS. unfold snd, fst.
      autorewrite with sublist.
      strip_repr.
      Intros.
      repeat forward.
      forward_if. lia.
      forward_if (PROP ( )
     LOCAL (temp der_encoder._size (Vint (Int.repr zt + Int.repr zl)%int);
     temp _tmp (Vint (Int.repr zl)); temp _t'4 (Vint (Int.repr zl)); 
     temp _t'3 Vzero; temp _buf_size Vzero; temp der_encoder._t'1 Vzero;
     lvar _buf (tarray tuchar 32) (Vptr b i); temp _tag (Vint tag); temp _len (Vint l);
     temp _cb cb; temp _app_key app_key; temp _constructed (Vint constructed))
     SEP (data_at Tsh (tarray tuchar 0)
            (map Vint ll ++ sublist (len ll) 0 (default_val (tarray tuchar 0)))
            (Vptr b (i + Ptrofs.repr zt)%ptrofs); data_at_ Tsh (tarray tuchar 32) (Vptr b i);
     valid_pointer cb)).
     subst.
     contradiction.
     forward.
     entailer!.
     forward.
     entailer!.
     { do 2 f_equal.
       unfold evalErrW.
       cbn.
       erewrite TS.
       erewrite LS.
       simpl.
       replace ((32 <? snd (tag_serialize tag (Int.repr 0)))
           || (32 <? snd (tag_serialize tag (Int.repr 0)) +
                    snd (length_serialize l (Int.repr 0))))%bool with false. auto.
       symmetry.
       eapply orb_false_intro; Zbool_to_Prop; try lia. }
      repeat  erewrite data_at_zero_array_eq; auto.
       erewrite LLE.
       autorewrite with sublist.
       auto.
    + (* cb <> nullval *)
    (*  destruct (der_write_TL_m tag l 32 constructed []) as [ls z] eqn : DWT.
      assert (fst (der_write_TL tag l 32 constructed) = ls) as FDWT by
             (unfold fst; break_let; inversion DWT; auto).
      assert (snd (der_write_TL tag l 32 constructed) = z) as SDWT by
             (unfold snd; break_let; inversion DWT; auto). *)
      destruct (tag_serialize tag (Int.repr (32))) as [tl zt] eqn : TS. 
      destruct (length_serialize l (Int.repr (32 - zt))) as [ll zl] eqn : LS. 
      assert ((snd (length_serialize l (Int.repr (32 - zt)))) = zl) as SLS
          by (unfold snd; break_let; inversion LS; auto).
      assert ((snd (tag_serialize tag (Int.repr 32)) = zt)) as TLS
          by (unfold snd; break_let; inversion TS; auto).
       assert ((fst (tag_serialize tag (Int.repr 32)) = tl)) as TLL
          by (unfold fst; break_let; inversion TS; auto).
       assert ((fst (length_serialize l (Int.repr (32 - zt)))) = ll) as LLL
           by (unfold fst; break_let; inversion LS; auto).
      pose proof (length_serialize_bounds l (Int.repr (32 - zt))) as L.
      pose proof (tag_serialize_bounds tag (Int.repr 32)) as TL. 
     forward_call (tag, b, i, 32).
     assert (0 <= zt <= 32) as T.
      { subst. unfold tag_serialize.
        pose proof (req_size_32 (tag >>u Int.repr 2)).
        repeat break_if; simpl; try lia. }
      forward_if. lia.
      Intros.
      forward.
     forward_if ((temp _t'3 
                       (Vint (Int.repr 
                                (32 -  (snd (tag_serialize tag (Int.repr 32))))))%int)).
     forward.
     entailer!.
     discriminate.
     erewrite TS.
     forward_call (l, b, (i + Ptrofs.repr zt)%ptrofs, (32 - zt)).
     unfold Frame.
     instantiate (1 := [(data_at Tsh (tarray tuchar zt)
                                (map Vint tl) 
                                (Vptr b i) * 
                        data_at_ Tsh enc_key_s app_key *
                        func_ptr' dummy_callback_spec cb *
                        valid_pointer cb)%logic]).
     simpl.
     
     erewrite sepcon_comm.
     change_compspecs CompSpecs.
     erewrite <- data_at_app_gen.
     entailer!.
     auto.
     1-6: try list_solve; try lia.
     erewrite Zlength_map.
     auto
     admit.
     split. admit. (* change in length *)
     cbn in H0; ptrofs_compute_add_mul; try rep_omega.
     cbn in H0.
     Intros.
     forward.
     forward.
   (*    repeat forward.
       entailer!. 
       unfold der_write_TL.
       erewrite TS, LS.        
       rewrite BC, Z0. auto.
       erewrite LS.
       rewrite_if_b.
       erewrite sepcon_comm.
       erewrite <- data_at_app_gen.
       entailer!.
       auto.
       { subst; unfold default_val;
           simpl;
           try erewrite Zlength_list_repeat;
           try nia; auto. }
       nia.
       reflexivity.
       setoid_rewrite H4. 
       unfold default_val.
       simpl.
       erewrite Zlength_list_repeat.                   
       all: nia. } *)
       forward_if.
       break_let.
       generalize H2.
       strip_repr. intro.
       forward.
       entailer!.
       { unfold evalErrW.
         unfold der_write_TL_m.
         cbn. 
         erewrite Heqp.
         erewrite Heqp0.
         simpl.
         break_if.
         auto.
         destruct_orb_hyp.
         Zbool_to_Prop.
         lia. }
       erewrite sepcon_comm.
       erewrite Zlength_map.
       remember (len l0) as k.
       change_compspecs CompSpecs.
       erewrite <- data_at_app_gen.
       entailer!.
       1-6: admit.
       break_let.
       simpl in BT, T, H2, BL.
       
    (*          ** remember (snd (tag_serialize tag (Int.repr 32))) as z0.
          remember (snd (length_serialize l (Int.repr (32 - z0)))) as z1.
          assert (zl <> -1) as Z0.
          { eapply repr_neq_e. subst; auto. }
          unfold POSTCONDITION.
          unfold abbreviate.
          rewrite <- SDWT.
          unfold der_write_TL.
          erewrite TS, LS.
          replace ((zt =? -1) || (32 <? zt))%bool with false.              
          replace (zl =? -1) with false.
          replace (32 <? zl + zt) with true.
          rewrite_if_b.
          forward.
          entailer!.
          subst.
          erewrite sepcon_comm.
          change_compspecs CompSpecs.
          erewrite <- data_at_app_gen.
          entailer!.
          auto.
          { subst; unfold default_val;
              simpl;
              try erewrite Zlength_list_repeat;
              try nia; auto. } 
          nia.
          reflexivity.
          setoid_rewrite H5.
          setoid_rewrite H11.
          rep_omega.
          symmetry.
          Zbool_to_Prop; try rep_omega.
          rewrite Int.unsigned_repr in *; try rep_omega.
          symmetry.
          Zbool_to_Prop. nia.
          symmetry.
          eapply orb_false_intro;
            Zbool_to_Prop; try nia.            
       **
         erewrite LS.
         erewrite SLS in *.
         assert (zl <> -1) as Z0. 
         { eapply repr_neq_e. auto. }
         assert (0 < zt) as Zgt0.
         { pose proof (tag_serialize_req_size_gt0 tag (Int.repr 32)).
           erewrite TS in H3.
           nia. }             
         assert (0 < len tl) as LENTL.
         { pose proof (tag_serialize_req_size tag (Int.repr 32)).
           rewrite TS in H3.
           erewrite H3.
           all: nia. } *)
       remember z as zt.
       remember l0 as tl.
       remember l1 as ll.
       remember z0 as zl.
          forward_if
     (PROP ( )
     LOCAL (temp der_encoder._size (Vint (Int.repr zt + Int.repr (snd (ll, zl)))%int);
     temp _tmp (Vint (Int.repr (snd (ll, zl)))); temp _t'5 (Vint (Int.repr (snd (ll, zl))));
     temp _t'4 (Vint (Int.repr (32 - zt)));
     temp _t'3 (Val.of_bool (Int.repr 32 < Int.repr zt)%int);
     temp _buf_size (Vint (Int.repr 32)); temp der_encoder._t'1 (Vint (Int.repr 32));
     lvar _buf (tarray tuchar 32) (Vptr b i); temp _tag (Vint tag); temp _len (Vint l);
     temp _cb cb; temp _app_key app_key; temp _constructed (Vint constructed))
     SEP (data_at Tsh (tarray tuchar (32 - zt))
             (map Vint ll ++ sublist (len ll) (32 - zt) (default_val (tarray tuchar (32 - zt))))
             (Vptr b (i + Ptrofs.repr zt)%ptrofs);
      if Val.eq cb nullval 
      then data_at Tsh (tarray tuchar (snd (tag_serialize tag (Int.repr 32))))
       (map Vint (fst (tag_serialize tag (Int.repr 32)))) (Vptr b i)
      else  data_at Tsh (tarray tuchar (snd (tag_serialize tag (Int.repr 32))))
                        (map Vint (fst (tag_serialize tag (Int.repr 32)))) (Vptr b i)
      ;
     data_at_ Tsh enc_key_s app_key; valid_pointer cb; func_ptr' dummy_callback_spec cb))

; try congruence.          
          { forward_if 
             (PROP ( )
  LOCAL (
  temp der_encoder._size (Vint (Int.repr (len (map Vint tl)) + Int.repr (snd (ll, zl)))%int);
  temp _tmp (Vint (Int.repr (snd (ll, zl)))); 
  temp _t'4 (Vint (Int.repr (32 - len (map Vint tl))));
  temp _t'3 (Val.of_bool (Int.repr 32 < Int.repr (len (map Vint tl)))%int);
  temp _buf_size (Vint (Int.repr 32)); temp der_encoder._t'1 (Vint (Int.repr 32));
  lvar _buf (tarray tuchar 32) (Vptr b i); temp _tag (Vint tag); temp _len (Vint l); 
  temp _cb cb; temp _app_key app_key; temp _constructed (Vint constructed))
  SEP (data_at Tsh (tarray tuchar (32 - len (map Vint tl)))
         (map Vint ll ++
          sublist (len ll) (32 - len (map Vint tl))
            (default_val (tarray tuchar (32 - len (map Vint tl)))))
         (Vptr b (i + Ptrofs.repr (len (map Vint tl)))%ptrofs);
 data_at Tsh (tarray tuchar (len (map Vint tl)))
  (map Vint tl) (Vptr b i);
  data_at_ Tsh enc_key_s app_key; valid_pointer cb; func_ptr' dummy_callback_spec cb)); 
try congruence.
          
            
          (*  assert (zt = (len (map Vint tl))) as ZT.
            { symmetry. 
              pose proof (tag_serialize_req_size tag (Int.repr 32)).
              erewrite TS in H5.
              autorewrite with sublist.
              eapply H5.
              auto. }
            erewrite ZT.   *)        
            forward.
            entailer!.
           (*  repeat rewrite_if_b.
            assert (zt = (len (map Vint tl))) as ZT.
            { symmetry. 
              pose proof (tag_serialize_req_size tag (Int.repr 32)).
              erewrite TS in H4.
              autorewrite with sublist.
              eapply H4.
              auto. } 
            erewrite <- ZT.
            unfold snd. *)
            admit.
            repeat erewrite Zlength_map.
            change_compspecs CompSpecs.
            entailer!.
            forward_call ((Vptr b i), (zt + zl), app_key).
            entailer!.
            cbn.
            repeat f_equal.
            autorewrite with sublist.
            admit.
            admit.
            forward_if.
            replace (zt + zl <? 0) with false in H4.
            cbv in H4.
            congruence.
            symmetry.
            Zbool_to_Prop.
            cbn in BT, BL.
            rewrite Int.unsigned_repr in *.
            admit.
            admit.          
            forward.
            repeat rewrite_if_b.
            entailer!.
          all: admit. }
          rewrite_if_b.
          forward.
          entailer!.
          admit.
          admit.
          
 { forward_if 
             (PROP ( )
  LOCAL (temp _t'7 (Vint (Znth 0 tl));
  temp der_encoder._size (Vint (Int.repr (len (map Vint tl)) + Int.repr (snd (ll, zl)))%int);
  temp _tmp (Vint (Int.repr (snd (ll, zl)))); temp _t'5 (Vint (Int.repr (snd (ll, zl))));
  temp _t'4 (Vint (Int.repr (32 - len (map Vint tl))));
  temp _t'3 (Val.of_bool (Int.repr 32 < Int.repr (len (map Vint tl)))%int);
  temp _buf_size (Vint (Int.repr 32)); temp der_encoder._t'1 (Vint (Int.repr 32));
  lvar _buf (tarray tuchar 32) (Vptr b i); temp _tag (Vint tag); temp _len (Vint l); 
  temp _cb cb; temp _app_key app_key; temp _constructed (Vint constructed))
  SEP (data_at Tsh (tarray tuchar (32 - len (map Vint tl)))
         (map Vint ll ++
          sublist (len ll) (32 - len (map Vint tl))
            (default_val (tarray tuchar (32 - len (map Vint tl)))))
         (Vptr b (i + Ptrofs.repr (len (map Vint tl)))%ptrofs);
data_at Tsh tuchar (Vint (Int.zero_ext 8 (Znth 0 tl or Int.repr 32)%int)) (Vptr b i);
data_at Tsh (tarray tuchar (len (map Vint tl) - 1))
    (sublist 1 (len (map Vint tl)) (map Vint tl)) (Vptr b (i + Ptrofs.repr 1)%ptrofs);

  data_at_ Tsh enc_key_s app_key; valid_pointer cb; func_ptr' dummy_callback_spec cb));
     try congruence.
   erewrite TLL.
   assert (zt = (len (map Vint tl))) as ZT.
   { symmetry. 
     pose proof (tag_serialize_req_size tag (Int.repr 32)).
     erewrite TS in H5.
     autorewrite with sublist.
     eapply H5.
     auto. }
   erewrite ZT.    
   erewrite split_data_at_sublist_tuchar with (j := 1%Z).
   erewrite sublist_one with (lo := 0).
   erewrite data_at_tuchar_singleton_array_eq.
   Intros.
   forward.
   entailer!.
   { unfold tag_serialize.
     pose proof (Byte.Z_mod_modulus_range 
                   (Int.unsigned (((tag & Int.repr 3) << Int.repr 6)
                                    or (tag >>u Int.repr 2))%int)).
     break_if.
     rewrite if_false.
     cbn.
     erewrite Int.zero_ext_mod; try rep_omega.
     erewrite <- Byte.Z_mod_modulus_eq;
       rep_omega.
     discriminate.
     rewrite if_false by discriminate.
     break_if;
       cbn;
       erewrite Int.zero_ext_mod; try rep_omega;
         pose proof (Byte.Z_mod_modulus_range 
                       ( Int.unsigned (((tag & Int.repr 3) << Int.repr 6)
                                         or Int.repr 31)%int));
         erewrite <- Byte.Z_mod_modulus_eq;
         try rep_omega. }
   forward.
   rewrite <- ZT.
   repeat rewrite_if_b.
   entailer!.
   autorewrite with sublist list norm.
   autorewrite with sublist in ZT.
   rewrite ZT.
   entailer!.
   1-5: auto; autorewrite with sublist in *;
     unfold snd in *; try nia.   
   assert (zt = (len (map Vint tl))) as ZT.
   { symmetry. 
     pose proof (tag_serialize_req_size tag (Int.repr 32)).
     erewrite TS in H4.
     autorewrite with sublist.
     eapply H4.
     auto. }
   erewrite <- ZT.
   unfold snd.
   unfold POSTCONDITION.
   unfold abbreviate.
   unfold MORE_COMMANDS.
   unfold abbreviate.
   forward_call ((Vptr b i), (zt + zl), app_key).
   cbn in BT, BL.
   rep_omega.
   forward_if.
   replace (zt + zl <? 0) with false in H4.
   cbv in H4.
   congruence.
   symmetry.
   Zbool_to_Prop.
   cbn in BT, BL.
   rewrite Int.unsigned_repr in *.
   nia.
   rep_omega.
   forward.
   rewrite_if_b.
   rewrite ZT.
   entailer!. }
        --
          
          forward.
          destruct (eq_dec constructed 0%int).
          pose proof (der_write_TL_serialize_sum tag l 32) as N.             
          rewrite TS, LS in N.
          erewrite N.
          repeat rewrite_if_b.
          entailer!.
          remember (snd (tag_serialize tag (Int.repr 32))) as zt.
          remember (snd (length_serialize l (Int.repr (32 - zt)))) as zl.
          remember (fst (tag_serialize tag (Int.repr 32))) as tl.
          remember (fst (length_serialize l (Int.repr (32 - zt)))) as ll.
          assert (zl = len ll) as ZL.
          { symmetry. 
            pose proof (length_serialize_req_size l (Int.repr (32 - zt))).
            erewrite LS in *.
            auto. }
          rewrite <- ZL.
          erewrite sepcon_comm.
          erewrite <- data_at_app_gen.
          entailer!.
          all: autorewrite with sublist; try  erewrite ZL; auto; try nia.
          assert (zt = len tl) as ZT.
          { symmetry. 
            pose proof (tag_serialize_req_size tag (Int.repr (32))).
            erewrite TS in *.
            auto. }
          auto.
          autorewrite with sublist in H5.
          auto.
          erewrite Zlength_sublist_correct.
          assert (zt = len tl) as ZT.
          { symmetry. 
            pose proof (tag_serialize_req_size tag (Int.repr (32))).
            erewrite TS in *.
            auto. }
          rep_omega.
          unfold snd in *.
          nia.
          unfold tarray.
          erewrite Zlength_default_val_Tarray_tuchar; nia. 
          auto with ints.

          pose proof (der_write_TL_serialize_sum_c tag l 32) as N.             
          rewrite TS, LS in N.
          erewrite N.
          repeat rewrite_if_b.
          entailer!.
          
          remember (snd (tag_serialize tag (Int.repr 32))) as zt.
          remember (snd (length_serialize l (Int.repr (32 - zt)))) as zl.
          remember (fst (tag_serialize tag (Int.repr 32))) as tl.
          remember (fst (length_serialize l (Int.repr (32 - zt)))) as ll.

          assert (zt = len tl) as ZT.
          { symmetry. 
            pose proof (tag_serialize_req_size tag (Int.repr (32))).
            erewrite TS in *.
            auto. }
          assert (zl = len ll) as ZL.
          { symmetry. 
            pose proof (length_serialize_req_size l (Int.repr (32 - zt))).
            erewrite LS in *.
            auto. }
          rewrite <- ZL.
          erewrite sepcon_comm.
          erewrite <- data_at_tuchar_singleton_array_eq.
          erewrite sepcon_comm.
          erewrite sepcon_assoc.
          erewrite <- data_at_app_gen with (ls := Vint (Int.zero_ext 8 (Znth 0 tl or Int.repr 32)%int)
                                                      :: (sublist 1 (len tl) (map Vint tl))).
          erewrite sepcon_comm.
          erewrite <- data_at_app_gen.
          entailer!.
          all: autorewrite with sublist; try  erewrite ZL; auto; try nia.
          auto.
          autorewrite with sublist in H5.
          auto.
          erewrite Zlength_sublist_correct.
          rep_omega.
          unfold snd in *.
          nia.
          unfold tarray.
          erewrite Zlength_default_val_Tarray_tuchar; nia. }
      all: try erewrite TLL.
      assert (zt = len tl) as ZT.
      { symmetry. 
        pose proof (tag_serialize_req_size tag (Int.repr (32))).
        erewrite TS in *.
        auto. }
      auto.

      unfold tarray.
      { subst; unfold default_val;
          simpl;
          try erewrite Zlength_list_repeat;
          try nia; auto. }
      Focus 2.
      assert (zt = len tl) as ZT.
      { symmetry. 
        pose proof (tag_serialize_req_size tag (Int.repr 32)).
        erewrite TS in *.
        auto. }
      unfold default_val;
        simpl;
        try erewrite Zlength_list_repeat;
        try nia; auto.
      assert (zt = len tl) as ZT.
      { symmetry. 
        pose proof (tag_serialize_req_size tag (Int.repr 32)).
        erewrite TS in *.
        auto. }
      
      erewrite ZT.
      autorewrite with sublist list norm.
      f_equal.
      unfold default_val.
      simpl.
      erewrite <- sublist_list_repeat with (k := 32); auto; nia.
      nia.
Qed.

