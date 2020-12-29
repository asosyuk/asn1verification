Require Import Core.Core Core.VstTactics Core.StructNormalizer VstLib
        ErrorWithWriter.
Require Import Core.Tactics 
        VST.floyd.proofauto Clight.der_encoder
        Core.Notations Core.SepLemmas.
Require Import Clight.dummy Lib.Callback.Dummy Exec.Der_write_TL_m.
Require Import VST.Ber_tlv_length_serialize
        VST.Ber_tlv_tag_serialize.
Require Import 
        Exec.Ber_tlv_length_serialize Exec.Ber_tlv_tag_serialize Types.

Definition composites :=
  composites ++ [Composite dummy._application_specific_key Struct nil noattr].

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
Proof. make_cs_preserve CompSpecs  VST.Ber_tlv_tag_serialize.CompSpecs. Defined.

Instance Change4 : change_composite_env  VST.Ber_tlv_tag_serialize.CompSpecs CompSpecs.
Proof. make_cs_preserve  VST.Ber_tlv_tag_serialize.CompSpecs CompSpecs. Defined.

Instance Change5 : change_composite_env CompSpecs  VST.Ber_tlv_length_serialize.CompSpecs.
Proof. make_cs_preserve CompSpecs VST.Ber_tlv_length_serialize.CompSpecs. Defined.

Instance Change6 : change_composite_env VST.Ber_tlv_length_serialize.CompSpecs CompSpecs.
Proof. make_cs_preserve  VST.Ber_tlv_length_serialize.CompSpecs CompSpecs. Defined.

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
              data_at_ Tsh enc_key_s app_key *
              valid_pointer cb))
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
              data_at_ Tsh enc_key_s app_key *
              valid_pointer cb)).

Definition Gprog := ltac:(with_library prog [der_write_TL_spec;
                                             ber_tlv_tag_serialize_spec; 
                                             der_tlv_length_serialize_spec;
                                             (_cb, dummy_callback_spec)]).

Open Scope Z.

Theorem der_write_TL_correctness: 
  semax_body Vprog Gprog (normalize_function f_der_write_TL composites)
             der_write_TL_spec.
Admitted.
(*
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
            func_ptr' dummy_callback_spec cb * valid_pointer cb))).
  - break_if; entailer!.
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
    + 
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
                                   (Vptr b i))%logic]).
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
                                   (Vptr b i))%logic]).
      simpl.
      erewrite data_at_zero_array_eq; auto.
      rewrite data_at_zero_array_eq; auto.
      entailer!.      
      split; auto. strip_repr.
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
            (Vptr b (i + Ptrofs.repr zt)%ptrofs); data_at_ Tsh (tarray tuchar 32) (Vptr b i))).
     subst.
     contradiction.
     erewrite LS.
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
      pose proof (req_size_32 (tag >>u Int.repr 2)) as R.
      pose proof (Ber_tlv_length_serialize.req_size_32 l) as RR.
      assert (len tl = zt) as ZT.
      { pose proof (tag_serialize_req_size tag (Int.repr 32)) as G.
        erewrite TS in G.
        eapply G.
        discriminate.
        strip_repr. } 
      cbn in H0.
      simpl in BL, BT.
      erewrite SLS in *. erewrite TLS in *.
      clear SLS TLS TLL LLL.
     forward_call (tag, b, i, 32).
     assert (0 <= zt <= 32) as T.
      { subst. unfold tag_serialize.
        
        repeat break_if; simpl; try lia. }
       assert (0 <= zl <= 32) as LL.
      { subst. unfold length_serialize.
        repeat break_if; simpl; try lia. }
      forward_if. 
       assert ((snd (tag_serialize tag (Int.repr 32)) = zt)) as TLS
          by (unfold snd; break_let; inversion TS; auto).
      erewrite TLS in *. generalize H1. strip_repr. intro. lia.
      Intros.
       assert ((snd (tag_serialize tag (Int.repr 32)) = zt)) as TLS
          by (unfold snd; break_let; inversion TS; auto).
      erewrite TLS in *. clear TLS.
      forward.
      erewrite TS.
     forward_if ((temp _t'3 
                       (Vint (Int.repr 
                                (32 -  zt)))%int)); try lia.
     forward.
     entailer!.
     discriminate.
     forward_call (l, b, (i + Ptrofs.repr zt)%ptrofs, (32 - zt)).
     unfold Frame.
     instantiate (1 := [(data_at Tsh (tarray tuchar zt)
                                (map Vint tl) 
                                (Vptr b i) * 
                        data_at_ Tsh enc_key_s app_key *
                        func_ptr' dummy_callback_spec cb *
                        valid_pointer cb)%logic]).
     simpl.
     entailer!.
     erewrite sepcon_comm.
     change_compspecs CompSpecs.
     erewrite <- data_at_app_gen.
     entailer!.
     1-6: try lia; autorewrite with sublist;
       try  erewrite Zlength_default_val; try lia.
     f_equal.
     unfold default_val.
     simpl.
     erewrite <- sublist_list_repeat with (k := 32); auto; nia.
     split. 
     lia.
     ptrofs_compute_add_mul; strip_repr.
     Intros.
     forward.
     forward.
     erewrite LS.
     forward_if. lia.
          forward_if
     (PROP ( )
     LOCAL (temp der_encoder._size (Vint (Int.repr zt + Int.repr (snd (ll, zl)))%int);
     temp _tmp (Vint (Int.repr (snd (ll, zl)))); temp _t'5 (Vzero);
     temp _t'4 (Vint (Int.repr (snd (ll, zl))));
     temp _t'3 (Vint (Int.repr (32 - zt)));
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
          unfold MORE_COMMANDS.
          unfold abbreviate.
          { forward_if 
             (PROP ( )
     LOCAL (temp der_encoder._size
              (Vint (Int.repr 0 + Int.repr zt + Int.repr (snd (ll, zl)))%int);
     temp _tmp (Vint (Int.repr (snd (ll, zl)))); temp _t'4 (Vint (Int.repr (snd (ll, zl))));
     temp _t'3 (Vint (Int.repr (32 - zt))); temp _buf_size (Vint (Int.repr 32));
     temp der_encoder._t'1 (Vint (Int.repr 32)); lvar _buf (tarray tuchar 32) (Vptr b i);
     temp _tag (Vint tag); temp _len (Vint l); temp _cb cb; temp _app_key app_key;
     temp _constructed (Vint constructed))
     SEP (data_at Tsh (tarray tuchar (32 - zt))
            (map Vint ll ++ sublist (len ll) (32 - zt) (default_val (tarray tuchar (32 - zt))))
            (Vptr b (i + Ptrofs.repr zt)%ptrofs);
     data_at Tsh (tarray tuchar zt) (map Vint tl) (Vptr b i); data_at_ Tsh enc_key_s app_key;
     func_ptr' dummy_callback_spec cb; valid_pointer cb)); 
try congruence.
            forward.
            entailer!.
            repeat erewrite Zlength_map.
            normalize.
            forward_call ((Vptr b i), (zt + zl), app_key).
            strip_repr.
            forward_if.
            replace (zt + zl <? 0) with false in H4.
            cbv in H4.
            congruence.
            symmetry.
            Zbool_to_Prop.
            cbn in BT, BL.
            lia.         
            forward.
            repeat rewrite_if_b.
            replace (zt + zl <? 0) with false by (symmetry; Zbool_to_Prop; lia).
            normalize.   
            erewrite TS.
            entailer!. }
          forward.
          rewrite_if_b.
          erewrite TS.
          entailer!.
          do 2 f_equal.
          { unfold evalErrW.
            cbn.
            erewrite TS, LS.
            replace ((32 <? len tl) || (32 <? len tl + zl))%bool with false.
            simpl.
            auto.
            symmetry.
            eapply orb_false_intro; Zbool_to_Prop; try lia.
          }
          assert (0 <= len ll <= 32 - len tl) as P.
          { pose proof 
                 (length_serialize_req_size l (Int.repr (32 - len tl))) as B.
            assert (len ll = zl).
            erewrite LS in B.
            eapply B.
            strip_repr.
            strip_repr.
            lia. }
          erewrite sepcon_comm.
          erewrite <- data_at_app_gen.
          entailer!.
           all: try lia; autorewrite with sublist;
             try  setoid_rewrite Zlength_default_val ; try lia.
           setoid_rewrite Zlength_sublist;
             try lia;
             try (unfold default_val; simpl; rewrite Zlength_list_repeat; lia).
            auto.
           setoid_rewrite Zlength_sublist; try  lia.
           unfold default_val; simpl. rewrite Zlength_list_repeat; lia.
Qed.

*)
