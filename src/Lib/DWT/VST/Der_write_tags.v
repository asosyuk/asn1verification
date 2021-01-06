Require Import Core.Core Core.StructNormalizer VstLib Exec.Der_write_tags 
        ErrorWithWriter Clight.dummy Callback.Dummy.
Require Import VST.floyd.proofauto.
Require Import VstTactics.
Require Import Core.Tactics Core.Notations Core.SepLemmas.
Require Import VST.Der_write_TL Types. 
Require Import Clight.der_encoder.

Definition Vprog : varspecs. 
Proof.
  mk_varspecs prog. 
Defined.

Instance CompSpecs : compspecs. 
Proof.
  make_compspecs prog.
Defined.

Instance Change1 : change_composite_env Callback.Dummy.CompSpecs CompSpecs.
Proof. make_cs_preserve Dummy.CompSpecs CompSpecs. Defined.

Instance Change2 : change_composite_env CompSpecs Dummy.CompSpecs.
Proof. make_cs_preserve CompSpecs Dummy.CompSpecs. Defined.

Instance Change4 : change_composite_env CompSpecs Der_write_TL.CompSpecs.
Proof. make_cs_preserve CompSpecs Der_write_TL.CompSpecs. Defined.


Instance Change3 : change_composite_env Der_write_TL.CompSpecs CompSpecs.
Proof. make_cs_preserve Der_write_TL.CompSpecs CompSpecs. Defined.


Open Scope Z.

Section Der_write_tags.
     
Definition der_write_tags_spec : ident * funspec :=
  DECLARE _der_write_tags
  WITH td_p : val, td : TYPE_descriptor,
       struct_len: Z, tag_mode : Z, last_tag_form : Z, 
       cb : val, app_key : val,
       tags_p : val
  PRE[tptr type_descriptor_s, tuint, tint, tint, tuint, 
      tptr cb_type, tptr tvoid]
  PROP(tag_mode = 0;
         last_tag_form = 0;
         1 = len (tags td); (* primitive tag *)
         isptr tags_p;
         0 <= len (tags td) + 1 <= 16) 
  PARAMS(td_p; Vint (Int.repr struct_len); Vint (Int.repr tag_mode);
           Vint (Int.repr last_tag_form); Vint (Int.repr 0); cb; app_key)
  GLOBALS()
  SEP(field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) 
               [StructField _tags] 
               tags_p td_p;
        field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) 
                 [StructField _tags_count] 
                 (Vint (Int.repr (len (tags td)))) td_p;
        data_at Tsh (tarray tuint (len (tags td)))
                (map Vint (map Int.repr (tags td))) tags_p;
        func_ptr' dummy_callback_spec cb;
        data_at_ Tsh tuint app_key;
        valid_pointer cb)
  POST[tint]
  let size := if Val.eq cb nullval then 0 else 32 in
  PROP()
      LOCAL(temp ret_temp 
                 (Vint (Int.repr 
                          (match evalErrW 
                                   (der_write_tags td struct_len tag_mode
                                                   last_tag_form 0 size) [] with
                           | Some w => encoded w
                           | None => -1
                           end))))
      SEP(field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) 
                   [StructField _tags] 
                   tags_p td_p;
            field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) 
                     [StructField _tags_count] 
                     (Vint (Int.repr (Zlength (tags td)))) td_p;
            data_at Tsh (tarray tuint (len (tags td))) 
                    (map Vint (map Int.repr (tags td))) tags_p;
            func_ptr' dummy_callback_spec cb;
            data_at_ Tsh tuint app_key;
            valid_pointer cb).


Definition Gprog := ltac:(with_library prog [der_write_tags_spec;
                                             der_write_TL_spec]).

Theorem der_write_tags_correctness : semax_body Vprog Gprog 
                                     (normalize_function 
                                        f_der_write_tags composites)
                                     der_write_tags_spec.
Admitted.
(* Proof.
  start_function.
  change_compspecs Der_write_TL.CompSpecs.
  forward.
  forward_if True.
  forward.
  entailer!.
  forward.
  entailer!.
  forward_if (
       PROP ( )
  LOCAL (temp _tags_count (Vint (Int.repr (len (tags td)))); 
         temp _tags tags_p;
         temp _t'17 (Vint (Int.repr (len (tags td)))); 
         lvar _lens (tarray tint 16) v_lens;
         lvar _tags_buf_scratch (tarray tuint 16) v_tags_buf_scratch; 
         temp _sd td_p;
         temp _struct_length (Vint (Int.repr struct_len));
         temp _tag_mode (Vint (Int.repr tag_mode));
         temp _last_tag_form (Vint (Int.repr last_tag_form));
         temp _tag (Vint (Int.repr tag));
         temp _cb cb; temp _app_key app_key)
  SEP (data_at_ Tsh (tarray tint 16) v_lens; 
       data_at_ Tsh (tarray tuint 16) v_tags_buf_scratch; 
       field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p;
       field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
                (Vint (Int.repr (len (tags td)))) td_p;
       data_at Tsh (tarray tuint (len (tags td)))
               (map Vint (map Int.repr (tags td))) tags_p;
       func_ptr' dummy_callback_spec cb; data_at_ Tsh tuint app_key; 
       valid_pointer cb)).
  congruence.
  forward.
  forward.
  entailer!.
  forward_if.
  lia.
  forward.
  Require Import Exec.Der_write_TL_m.
  remember (tags td) as ts.
  remember (len ts) as tags_count.
  forward_loop (
  EX j : Z, EX overall_length : Z, EX lens : list Z,
  PROP (exists ls, der_write_tags_loop1 (sublist (tags_count - j) 
                                            tags_count ts) struct_len [] [] 
              = inr (ls, (lens, encode overall_length));
       len lens = j;
       j <= tags_count)
  LOCAL (
  temp _tags tags_p;  
  temp _i (Vint (Int.repr tags_count - Int.repr j - 1)%int);
  temp _overall_length (Vint (Int.repr overall_length));
  temp _tags_count (Vint (Int.repr tags_count));
  temp _t'17 (Vint (Int.repr tags_count));
  lvar _lens (tarray tint 16) v_lens;
  lvar _tags_buf_scratch (tarray tuint 16) v_tags_buf_scratch; 
  temp _sd td_p;
  temp _struct_length (Vint (Int.repr struct_len)); 
  temp _tag_mode (Vint (Int.repr tag_mode));
  temp _last_tag_form (Vint (Int.repr last_tag_form)); 
  temp _tag (Vint (Int.repr tag));
  temp _cb cb; temp _app_key app_key)
  SEP (data_at Tsh (tarray tint 16)
                (default_val (tarray tint (tags_count - len lens)) ++ 
                 map Vint (map Int.repr lens) ++ 
                 (default_val (tarray tint (16 - (tags_count))))) 
               v_lens; 
   data_at_ Tsh (tarray tuint 16) v_tags_buf_scratch; 
   field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p;
   field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
                (Vint (Int.repr (len (tags td)))) td_p;
  data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
  func_ptr' dummy_callback_spec cb;
  data_at_ Tsh tuint app_key;
  valid_pointer cb))%assert 

 break:
  (EX lens : list Z, EX overall_length : Z, EX j : Z,
  PROP (j < 0;
        exists ls, der_write_tags_loop1 ts struct_len [] [] 
              = inr (ls, (lens, encode overall_length));
       len lens = len (tags td))
  LOCAL (temp _tags tags_p;
  temp _i (Vint (Int.repr j));
  temp _overall_length (Vint (Int.repr overall_length)); (* changed *)
  temp _tags_count (Vint (Int.repr tags_count));
  temp _t'17 (Vint (Int.repr tags_count));
  lvar _lens (tarray tint 16) v_lens; 
  lvar _tags_buf_scratch (tarray tuint 16) v_tags_buf_scratch;
  temp _sd td_p;
  temp _struct_length (Vint (Int.repr struct_len)); 
  temp _tag_mode (Vint (Int.repr tag_mode));
  temp _last_tag_form (Vint (Int.repr last_tag_form)); 
  temp _tag (Vint (Int.repr tag));
  temp _cb cb; temp _app_key app_key)
  SEP (data_at Tsh (tarray tint 16)
               (default_val (tarray tint (len (tags td) - len lens)) ++
                            map Vint (map Int.repr lens)
                            ++ default_val (tarray tint (16 - len (tags td))))
               v_lens;
       data_at_ Tsh (tarray tuint 16) v_tags_buf_scratch; 
       field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p;
       field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
                (Vint (Int.repr (len (tags td)))) td_p;
       data_at Tsh (tarray tuint (len (tags td)))
               (map Vint (map Int.repr (tags td))) tags_p;
       func_ptr' dummy_callback_spec cb;
       data_at_ Tsh tuint app_key;
       valid_pointer cb))%assert.
  + forward.    
    Exists 0 struct_len (@nil Z).
    autorewrite with sublist.
    entailer!.
    repeat split.
    eexists. cbn. auto.
    strip_repr.
    repeat erewrite default_val_app.
    replace (len (tags td) + (16 - len (tags td))) with 16 by list_solve.
    entailer!.
  + Intros j overall_length lens.
    forward_if.
    assert (len (tags td) - len lens - 1 >= 0) as JJ.
    { generalize H8.
    strip_repr. intro. subst. list_solve. }
     assert ((0 <= Int.unsigned (Int.repr (len (tags td) - j) - 1)%int 
             < len (map Int.repr (tags td)))) as TJ.
    { subst.
      erewrite Zlength_map.
      strip_repr. }
(*    assert (tags_count - j - 1 >= 0) as TJ. 
    { generalize H8; strip_repr;
        subst;
        repeat break_if; strip_repr. } *)
    assert ((0 <= Int.unsigned (Int.repr (tags_count - j) - 1)%int 
             < len ((tags td)))) as TJ'.
    { try erewrite Zlength_map; subst; strip_repr. }
    forward.
    strip_repr.
    remember (Int.repr (Znth (tags_count - j - 1) ((ts)))) as fi.
    destruct H5 as [ls Loop].
    forward_call (fi, Int.repr overall_length, nullval, nullval, Int.zero, ls).
    entailer!. 
    rewrite_if_b.
    unfold Frame.
    instantiate
    (1 :=
       [(data_at Tsh (tarray tint 16)
     (default_val (tarray tint (tags_count - len lens)) ++
      map Vint (map Int.repr lens) ++ default_val (tarray tint (16 - tags_count))) v_lens *
   data_at_ Tsh (tarray tuint 16) v_tags_buf_scratch *
   field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p *
   field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
     (Vint (Int.repr (len (tags td)))) td_p *
   data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p *
   func_ptr' dummy_callback_spec cb * data_at_ Tsh tuint app_key * 
   valid_pointer cb)%logic]).
    unfold fold_right_sepcon.
    entailer!.
    repeat rewrite_if_b.
    Intros.
    forward.
    entailer!.
    forward.
    entailer!.
    entailer!.
    erewrite upd_Znth_same.
    cbn. auto.
    unfold default_val; cbn; try nia.
    autorewrite with sublist.
    list_solve.
    erewrite upd_Znth_same.
    repeat rewrite_if_b.
    forward_if.
  { forward.
    entailer!.
    Require Import Exec.Der_write_tags.
    { (* return - 1 *)
      remember (tags td) as ts.    
      assert (exists e, der_write_TL_m
                   (Int.repr (Znth (len (tags td) - len lens - 1) 
                         ((tags td))))
                   (Int.repr overall_length) 0 0%int ls = inl e) as E.
    { Require Import Der_write_tags_lemmas.
      eapply eval_DWT_opt_to_Z.
      erewrite Heqts in *.
      setoid_rewrite H5. auto. }
    destruct E as [err E].    
    unfold der_write_tags.
    assert (exists k, der_write_tags_loop1 (tags td) struct_len [] [] = inl k) as EEE.
    { erewrite Heqts in *. 
      exists err.
      eapply write_TL_to_loop1_sublist with (j := len lens); (* QED *)
      try list_solve;
      eassumption.
      }
    destruct EEE as [k EEE].
    unfold evalErrW.
    cbn. 
    break_if; auto.
    break_match; auto.
    generalize Heqo.
    break_if.
    generalize Heqb0.
    Zbool_to_Prop.
    intro.
    pose proof (Zlength_nonneg (tags td)).
    nia.
    rewrite H5 in *.
    erewrite EEE.
    congruence. }
  }
    abbreviate_semax.
    deadvars!.
    forward.  
    entailer!.
    entailer!.
    autorewrite with sublist.
    erewrite upd_Znth_same.
    auto.
    autorewrite with sublist.
    unfold default_val; simpl;
    repeat rewrite Zlength_list_repeat;
    subst;
    generalize H8;
    strip_repr; intro; try list_solve.
    repeat erewrite upd_Znth_same.
    forward.
    forward.
    entailer!.
    entailer!.
    erewrite upd_Znth_same.
    auto.
    autorewrite with sublist.
    unfold default_val; simpl;
    repeat rewrite Zlength_list_repeat; try list_solve.
    erewrite upd_Znth_same.
    forward.
    entailer!.
    forward.
    assert (exists v, der_write_TL_m 
                   fi (Int.repr overall_length) 0 0%int ls = inr v) as I.
    { eapply eval_DWT_opt_inr' in H5.
      eassumption. }
    destruct I as [v I].
    unfold evalErrW in H5.
    setoid_rewrite I in H5.
    break_let.
    Exists (j + 1) (encoded a + overall_length) (overall_length :: lens).
    entailer!.
    repeat split; auto; try list_solve.
    assert (exists ls', der_write_TL_m
                    (Int.repr (Znth (len (tags td) - len lens - 1) 
                           (tags td)))
                    (Int.repr overall_length) 0 0%int ls 
                   = inr (ls', {| encoded := (encoded a) |})) as E.
    { eapply eval_DWT_opt_inr; auto.
      unfold evalErrW.
      erewrite I.
      auto. }  
    destruct E as [ls' TL].
    eexists.
    eapply write_TL_to_loop1_sublist_inr with (j := len lens).
    list_solve.
    erewrite Loop.
    auto.
    eassumption.
    do 2 f_equal.
    strip_repr.
    f_equal.
    lia.
    unfold evalErrW.
    erewrite I.
    unfold encoded.   
    normalize.
    do 2 f_equal.
    lia.
    unfold evalErrW.
    erewrite I.
    remember (len lens) as j.
    destruct a.
    assert ( (upd_Znth (len (tags td) - j - 1)
       (upd_Znth (len (tags td) - j - 1)
          (default_val (tarray tint (len (tags td) - j)) ++
           map Vint (map Int.repr lens) ++ default_val (tarray tint (16 - len (tags td))))
          (Vint (Int.repr encoded))) (Vint (Int.repr (overall_length + encoded - encoded)))) = 
         (default_val (tarray tint (len (tags td) - len (overall_length :: lens))) ++
         (Vint (Int.repr overall_length) :: map Vint (map Int.repr lens)) ++
         default_val (tarray tint (16 - len (tags td))))) as U.
    { replace (overall_length + encoded - encoded) with overall_length by nia.
      assert (upd_Znth_idem: forall {A} j ls (a b : A),
                 0 <= j < len ls ->           
                 
                 upd_Znth j (upd_Znth j ls b) a = upd_Znth j ls a).
      { intros.
        erewrite upd_Znth_unfold.
        erewrite sublist_upd_Znth_l.
        erewrite sublist_upd_Znth_r.
        erewrite upd_Znth_Zlength.
        erewrite upd_Znth_unfold.
        auto.
        all: try nia.
         erewrite upd_Znth_Zlength; try nia.
          erewrite upd_Znth_Zlength; try nia. }

      erewrite upd_Znth_idem.
      erewrite upd_Znth_app1.
      erewrite upd_Znth_unfold.
      setoid_rewrite (Zlength_default_val).      
      autorewrite with sublist.
      replace (len (tags td) - Z.succ (len lens)) with 0 by list_solve.
      autorewrite with sublist.
      auto.
      all: cbn; try list_solve. }
    setoid_rewrite U.
    entailer!.
    all: autorewrite with sublist.
    1-3: 
    setoid_rewrite Zlength_default_val;
     try setoid_rewrite Zlength_default_val with (t := tint) (n := (16 - (tags_count)));
       subst; try list_solve.
    subst. strip_repr.
    ++ (* BREAK *)
    forward.
    Exists lens overall_length (tags_count - j - 1).
    entailer!.
    repeat split.
    generalize H8.
    strip_repr.
    remember (len lens) as j.
    destruct H5.
    erewrite sublist_same_gen in H.
    eexists.
    eassumption.
    generalize H8.
    strip_repr.
    intro.
    lia.
    lia.
    generalize H8;
      strip_repr;
      intro;
      list_solve.
    strip_repr.       
  + Intros lens overall_length j.
    forward_if.
  { forward. }
    (* 3d loop *)
  {  
  destruct H6 as [ls Loop].
  forward_loop ( 
  EX j : Z, EX l : Z, 
  PROP (0 <= j <= tags_count;
        exists ls', der_write_tags_loop2 (sublist 0 j ts)
                                  (sublist 0 j (map Int.repr lens)) 
                                  j
                                  (if Val.eq cb nullval then 0 else 32)
                                  last_tag_form ls = inr (ls', encode l))
  LOCAL (
  temp _i (Vint (Int.repr j));
  temp _tags tags_p;
  temp _overall_length (Vint (Int.repr overall_length));
  temp _tags_count (Vint (Int.repr tags_count));
  temp _t'17 (Vint (Int.repr tags_count)); 
  lvar _lens (tarray tint 16) v_lens;
  lvar _tags_buf_scratch (tarray tuint 16) v_tags_buf_scratch; 
  temp _sd td_p;
  temp _struct_length (Vint (Int.repr struct_len));
  temp _tag_mode (Vint (Int.repr tag_mode));
  temp _last_tag_form (Vint (Int.repr last_tag_form));
  temp _tag (Vint (Int.repr tag));
  temp _cb cb; temp _app_key app_key)
  SEP (data_at Tsh (tarray tint 16)
                (default_val (tarray tint (len (tags td) - len lens)) 
                 ++ map Vint (map Int.repr lens) ++
                 default_val (tarray tint (16 - len (tags td)))) v_lens;
       data_at_ Tsh (tarray tuint 16) v_tags_buf_scratch ;
        
       field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p;
       field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
                (Vint (Int.repr (len (tags td)))) td_p;
       data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
       func_ptr' dummy_callback_spec cb; data_at_ Tsh tuint app_key; valid_pointer cb))%assert

  break: 
  (PROP (exists l ls', der_write_tags_loop2 ts (map Int.repr lens) (len (tags td))
                       (if Val.eq cb nullval then 0 else 32)
                        last_tag_form ls = inr (ls', encode l))
  LOCAL (temp _i (Vint (Int.repr tags_count)); 
         temp _tags tags_p;
         temp _overall_length (Vint (Int.repr overall_length));
         temp _tags_count (Vint (Int.repr tags_count));
         temp _t'17 (Vint (Int.repr tags_count));
         lvar _lens (tarray tint 16) v_lens;
         lvar _tags_buf_scratch (tarray tuint 16) v_tags_buf_scratch; 
         temp _sd td_p;
         temp _struct_length (Vint (Int.repr struct_len));
         temp _tag_mode (Vint (Int.repr tag_mode));
         temp _last_tag_form (Vint (Int.repr last_tag_form)); 
         temp _tag (Vint (Int.repr tag));
         temp _cb cb; temp _app_key app_key)
  SEP (data_at Tsh (tarray tint 16)
                (default_val (tarray tint (len (tags td) - len lens)) ++
         map Vint (map Int.repr lens) ++
         default_val (tarray tint (16 - len (tags td)))) v_lens;
        data_at_ Tsh (tarray tuint 16) v_tags_buf_scratch;
       field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p;
       field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
                (Vint (Int.repr (len (tags td)))) td_p;
       data_at Tsh (tarray tuint (len (tags td)))
               (map Vint (map Int.repr (tags td))) tags_p;
       func_ptr' dummy_callback_spec cb;
       data_at_ Tsh tuint app_key; 
       valid_pointer cb))%assert.
  ++ forward.
     Exists 0 0.
     entailer!.
     exists ls; auto.
 ++ Intros i l.
    forward_if. 
    { forward_if
        (temp _t'4 
              ((Val.of_bool
                  (Int.repr i < Int.repr (tags_count - 1))%int))).
      congruence.
      forward.
      entailer!.
      assert ((0 <= i < len (map Int.repr (tags td)))) as K.
      { erewrite Zlength_map. subst. lia. }
      forward.
      assert ( (0 <= i < len (tags td))) as K' by (subst; list_solve).
      forward.
      replace (len (tags td) - len lens) with 0 by list_solve.
      autorewrite with sublist.
      forward.
      entailer!.
      autorewrite with sublist.
      auto.
      erewrite app_Znth1.
      forward_call (Int.repr (Znth i ts),
                  Int.repr (Znth i lens),
                  cb, app_key, 0%int, ls).
    entailer!.
    cbn.
    repeat f_equal.
    autorewrite with sublist.
    auto.
    break_if; auto.
    generalize Heqb.
    unfold Int.lt.
    strip_repr.
    break_if; try lia.
    congruence.
    rewrite_if_b.
    unfold Frame.
    instantiate
      (1 :=
         [(data_at Tsh (tarray tint 16)
     (map Vint (map Int.repr lens) ++
          default_val (tarray tint (16 - len (tags td)))) v_lens *
   data_at_ Tsh (tarray tuint 16) v_tags_buf_scratch *
   field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p *
   field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
            (Vint (Int.repr (len (tags td)))) td_p *
   data_at Tsh (tarray tuint (len (tags td)))
           (map Vint (map Int.repr (tags td))) tags_p)%logic]).
    unfold fold_right_sepcon.
    rewrite_if_b.
    entailer!.
    erewrite data_at__change_composite.
    entailer!.
    (*  cs_preserve_type CompSpecs Der_write_TL.CompSpecs
        (coeq CompSpecs Der_write_TL.CompSpecs)
    enc_key_s = true doesn't hold *)
    admit.
    (* change_compspecs CompSpecs. - not working - debug *)
    rewrite_if_b.
    Intros.
    forward.
    abbreviate_semax.
    forward_if.
   { (* return -1 *)
     rewrite_if_b.
    forward.
    rewrite_if_b.
    entailer!.
    remember (tags td) as ts.   
     assert (i = 0) as II by lia.
    erewrite II in *.
      assert (exists e, der_write_TL_m
                   (Int.repr (Znth 0 ts))
                   (Int.repr (Znth 0 lens)) 32 0%int ls = inl e) as E.
    { eapply eval_DWT_opt_to_Z.
      erewrite Heqts in *.
      subst.
      setoid_rewrite H11. auto. }
    destruct E as [err E].  
    destruct H9 as [e2 Loop2].
    { unfold der_write_tags.
      break_if; Zbool_to_Prop; try list_solve.
      subst; list_solve.
      unfold evalErrW.
      cbn.
      break_if; Zbool_to_Prop; try list_solve.
      subst.
      erewrite Loop.
      simpl.
      replace (tags td) with [Znth 0 (tags td)].
      replace (lens) with [Znth 0 lens].
      simpl.
      erewrite E.
      auto.  
      all: erewrite <- sublist_one with (hi := len lens);
      try list_solve; 
      autorewrite with sublist; auto. }
     (* change_compspecs CompSpecs. - not working - debug *)
    admit. }
    forward.
    Exists 1.
    assert (i = 0) as II by lia.
    erewrite II in *.
    assert (O := H11).
    eapply (eval_DWT_opt_inr
              (Int.repr (Znth 0 ts))
              (Int.repr (Znth 0 lens))
              (if Val.eq cb nullval then 0 else 32)
               0%int ls) in O.
    destruct O as [lso O].
    
    break_match; try contradiction.
    break_match.
    Exists encoded.
    repeat rewrite_if_b.
    entailer!.
    destruct H9 as [ls' E].
    eexists.
    autorewrite with sublist.
    { replace (tags td) with [Znth 0 (tags td)].
      replace (lens) with [Znth 0 lens].
      simpl.
      erewrite O.
      repeat f_equal.
      lia.
      all: erewrite <- sublist_one with (hi := len lens);
        try list_solve; 
        autorewrite with sublist; auto. }
    replace (len (tags td) - len lens) with 0 by list_solve.
    entailer!.
    admit. (* change CompSpecs *)
    rewrite_if_b.   
    reflexivity.
    subst. auto.
    list_solve. }
    (* loop break *)
    forward.
    entailer!.
    rewrite_if_b.
    split.
    generalize H9.
    autorewrite with sublist.
    intro K.
    eexists.
    replace i with (len (tags td)) in * by list_solve.
    eassumption.
    repeat f_equal.
    lia.
 ++ (* after loop *)
    forward.
    entailer!.
    destruct H6 as [ls' Loop2].
    cbn.
    unfold der_write_tags.
    break_if. Zbool_to_Prop. lia.
    repeat rewrite_if_b.
    break_if; Zbool_to_Prop; try lia.
    break_if; Zbool_to_Prop; try lia.
    cbn.
    unfold evalErrW.
    erewrite Loop.
    simpl.
    destruct Loop2 as [ls'' Loop2].
    erewrite Loop2.
    do 2 f_equal.
Admitted.
*)
End Der_write_tags.
