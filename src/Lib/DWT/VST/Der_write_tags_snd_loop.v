Require Import Core.Core Core.StructNormalizer VstLib Exec.Der_write_tags 
        ErrorWithWriter Clight.dummy Callback.Dummy.
Require Import VST.floyd.proofauto.

 Require Import VST.Der_write_TL. 

Require Import Clight.der_encoder Types.
Require Import VstTactics.
 Require Import Core.Tactics Core.Notations Core.SepLemmas.

Definition composites :=
  composites ++ (match find_cs dummy._dummy dummy.composites with
                 | Some r => [r]
                 | None => []
                 end).

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


Instance Change3 : change_composite_env Der_write_TL.CompSpecs CompSpecs.
Proof. make_cs_preserve Der_write_TL.CompSpecs CompSpecs. Defined.

Instance Change4 : change_composite_env CompSpecs Der_write_TL.CompSpecs.
Proof. make_cs_preserve CompSpecs Der_write_TL.CompSpecs. Defined.

Open Scope Z.

Section Der_write_tags.

(* from ber_check_tags
   (tag_mode = 0;
   last_tag_form = 0;
   0 < len ptr <= Ptrofs.max_unsigned;
   (Znth 0 ptr) & 32 = 0;
   nullval = opt_ctx_p;
   nullval = opt_tlv_form_p;
   1 = len (tags td);
   0 <= Ptrofs.unsigned i + len ptr <= Ptrofs.max_unsigned;
   Forall (fun x => 0 <= x <= Byte.max_unsigned) ptr;
   0 <= size <= Int.max_unsigned) *)
           
Definition der_write_tags_spec : ident * funspec :=
  DECLARE _der_write_tags
  WITH td_p : val, td : TYPE_descriptor,
       struct_len: Z, tag_mode : Z, last_tag_form : Z, tag : Z, 
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
           Vint (Int.repr last_tag_form); Vint (Int.repr tag); cb; app_key)
    GLOBALS()
    SEP(field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) 
                         [StructField _tags] 
                         tags_p td_p;
          field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) 
                         [StructField _tags_count] 
                         (Vint (Int.repr (len (tags td)))) td_p;
        data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
        func_ptr' dummy_callback_spec cb;
        data_at_ Tsh enc_key_s app_key;
        valid_pointer cb)
    POST[tint]
    let size := if Val.eq cb nullval then 0 else 32 in
      PROP()
      LOCAL(temp ret_temp 
                 (Vint (Int.repr (match evalErrW 
                 (der_write_tags td struct_len tag_mode last_tag_form tag size) [] with
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
          data_at_ Tsh enc_key_s app_key;
          valid_pointer cb).


Definition Gprog := ltac:(with_library prog [der_write_tags_spec;
                                             der_write_TL_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog 
                                     (normalize_function 
                                        f_der_write_tags composites)
                                     der_write_tags_spec.
Proof.
  start_function.
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
       func_ptr' dummy_callback_spec cb; data_at_ Tsh enc_key_s app_key; 
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
  PROP (0 <= tags_count - j - 1 <= tags_count;
        exists ls, der_write_tags_loop1 (sublist (tags_count - j) 
                                            tags_count ts) struct_len [] [] 
              = inr (ls, (lens, encode overall_length));
       len lens = j)
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
  data_at_ Tsh enc_key_s app_key;
  valid_pointer cb))%assert 

 break:
  (EX lens : list Z, EX overall_length : Z, EX j : Z,
  PROP (j < 0;
        exists ls, der_write_tags_loop1 ts struct_len [] [] 
              = inr (ls, (lens, encode overall_length)))
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
       data_at_ Tsh enc_key_s app_key;
       valid_pointer cb))%assert.
  + forward.    
    Exists 0 struct_len (@nil Z).
    autorewrite with sublist.
    entailer!.
    repeat split.
    eexists. cbn. auto.
    strip_repr.
    assert (forall { cs : compspecs } t l1 l2, 
               (default_val (tarray t l1) ++
                default_val (tarray t l2)) = default_val (tarray t (l1 + l2))) as DV.
    admit. (* add lemma *)
    repeat erewrite DV.
    autorewrite with sublist.
    replace (len (tags td) + (16 - len (tags td))) with 16 by list_solve.
    entailer!.
  + Intros j overall_length lens.
    forward_if.
    assert ((0 <= Int.unsigned (Int.repr (tags_count - j) - 1)%int 
             < len (map Int.repr (tags td)))) as TJ.
    { erewrite Zlength_map; subst; strip_repr. }
(*    assert (tags_count - j - 1 >= 0) as TJ. 
    { generalize H8; strip_repr;
        subst;
        repeat break_if; strip_repr. } *)
    assert ((0 <= Int.unsigned (Int.repr (tags_count - j) - 1)%int 
             < len ((tags td)))) as TJ'.
    { try erewrite Zlength_map; subst; strip_repr. }
    forward.
  (*  entailer!.
    strip_repr.
    entailer!.
    erewrite app_Znth1.
    erewrite Znth_map.
    auto.
    1-2: try (strip_repr;
              list_solve).
    erewrite app_Znth1.
    strip_repr. *)
    strip_repr.
    (* erewrite zlist_hint_db.Znth_map_Vint. *)
    remember (Int.repr (Znth (tags_count - j - 1) ((ts)))) as fi.
    destruct H6 as [ls Loop].
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
   func_ptr' dummy_callback_spec cb * data_at_ Tsh enc_key_s app_key * 
   valid_pointer cb)%logic]).
    unfold fold_right_sepcon.
    entailer!.
    eapply valid_pointer_null.
    repeat rewrite_if_b.
    Intros.
    forward.
    forward.
    entailer!.
    erewrite upd_Znth_same.
    cbn. auto.
    unfold default_val; cbn; try nia.
    autorewrite with sublist.
    nia.
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
      setoid_rewrite H6. auto. }
    destruct E as [err E].    
    unfold der_write_tags.
    assert (exists k, der_write_tags_loop1 (tags td) struct_len [] [] = inl k) as EEE.
    { erewrite Heqts in *. 
      exists err.
      eapply write_TL_to_loop1_sublist with (j := len lens); 
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
    rewrite H6 in *.
    erewrite EEE.
    congruence. } 
  }
    abbreviate_semax.
    deadvars!.
    forward.  
    entailer!.
    autorewrite with sublist.
    erewrite upd_Znth_same.
    auto.
    autorewrite with sublist.
    unfold default_val; simpl;
    repeat rewrite Zlength_list_repeat;
    subst;
    generalize H8;
    strip_repr; nia.
    repeat erewrite upd_Znth_same.
    forward.
    forward.
    entailer!.
    erewrite upd_Znth_same.
    auto.
    autorewrite with sublist.
    unfold default_val; simpl;
    repeat rewrite Zlength_list_repeat; nia.
    erewrite upd_Znth_same.
    forward.
    forward.
    assert (exists v, der_write_TL_m 
                   fi (Int.repr overall_length) 0 0%int ls = inr v) as I.
    { eapply eval_DWT_opt_inr' in H6.
      eassumption. }
    destruct I as [v I].
    unfold evalErrW in H6.
    setoid_rewrite I in H6.
    break_let.
    Exists (j + 1) (encoded a + overall_length) (overall_length :: lens).
    entailer!.
    split. 
    admit. (* 0 <= len (tags td) - (len lens + 1) - 1 <= len (tags td) *)
    assert (exists ls', der_write_TL_m
                    (Int.repr (Znth (len (tags td) - len lens - 1) 
                           (tags td)))
                    (Int.repr overall_length) 0 0%int ls 
                   = inr (ls', {| encoded := (encoded a) |})) as E.
    { eapply eval_DWT_opt_inr; auto.
      unfold evalErrW.
      erewrite I.
      auto. }  
    repeat split; auto; try list_solve.
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
      subst.
      all: admit. (* default list manipulations *)     
    }
    setoid_rewrite U.
    entailer!.
    all: autorewrite with sublist.
    1-3: 
    setoid_rewrite Zlength_default_val;
     try setoid_rewrite Zlength_default_val with (t := tint) (n := (16 - (tags_count - 1)));
       try nia.
    list_solve.
    strip_repr.
    list_solve.
    ++ (* BREAK *)
    forward.
    Exists lens overall_length (tags_count - j - 1).
    entailer!.
    repeat split.
    generalize H8.
    strip_repr.
    remember (len lens) as j.
    destruct H6.
    erewrite sublist_same_gen in H.
    eexists.
    eassumption.
    generalize H8.
    strip_repr.
    intro.
    lia.
    lia.
    strip_repr.       
  + Intros lens overall_length j.
    forward_if.
  { forward. }
    (* 3d loop *)
  {  
  destruct H6 as [ls Loop].
  forward_loop ( 
  EX j : Z, EX l : Z, EX k : Z,
  PROP (0 <= j <= tags_count;
        len lens = tags_count; (* Do we need this ? *)
        exists ls, der_write_tags_loop2 (sublist 0 j ts)
                                  (sublist 0 j (map Int.repr lens)) 
                                  k
                                  (if Val.eq cb nullval then 0 else 32)
                                  struct_len [] = inr (ls, encode l))
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
       func_ptr' dummy_callback_spec cb; data_at_ Tsh enc_key_s app_key; valid_pointer cb))%assert

  break: 
  (EX l : Z,                     
  PROP (exists ls', der_write_tags_loop2 ts (map Int.repr lens) 0
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
       data_at_ Tsh enc_key_s app_key; 
       valid_pointer cb))%assert.
  ++ forward.
     Exists 0 0 0.
     entailer!.
      repeat split.
     admit. (*  len lens = len (tags td) *)
     exists []; auto.
 ++ Intros i l k.
    forward_if. 
    { forward_if
        (temp _t'4 ((Val.of_bool
                            (Int.repr i < Int.repr (tags_count - 1))%int))).
      congruence.
      forward.
      entailer!.
      assert ((0 <= i < len (map Int.repr (tags td)))) as K.
      { erewrite Zlength_map. subst. lia. }
      forward.
      assert ( (0 <= i < len (tags td))) as K' by (subst; list_solve).
      forward.
      forward.
      entailer!.
      erewrite app_Znth1.
      auto.
      admit. (*  (Znth i (default_val (tarray tint (len (tags td) - len lens)))) *)
      autorewrite with sublist.
      admit. (*  i < len (default_val (tarray tint (len (tags td) - len lens))) *) 
      erewrite app_Znth1.
    forward_call (Int.repr (Znth i ts),
                  Int.repr (Znth i lens),
                  cb, app_key, 
                  force_int (Val.of_bool (Int.repr i < Int.repr (len (tags td) - 1))%int), ls).
    entailer!.
    cbn.
    unfold force_int;
    unfold Val.of_bool.
    repeat f_equal.
    (* Znth i (list_repeat (Z.to_nat (len (tags td) - len lens)) Vundef) =
  Vint (Int.repr (Znth i lens)) *)   
    admit.
    break_if; auto.
    unfold Frame.
      instantiate
      (1 :=
         [(data_at Tsh (tarray tint 16)
     (default_val (tarray tint (len (tags td) - len lens)) ++
      map Vint (map Int.repr lens) ++ default_val (tarray tint (16 - len (tags td)))) v_lens *
   data_at_ Tsh (tarray tuint 16) v_tags_buf_scratch *
   field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags) tags_p td_p *
   field_at Tsh (Tstruct _asn_TYPE_descriptor_s noattr) (DOT _tags_count)
     (Vint (Int.repr (len (tags td)))) td_p *
   data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p)%logic]).
    unfold fold_right_sepcon.
    rewrite_if_b.
    entailer!.
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
      assert (exists e, der_write_TL_m
                   (Int.repr (Znth i ts))
                   (Int.repr (Znth i lens)) 32 (force_int
                    (Val.of_bool (Int.repr i < Int.repr (len ts - 1))%int
                     )) ls = inl e) as E.
    { eapply eval_DWT_opt_to_Z.
      erewrite Heqts in *.
      setoid_rewrite H11. auto. }
    destruct E as [err E].  
    destruct H9 as [e2 Loop2].
    assert (der_write_tags_loop2 
              (sublist 0 (i + 1) ts)
              (sublist 0 (i + 1) (map Int.repr lens)) (i)
              32 0 ls = inl err) as EEE.
    { admit. }
    eapply write_TL_to_loop2_sublist in EEE.
    replace i with (len ts) in EEE by admit.
    unfold evalErrW.
    rewrite_if_b.
    repeat f_equal.
    unfold der_write_tags.
    cbn.
    break_if. auto.
    break_if.
    Zbool_to_Prop.
    list_solve.
    subst.
    erewrite Loop.
    simpl.
    erewrite EEE. auto.
    entailer!.
    (* change_compspecs CompSpecs. - not working - debug *)
    admit. }
    forward.
    Exists (i + 1).
    assert (O := H11).
    eapply (eval_DWT_opt_inr
              (Int.repr (Znth i ts))
              (Int.repr (Znth i lens))
              (if Val.eq cb nullval then 0 else 32)
              (force_int
                 (if eq_dec (Int.repr last_tag_form) 0%int
                  then Val.of_bool (Int.repr i < Int.repr (len (tags td) - 1))%int
                  else Vone)) ls) in O.
    destruct O as [lso O].
    break_match; try contradiction.
    break_match.
    Exists encoded.
    Exists (k + 1).
    repeat rewrite_if_b.
    entailer!.
    destruct H9 as [ls' E].
    eexists.
    rewrite_if_b.
    assert (write_TL_to_loop2_sublist_inr : 
               forall ts ll  ls1 ls2 j s i ltf v1 v2 ii,
                 der_write_tags_loop2
                   (sublist 0 j ts) 
                   (sublist 0 j ll) (i - 1) s ltf ii = inr (ls1, v1) ->
                 der_write_TL_m (Int.repr (Znth j ts))
                                (Znth j ll) s 
                   (if (negb (ltf =? 0) || (i - 1 <? len ts - 1))%bool
                    then 1%int 
                    else 0%int) ls1 = inr (ls2, v2) ->
                 
                 der_write_tags_loop2 
                   (sublist 0 (j + 1) ts)
                   (sublist 0 (j + 1) ll) 
                   i s ltf ii = inr (ls2, v2)). admit.
    eapply write_TL_to_loop2_sublist_inr.
    replace (k + 1 - 1) with k by nia.
    eassumption.
    instantiate (1 := lso).
    admit. (* from O *)
    entailer!.
    admit. (* change CompSpecs *)
    rewrite_if_b.
    rewrite if_true.
    reflexivity.
    subst. auto.
    admit. (* len (default_val) *)  }
    (* loop break *)
    forward.
    Exists l.
    entailer!.
    rewrite_if_b.
    split.
    generalize H9.
    autorewrite with sublist.
    auto.
    (* remove k - change exec spec to reflect the restrictions *)
    admit. 
    repeat f_equal.
    lia.
 ++ (* after loop *)
    Intros l.
    forward.
    entailer!.
    * destruct H6 as [a Loop2].
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
      replace (len (tags td)) with 0 by admit. (* why len here? - check exec *)
      erewrite Loop2.
      do 2 f_equal.
      simpl.
      admit.
Admitted.

    
