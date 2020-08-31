Require Import Der_write_TL.
Require Import Core.Core Core.StructNormalizer VstLib Exec.Der_write_tags 
        ErrorWithWriter Clight.dummy Callback.Dummy.
Require Import VST.floyd.proofauto.
Require Import Clight.der_encoder Types.
Require Import VstTactics.
 Require Import Core.Tactics Core.Notations Core.SepLemmas.

(* Require Import VST.Der_write_TL. *)

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

Open Scope Z.

Section Der_write_tags.

Definition type_descr_composites :=
  ((_name, (tptr tschar)) :: (_xml_tag, (tptr tschar)) ::
    (_op, (tptr (Tstruct _asn_TYPE_operation_s noattr))) ::
    (_tags, (tptr tuint)) :: (_tags_count, tuint) ::
    (_all_tags, (tptr tuint)) :: (_all_tags_count, tuint) ::
    (_encoding_constraints, (Tstruct _asn_encoding_constraints_s noattr)) ::
    (_elements, (tptr (Tstruct _asn_TYPE_member_s noattr))) ::
    (_elements_count, tuint) :: (_specifics, (tptr tvoid)) :: nil).


Fixpoint mk_TYPE_descriptor_repr (ls : list (ident * type))  :=
  match ls with
    | [] => val
    | [h] => let (_, t) := h in reptype t
    | h :: tl => let (_, t) := h in
                (reptype t * mk_TYPE_descriptor_repr tl)%type
  end.  

Definition type_descr := mk_TYPE_descriptor_repr type_descr_composites.

Definition get_tags_count (v : type_descr) :=
  let (_, y) := v in
  let (_, y) := y in
  let (_, y) := y in
  let (_, y) := y in
  let (x, y) := y in
        x. 

Definition get_tags (v : type_descr) :=
  let (_, y) := v in
  let (_, y) := y in
  let (_, y) := y in
  let (x, y) := y in
        x.

Definition der_write_tags_spec : ident * funspec :=
  DECLARE _der_write_tags
  WITH td_p : val, td : TYPE_descriptor,
       struct_len: Z, tag_mode : Z, last_tag_form : Z, tag : Z, 
       cb : val, app_key : val,
       td' : type_descr,
       tags_p : val
  PRE[tptr type_descriptor_s, tuint, tint, tint, tuint, 
      tptr cb_type, tptr tvoid]
    PROP(isptr tags_p;
         0 <= len (tags td) + 1 <= 16;
         get_tags_count td' = Vint (Int.repr (Zlength (tags td)));
         get_tags td' = tags_p) 
    PARAMS(td_p; Vint (Int.repr struct_len); Vint (Int.repr tag_mode);
           Vint (Int.repr last_tag_form); Vint (Int.repr tag); cb; app_key)
    GLOBALS()
    SEP(data_at Tsh type_descriptor_s td' td_p;
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
      SEP(data_at_ Tsh type_descriptor_s td_p;
          data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
          func_ptr' dummy_callback_spec cb;
          data_at_ Tsh enc_key_s app_key;
          valid_pointer cb).

Definition Gprog := ltac:(with_library prog [der_write_tags_spec;
                                               der_write_TL_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog (normalize_function f_der_write_tags composites)
                                     der_write_tags_spec.
Proof.
  start_function.
  unfold get_tags_count in H1.
  repeat break_let.
  forward.
  rewrite H1.
  forward_if True.
  *
  forward.
  entailer!.
  { break_if;
    unfold der_write_tags;
    replace (4 <? Zlength (tags td) + 1) with true;
    auto;
    symmetry; Zbool_to_Prop; nia. }
  *
  forward.
  entailer!.
  *
  remember ((if ((Int.repr tag_mode == (Int.neg (Int.repr 1)))%int &&
                (negb (Int.eq (Int.repr (Zlength (tags td))) Int.zero))) 
             then Int.one
             else Int.zero)%bool) as t1.
  remember (if eq_dec (Int.repr tag_mode) 0%int
                  then len (tags td)
                  else len (tags td) + 1 - Int.unsigned t1) as tags_count.
  forward_if (
  PROP ()
  LOCAL (
  temp _tags v_tags_buf_scratch;
  temp _tags_count (Vint (Int.repr tags_count));
  temp _tags_buf v_tags_buf_scratch;
  temp _t'17 (Vint (Int.repr tags_count));
  lvar _lens (tarray tint 16) v_lens;
  lvar _tags_buf_scratch (tarray tuint 16) v_tags_buf_scratch; 
  temp _sd td_p;
  temp _struct_length (Vint (Int.repr struct_len)); 
  temp _tag_mode (Vint (Int.repr tag_mode));
  temp _last_tag_form (Vint (Int.repr last_tag_form));
  temp _tag (Vint (Int.repr tag));
  temp _cb cb;
  temp _app_key app_key)
  SEP (data_at_ Tsh (tarray tint 16) v_lens;
       data_at Tsh (tarray tuint (len (tags td)))
               (map Vint (map Int.repr (tags td))) tags_p;
       if eq_dec (Int.repr tag_mode) 0%int
       then data_at Tsh (tarray tuint 16)
         (map Vint (map Int.repr (tags td))
              ++ default_val (tarray tuint (16 - len (tags td))))
         v_tags_buf_scratch
       else 
         data_at Tsh (tarray tuint 16) 
                ((if ((Int.repr tag_mode == (Int.neg (Int.repr 1)))%int &&
               (negb (Int.eq (Int.repr (Zlength (tags td))) Int.zero)))%bool
                then upd_Znth 0 (map Vint (map Int.repr (tags td))) (Vint (Int.repr tag)) 
                else (Vint (Int.repr tag) :: (map Vint (map Int.repr (tags td))))) ++
                default_val (tarray tuint (16 - (len (tags td)) - 1))) 
               v_tags_buf_scratch;
 (* data_at Tsh type_descriptor_s
          (r, (r0, (r1, (tags_p, (Vint (Int.repr (len (tags td))), m3))))) td_p; *)
  func_ptr' dummy_callback_spec cb; data_at_ Tsh enc_key_s app_key; 
  valid_pointer cb;
  valid_pointer nullval)).
  ** admit.
  ** admit.
  ** 
  Arguments eq_dec : simpl never.
  forward_if.
  forward.
  entailer!.
  admit.
  entailer!.
  break_if; entailer!.
  admit.
  admit.
  repeat forward.
  (* loop 2 *) 
  Require Import Exec.Der_write_TL_m.
  remember (if eq_dec (Int.repr tag_mode) 0%int
       then data_at Tsh (tarray tuint 16)
                    ((map Vint (map Int.repr (tags td)))
                    ++
                    default_val (tarray tuint (16 - len (tags td))))
                    v_tags_buf_scratch 
     else
      data_at Tsh (tarray tuint 16)
        ((if
           ((Int.repr tag_mode == Int.neg (Int.repr 1))%int &&
            negb (Int.repr (len (tags td)) == 0)%int)%bool
          then upd_Znth 0 (map Vint (map Int.repr (tags td))) (Vint (Int.repr tag))
          else Vint (Int.repr tag) :: map Vint (map Int.repr (tags td))) ++
         default_val (tarray tuint (16 - len (tags td) - 1))) v_tags_buf_scratch)
           as data_at_tags.

  remember (tags td) as ts.
  forward_loop (
  EX j : Z, EX overall_length : Z, EX lens : list Z,
  PROP (0 <= j <= tags_count;
        exists ls, der_write_tags_loop1 (sublist (tags_count - j) tags_count ts) struct_len [] [] 
            = inr (ls, (lens, encode overall_length));
       len lens = j)
  LOCAL (
  temp _tags v_tags_buf_scratch;  
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
                (map Vint (map Int.repr lens) ++ (default_val (tarray tint (16 - j)))) 
               v_lens; 
       data_at_tags;
 (* data_at Tsh type_descriptor_s (r, (r0, (r1, (r2, (Vint (Int.repr (len (tags td))), m3))))) td_p; *)
  data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
  func_ptr' dummy_callback_spec cb;
  data_at_ Tsh enc_key_s app_key;
  valid_pointer cb;
  valid_pointer nullval))%assert 

 break:
  (EX lens : list Z, EX overall_length : Z, EX j : Z,
  PROP (j < 0;
        exists ls, der_write_tags_loop1 ts struct_len [] [] 
              = inr (ls, (lens, encode overall_length)))
  LOCAL (temp _tags v_tags_buf_scratch;
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
               ( map Vint (map Int.repr lens) ++
               default_val (tarray tint (16 - tags_count))) v_lens;
       data_at_tags;
 (* data_at Tsh type_descriptor_s 
          (r, (r0, (r1, (r2, (Vint (Int.repr (len (tags td))), m3))))) td_p; *)
       data_at Tsh (tarray tuint (len (tags td)))
               (map Vint (map Int.repr (tags td))) tags_p;
       func_ptr' dummy_callback_spec cb;
       data_at_ Tsh enc_key_s app_key;
       valid_pointer cb;
       valid_pointer nullval)).
  + forward. 
    entailer!.
    repeat break_if; strip_repr.    
    Exists 0 struct_len (@nil Z).
    autorewrite with sublist.
    entailer!.
    split.
    { generalize H3.
      repeat break_if;
        pose proof (Zlength_nonneg (tags td));
      intro I;
      eapply repr_neq_e in I; split;
      strip_repr. }
    split.
    eexists.
    simpl.
    auto.
    repeat break_if; strip_repr.    
  + Intros j overall_length lens.
    forward_if.
    assert (tags_count - j - 1 >= 0) as TJ. 
    { generalize H7; strip_repr;
        subst;
        repeat break_if; strip_repr. }
    erewrite Heqdata_at_tags.
    destruct (eq_dec (Int.repr tag_mode) 0%int).
 ++ forward.
    entailer!.
    strip_repr.
    entailer!.
    erewrite app_Znth1.
    erewrite Znth_map.
    auto.
    1-2: try (strip_repr;
              list_solve).
    erewrite app_Znth1.
    strip_repr.
    erewrite zlist_hint_db.Znth_map_Vint. 
    remember ((Znth (tags_count - j - 1) ((map Int.repr ts)))) as fi.
    destruct H5 as [ls Loop].
    forward_call (fi, Int.repr overall_length, nullval, nullval, Int.zero, ls).
    rewrite_if_b.
    unfold Frame.
    instantiate
    (1 :=
       [(data_at Tsh (tarray tint 16)
               (map Vint (map Int.repr lens) ++
               default_val (tarray tint (16 - j))) v_lens *
         data_at Tsh (tarray tuint 16)
                 (map Vint (map Int.repr ts) 
                      ++ default_val (tarray tuint (16 - len ts))) v_tags_buf_scratch *
         data_at Tsh (tarray tuint (len (tags td)))
                 (map Vint (map Int.repr (tags td))) tags_p *
         func_ptr' dummy_callback_spec cb * 
         data_at_ Tsh enc_key_s app_key * 
   valid_pointer cb)%logic]).
    unfold fold_right_sepcon.
    entailer!.
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
                   (Znth (len (tags td) - len lens - 1) 
                         (map Int.repr (tags td)))
                   (Int.repr overall_length) 0 0%int ls = inl e) as E.
    { eapply eval_DWT_opt_to_Z.
      erewrite Heqts in *.
      setoid_rewrite H5. auto. }
    destruct E as [err E].    
    unfold der_write_tags.
    assert (exists k, der_write_tags_loop1 (tags td) struct_len [] [] = inl k) as EEE.
    { erewrite Heqts in *. 
      exists err.
      eapply write_TL_to_loop1_sublist with (j := len lens).
      nia.
      eassumption.
      erewrite Znth_map in E.
      eassumption.
      nia. }
    destruct EEE as [k EEE].
    unfold evalErrW.
    cbn. 
    break_if; auto.
    break_match; auto.
    generalize Heqo.
    break_if.
    assert (tag_mode = 0).
    { inversion e.
      admit. } (* TODO: add assumption about tag_mode < IntMax *)
    generalize Heqb0.
    break_if.
    Zbool_to_Prop.
    intro.
    pose proof (Zlength_nonneg (tags td)).
    nia.
    rewrite H2 in *.
    discriminate.
    erewrite EEE.
    congruence. }
    admit. (* FIX type_descriptor type *) }
    rewrite_if_b.
    abbreviate_semax.
    deadvars!.
    forward.  
    entailer!.
    autorewrite with sublist.
    erewrite upd_Znth_same.
    auto.
    autorewrite with sublist.
    unfold default_val; simpl. rewrite Zlength_list_repeat.
    subst.
    generalize H7.
    strip_repr.
    nia.
    nia.
    forward.
   (* 
    break_if.
    autorewrite with sublist.
    erewrite upd_Znth_Zlength.
    autorewrite with sublist.
    erewrite Zlength_default_val.
    nia. 
    nia.
     autorewrite with sublist.
     generalize H8.
    erewrite upd_Znth_Zlength.
    autorewrite with sublist.
    erewrite Zlength_default_val.
    nia. 
    nia. *)
    erewrite upd_Znth_same.
    forward.
    entailer!.
    erewrite upd_Znth_same.
    auto.
    autorewrite with sublist.
    replace (len (default_val (tarray tint (16 - len lens))))
            with (16 - len lens).
    nia.
    setoid_rewrite Zlength_default_val; auto.
    nia.
    erewrite upd_Znth_same.
    forward.
    forward.
    assert (exists v, der_write_TL_m fi (Int.repr overall_length) 0 0%int ls = inr v) as I.
    { eapply eval_DWT_opt_inr' in H5.
      eassumption. }
    destruct I as [v I].
    unfold evalErrW in H5.
    setoid_rewrite I in H5.
    break_let.
    Exists (j + 1) (encoded a + overall_length) (overall_length :: lens).
    rewrite_if_b.
    entailer!.
    split. 
    assert (exists ls', der_write_TL_m
                    (Znth (len (tags td) - len lens - 1) 
                          (map Int.repr (tags td)))
                    (Int.repr overall_length) 0 0%int ls 
                   = inr (ls', {| encoded := (encoded a) |})) as E.
    { eapply eval_DWT_opt_inr; auto.
      unfold evalErrW.
      erewrite I.
      auto. }  
    destruct E as [ls' TL].
    eexists.
    eapply write_TL_to_loop1_sublist_inr with (j := len lens).
    autorewrite with sublist. nia.
    erewrite Loop.
    auto.
    erewrite Znth_map in TL.
    eassumption.
    nia.
    repeat split.
    autorewrite with sublist; nia.
    strip_repr.
    do 2 f_equal.
    nia.
    unfold evalErrW.
    erewrite I.
    unfold encoded.   
    normalize.
    do 2 f_equal.
    nia.
    unfold evalErrW.
    erewrite I.
    remember (len lens) as j.
    assert ((upd_Znth (len (tags td) - j - 1)
       (upd_Znth (len (tags td) - j - 1)
          (map Vint (map Int.repr lens) ++ default_val (tarray tint (16 - j)))
          (Vint (Int.repr match a with
                          | {| encoded := v |} => v
                          end)))
       (Vint
          (Int.repr
             (overall_length + match a with
                               | {| encoded := v |} => v
                               end - match a with
                                     | {| encoded := v |} => v
                                     end)))) =
        
         Vint (Int.repr overall_length) :: map Vint (map Int.repr lens) 
           ++ default_val (tarray tint (16 - (j + 1)))) as U.
    { destruct a.
      replace (overall_length + encoded - encoded) with overall_length by nia.
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
      admit.
      admit.
      admit. }
    setoid_rewrite U.
    entailer!.
    autorewrite with sublist. 
    setoid_rewrite Zlength_default_val with (t := tint) (n := (16 - j)); try nia.
    autorewrite with sublist.
    setoid_rewrite Zlength_default_val with (t := tint) (n := (16 - j)); try nia.
    autorewrite with sublist. 
    setoid_rewrite Zlength_default_val with (t := tint) (n := (16 - j)); try nia. 
    autorewrite with sublist.
    nia.
    strip_repr.
    autorewrite with sublist.
    nia.
    ++ admit. (* tag_mode <> 0 *)
    ++ forward.
       Exists lens overall_length (tags_count - j - 1).
       entailer!.
       generalize H7.
       strip_repr.
       break_if.
       intro.
       remember (len lens) as j.
       assert (j = len (tags td)) as J by nia.
       erewrite J in *.
       autorewrite with sublist in H5.
       intuition.
       break_if;
       strip_repr.
       intro.
       intuition.
       autorewrite with sublist in H5.
       eassumption.
       intro.
       intuition.
       autorewrite with sublist in H5.
       remember (len lens) as j.
       assert (j - 1 = len (tags td)) as J by nia.
       try erewrite <- J in *.
       replace j with (len (tags td) + 1) in H5 by nia.
       erewrite sublist_same_gen in H5; try nia.
       eassumption.
       1-2: break_if;
       strip_repr.
       strip_repr.
       remember (len lens) as j.
       assert ( ((if eq_dec (Int.repr tag_mode) 0%int
              then len (tags td)
              else
               (len (tags td) + 1 -
                Int.unsigned
                  (if
                    ((Int.repr tag_mode == Int.repr (- (1)))%int &&
                     negb (Int.repr (len (tags td)) == 0)%int)%bool
                   then 1%int
                   else 0%int))%Z) = j)).
       { generalize H7.
         repeat break_if; strip_repr; try nia. }
       erewrite H1.    
       entailer!.       
  + Intros lens overall_length j.
    forward_if.
  { forward. }
  erewrite   Heqdata_at_tags. 
    (* 3d loop *)
  {  
  destruct H5 as [ls H5].
  forward_loop ( 
  EX j : Z, EX l : Z,
  PROP (0 <= j <= tags_count;
        len lens = tags_count;
       (* exists ls, der_write_tags_loop2 (sublist 0 j ts)
                                  (map Int.repr lens) 
                                  (tags_count - j)
                                  (if Val.eq cb nullval then 0 else 32)
                                  struct_len [] = inr (ls, encode l) *)
        exists ls', der_write_tags_loop2_app 
                 (Z.to_nat j) ts (map Int.repr lens) 
                 (if Val.eq cb nullval then 0 else 32)
                 last_tag_form ls = inr (ls', encode l))
  LOCAL (
  temp _i (Vint (Int.repr j));
  temp _tags v_tags_buf_scratch;
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
               (map Vint (map Int.repr lens) ++
               default_val (tarray tint (16 - tags_count))) v_lens;
       data_at_tags;
    
 (* data_at Tsh type_descriptor_s 
    (r, (r0, (r1, (r2, (Vint (Int.repr (len (tags td))), m3))))) td_p; *)
       data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
       func_ptr' dummy_callback_spec cb; data_at_ Tsh enc_key_s app_key; valid_pointer cb;
       valid_pointer nullval))%assert

  break: 
  (EX l : Z,                         
  PROP (exists ls', der_write_tags_loop2_app (Z.to_nat (len ts)) 
                                   ts (map Int.repr lens)
                        (if Val.eq cb nullval then 0 else 32)
                        last_tag_form ls = inr (ls', encode l))
  LOCAL (temp _len (Vint (Int.repr l)); 
         temp __constr (Vint (if negb (last_tag_form =? 0)
                                         then Int.one 
                                         else Int.zero));
         temp _i (Vint (Int.repr tags_count)); 
         temp _tags v_tags_buf_scratch;
         temp _overall_length (Vint (Int.repr overall_length));
         temp _tags_count (Vint (Int.repr (len (tags td))));
         temp _t'17 (Vint (Int.repr (len (tags td))));
         lvar _lens (tarray tint 16) v_lens;
         lvar _tags_buf_scratch (tarray tuint 16) v_tags_buf_scratch; 
         temp _sd td_p;
         temp _struct_length (Vint (Int.repr struct_len));
         temp _tag_mode (Vint (Int.repr tag_mode));
         temp _last_tag_form (Vint (Int.repr last_tag_form)); 
         temp _tag (Vint (Int.repr tag));
         temp _cb cb; temp _app_key app_key)
  SEP (data_at Tsh (tarray tint 16)
               (map Vint (map Int.repr lens) ++
               default_val (tarray tint (16 - tags_count))) v_lens;
       data_at_tags;
       (* data_at Tsh type_descriptor_s 
     (r, (r0, (r1, (r2, (Vint (Int.repr (len (tags td))), m3))))) td_p; *)
       data_at Tsh (tarray tuint (len (tags td)))
               (map Vint (map Int.repr (tags td))) tags_p;
       func_ptr' dummy_callback_spec cb;
       data_at_ Tsh enc_key_s app_key; 
       valid_pointer cb;
       valid_pointer nullval))%assert.
  ++ forward.
     Exists 0 0.
     entailer!.
     repeat split; break_if; strip_repr;try nia;
       autorewrite with sublist;
       simpl.
     break_if; strip_repr; try nia.
     admit.
     break_if; strip_repr; try nia.
     admit.
     admit.
     1-2: exists ls; auto.
 ++ Intros i l.
    forward_if. 
    { forward_if
        (temp _t'4 (if eq_dec (Int.repr last_tag_form) 0%int 
                    then (Val.of_bool
                            (Int.repr i < Int.repr (tags_count - 1))%int)
                    else Vone)).
      forward.
      rewrite_if_b.
      entailer!.
      forward.
      entailer!.
      break_if; strip_repr.
      rewrite_if_b.
      entailer!.      
      erewrite Heqdata_at_tags.
      rewrite_if_b.
      destruct (eq_dec (Int.repr tag_mode) 0%int).
    { forward.
      forward.
      entailer!.
      erewrite app_Znth1.
      erewrite Znth_map.
      auto.
      1-2: autorewrite with sublist;
      generalize H10;
      strip_repr;
      try nia.
      forward.
      entailer!.
      erewrite app_Znth1.
      erewrite Znth_map.
      auto.
      autorewrite with sublist.
      generalize H10.
      strip_repr.
      nia.
      autorewrite with sublist.
       generalize H10.
      strip_repr.
      nia.
      erewrite app_Znth1.
      erewrite Znth_map.
      erewrite app_Znth1.
      erewrite Znth_map.
      erewrite Znth_map.
      erewrite Znth_map.
     
    forward_call (Int.repr (Znth i ts), Int.repr (Znth i lens), cb, app_key, 
                  force_int (if eq_dec (Int.repr last_tag_form) 0%int
                             then Val.of_bool (Int.repr i < Int.repr (len (tags td) - 1))%int
                             else Vone), ls).
    entailer!.
    unfold force_int;
    unfold Val.of_bool.
    repeat break_if; cbn; auto.
    rewrite_if_b.
    unfold Frame.
    instantiate
      (1 :=
         [(data_at Tsh (tarray tint 16)
                   (map Vint (map Int.repr lens) 
                        ++ default_val (tarray tint (16 - tags_count))) v_lens *
           data_at Tsh (tarray tuint 16)
                   (map Vint (map Int.repr ts)
                        ++ default_val (tarray tuint (16 - len ts))) v_tags_buf_scratch *
           data_at Tsh (tarray tuint (len (tags td)))
                   (map Vint (map Int.repr (tags td))) tags_p *
           valid_pointer nullval)%logic]).
    unfold fold_right_sepcon.
    entailer!.
    admit.
    (* change_compspecs CompSpecs. *)
    Intros.
    forward.
    abbreviate_semax.
    forward_if.
   { (* return -1 *)
    forward.
    rewrite_if_b.
    entailer!.
    remember (tags td) as ts.    
      assert (exists e, der_write_TL_m
                   (Int.repr (Znth i ts))
                   (Int.repr (Znth i lens)) 32 (force_int
                    (if eq_dec (Int.repr last_tag_form) 0%int
                     then Val.of_bool (Int.repr i < Int.repr (len ts - 1))%int
                     else Vone)) ls = inl e) as E.
    { eapply eval_DWT_opt_to_Z.
      erewrite Heqts in *.
      setoid_rewrite H11. auto. }
    destruct E as [err E].  
    destruct H9 as [e2 Loop2].
    assert (exists k, der_write_tags_loop2_app 
                   (S (Z.to_nat i))
                   (tags td) (map Int.repr lens) 32 last_tag_form ls = inl k) as EEE.
    { erewrite Heqts in *. 
      exists err.
      eapply write_TL_to_loop2_app.
      eassumption.
      admit. }
    destruct EEE as [k EEE].
    unfold evalErrW.
    cbn. 
    break_if; auto.
    break_match; auto.
    generalize Heqo.
    break_if.
    assert (tag_mode = 0).
    { inversion e.
      admit. } (* TODO: add assumption about tag_mode < IntMax *)
    all: admit. }
    forward.
    Exists (i + 1).
    Exists 0.
    repeat rewrite_if_b.
    entailer!.
    split.
    generalize H10; strip_repr.
    nia.
    destruct H9 as [ls' E].
    eexists.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)). 
    simpl.
    
    forward.
    entailer!.
    ++
      forward.
      entailer!.
      (* why (struct_len - struct_len)? *)
      admit.
      admit.
Admitted.

End Der_write_tags.
*)
