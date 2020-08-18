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
  forward_if (
  PROP ()
  LOCAL (
  temp _tags v_tags_buf_scratch;
  temp _tags_count
              (Vint
                 (Int.repr
                    (if eq_dec (Int.repr tag_mode) 0%int
                     then len (tags td)
                     else len (tags td) + 1 - Int.unsigned t1)));
  temp _tags_buf v_tags_buf_scratch;
  temp _t'17 (Vint (Int.repr (len (tags td))));
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
  remember (if eq_dec (Int.repr tag_mode) 0%int
                  then len (tags td)
                  else len (tags td) + 1 - Int.unsigned t1) as tags_count.
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
  EX j : Z, 
  let (overall_length, lens) :=
      (match der_write_tags_loop1
               (Z.to_nat j) [] 
               (sublist (len ts - j) (len ts) ts) struct_len [] with
        | inr (_, p) => match p with (l, ls) => (encoded l, ls) end
        | _ => (struct_len, [])
      end) in
  PROP (0 <= j <= tags_count)
  LOCAL (
  temp _tags v_tags_buf_scratch;  
  temp _i (Vint (Int.repr tags_count - Int.repr j - 1)%int);
  temp _overall_length (Vint (Int.repr overall_length));
  temp _tags_count (Vint (Int.repr tags_count));
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
               (default_val (tarray tint (16 - j))
                            ++ (map Vint (map Int.repr lens))) 
               v_lens; 
       data_at_tags;
 (* data_at Tsh type_descriptor_s (r, (r0, (r1, (r2, (Vint (Int.repr (len (tags td))), m3))))) td_p; *)
  data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
  func_ptr' dummy_callback_spec cb;
  data_at_ Tsh enc_key_s app_key;
  valid_pointer cb;
  valid_pointer nullval))%assert 

 break:
 (let (overall_length, lens) :=
      match der_write_tags_loop1 (length (tags td)) [] (tags td) struct_len [] with
        | inr (_, p) => match p with (l, lens) =>
          (encoded l, lens) end
        | _ => (struct_len, [])
      end in
  PROP ()
  LOCAL (temp _tags v_tags_buf_scratch;
  temp _i Vzero;
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
  SEP (data_at Tsh (tarray tint 16) (map Vint (map Int.repr lens)) 
               v_lens; (* changed *)
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
    Exists 0.
    autorewrite with sublist.
    unfold der_write_tags_loop1.
    break_let.
    simpl in Heqp.
    inversion Heqp.
    subst.
    entailer!.
    { generalize H3.
      repeat break_if;
        pose proof (Zlength_nonneg (tags td));
      intro I;
      eapply repr_neq_e in I; split;
      strip_repr. }
    apply derives_refl.
  +  
    Intros j.
    break_let.
    forward_if.
    erewrite Heqdata_at_tags.
    destruct (eq_dec (Int.repr tag_mode) 0%int).
 ++ forward.
    entailer!.
    strip_repr.
    admit.
    admit.
    erewrite app_Znth1.
    erewrite zlist_hint_db.Znth_map_Vint.
    entailer!.
    all: auto;
    autorewrite with sublist list;
    try nia.
    1-2: admit.
    erewrite app_Znth1.
    strip_repr.
    erewrite zlist_hint_db.Znth_map_Vint.
    remember ( (Znth (tags_count - j - 1) ((map Int.repr ts)))) as fi.
    forward_call (fi, Int.repr z, nullval, nullval, Int.zero).
    rewrite_if_b.
    unfold Frame.
  instantiate (1 :=
                 [data_at Tsh (tarray tint 16) (default_val (tarray tint (16 - j)) 
                                                            ++ map Vint (map Int.repr l))
                          v_lens;
   data_at Tsh (tarray tuint 16)
     (map Vint (map Int.repr (tags td))
          ++ default_val (tarray tuint (16 - len (tags td))))
     v_tags_buf_scratch ;
   (* data_at Tsh type_descriptor_s (r, (r0, (r1, (r2, (Vint (Int.repr (len (tags td))), m3)))))
     td_p ; *)
   data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td)))
     (get_tags (r, (r0, (r1, (r2, (Vint (Int.repr (len (tags td))), m3)))))) ; 
   func_ptr' dummy_callback_spec cb ; data_at_ Tsh enc_key_s app_key ; 
   valid_pointer cb]).
    unfold fold_right_sepcon.
    entailer!. 
    forward.
    admit.
    forward.
    admit.
    entailer!.
    erewrite upd_Znth_same;
       inversion Heqp;
    unfold default_val; cbn; try nia.
    admit. (* add lemma *)
    repeat rewrite_if_b.
    forward_if.
    abbreviate_semax.
    forward.
    erewrite upd_Znth_same in H6.
    entailer!.
    assert (exists e, der_write_TL_m
                   (Znth (len (tags td) - j - 1) 
                         (map Int.repr (tags td)))
                   (Int.repr z) 0 0%int [] = inl e) as E by admit. (* from H6 *)
    destruct E as [err  E].
    clear H6.
    assert (der_write_tags_loop1 (Z.to_nat (len (tags td) - j - 1))
                                 [] (tags td) z [] = inl err) as EE by admit.
                                  
    unfold der_write_tags.
    assert (der_write_tags_loop1 ((length (tags td)))
                                 [] (tags td) struct_len [] = inl err) as EEE by admit.
    unfold evalErrW.
    cbn. 
    break_if; auto.
    break_match; auto.
    generalize Heqo.
    break_if.
    admit. (* contradiction  with tag_mode = 0 *)
    erewrite EEE.
    congruence.
    admit.
    admit.
    rewrite_if_b.
    repeat forward.   
    remember (Int.repr
                match
                  evalErrW (Der_write_TL_m.der_write_TL_m fi (Int.repr struct_len) 0 0%int) []
                with
                | Some {| encoded := v0 |} => v0
                | None => -1
                end) as res.
    Exists (j + 1).
    rewrite_if_b.
    entailer!.
    split. 
    erewrite upd_Znth_same in H6.
    admit.
    unfold default_val; cbn.
    nia.
    split.
    do 2 f_equal.
    nia.
    erewrite upd_Znth_same.
    (* why struct len??? *)
    admit.
    unfold default_val; cbn; nia.
    ++ admit. (* tag_mode <> 0 *)
  + forward_if.
    forward.
    (* 3d loop *)
    forward_loop ( 
  EX i : Z,
  PROP ( 0 <= i <= len (tags td))
  LOCAL (temp _i (Vint (Int.repr 0)); temp _tags v_tags_buf_scratch;
  temp _overall_length (Vint (Int.repr struct_len));
  temp _tags_count (Vint (Int.repr (len (tags td))));
  temp _t'17 (Vint (Int.repr (len (tags td)))); lvar _lens (tarray tint 16) v_lens;
  lvar _tags_buf_scratch (tarray tuint 16) v_tags_buf_scratch; temp _sd td_p;
  temp _struct_length (Vint (Int.repr struct_len)); temp _tag_mode (Vint (Int.repr tag_mode));
  temp _last_tag_form (Vint (Int.repr last_tag_form)); temp _tag (Vint (Int.repr tag));
  temp _cb cb; temp _app_key app_key)
  SEP (data_at_ Tsh (tarray tint 16) v_lens;
  data_at Tsh (tarray tuint 16)
    (map Vint (map Int.repr (tags td)) ++ default_val (tarray tuint (16 - len (tags td))))
    v_tags_buf_scratch;
  data_at Tsh type_descriptor_s (r, (r0, (r1, (r2, (Vint (Int.repr (len (tags td))), m3))))) td_p;
  data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
  func_ptr' dummy_callback_spec cb; data_at_ Tsh enc_key_s app_key; valid_pointer cb;
  valid_pointer nullval))%assert break: 
  (PROP ( )
  LOCAL (temp _i (Vint (Int.repr 0)); temp _tags v_tags_buf_scratch;
  temp _overall_length (Vint (Int.repr struct_len));
  temp _tags_count (Vint (Int.repr (len (tags td))));
  temp _t'17 (Vint (Int.repr (len (tags td)))); lvar _lens (tarray tint 16) v_lens;
  lvar _tags_buf_scratch (tarray tuint 16) v_tags_buf_scratch; temp _sd td_p;
  temp _struct_length (Vint (Int.repr struct_len)); temp _tag_mode (Vint (Int.repr tag_mode));
  temp _last_tag_form (Vint (Int.repr last_tag_form)); temp _tag (Vint (Int.repr tag));
  temp _cb cb; temp _app_key app_key)
  SEP (data_at_ Tsh (tarray tint 16) v_lens;
  data_at Tsh (tarray tuint 16)
    (map Vint (map Int.repr (tags td)) ++ default_val (tarray tuint (16 - len (tags td))))
    v_tags_buf_scratch;
  data_at Tsh type_descriptor_s (r, (r0, (r1, (r2, (Vint (Int.repr (len (tags td))), m3))))) td_p;
  data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
  func_ptr' dummy_callback_spec cb; data_at_ Tsh enc_key_s app_key; valid_pointer cb;
  valid_pointer nullval)).
    ++ forward.
       Exists 0.
       entailer!.
    ++ Intro i.
      forward_if. 
      forward_if
        (temp _t'4 (if eq_dec (Int.repr last_tag_form) 0%int 
                        then (Val.of_bool
                               (Int.repr 0 < Int.repr (len (tags td) - 1))%int)
                        else Vone)).
      forward.
      rewrite_if_b.
      entailer!.
      forward.
      rewrite_if_b.
      entailer!.
      repeat forward.
      entailer!.
      admit.
      admit.
      remember (force_int ((Znth 0
          (map Vint (map Int.repr (tags td)) ++
               default_val (tarray tuint (16 - len (tags td))))))) as t6.

      remember (force_int 
                  (Znth 0 (default_val (nested_field_type (tarray tint 16) []))))
        as t7.
    forward_call (t6, t7, cb, app_key, 
                  (if eq_dec (Int.repr last_tag_form) 0%int
                   then (if (0 <? (len (tags td) - 1)) then 1 else 0)
                   else 1)%int).
    rewrite_if_b.
    unfold Frame.
    instantiate (1 :=
                [data_at_ Tsh (tarray tint 16) v_lens ;
   data_at Tsh (tarray tuint 16)
     (map Vint (map Int.repr (tags td)) ++
          default_val (tarray tuint (16 - len (tags td))))
     v_tags_buf_scratch;
   data_at Tsh type_descriptor_s
           (r, (r0, (r1, (r2, (Vint (Int.repr (len (tags td))), m3)))))
     td_p ;
   data_at Tsh (tarray tuint (len (tags td))) 
           (map Vint (map Int.repr (tags td))) tags_p;
   valid_pointer nullval]).
    unfold fold_right_sepcon.
    entailer!.
    admit. (* change compspecs change_compspecs CompSpecs. *)
    forward.
    abbreviate_semax.
    forward_if.
    forward.
    forward.
    Exists (i + 1).
    repeat rewrite_if_b.
    entailer!.
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
