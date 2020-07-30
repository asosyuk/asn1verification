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
       then data_at_ Tsh (tarray tuint 16) v_tags_buf_scratch
       else 
         data_at Tsh (tarray tuint 16) 
                ((if ((Int.repr tag_mode == (Int.neg (Int.repr 1)))%int &&
               (negb (Int.eq (Int.repr (Zlength (tags td))) Int.zero)))%bool
                then upd_Znth 0 (map Vint (map Int.repr (tags td))) (Vint (Int.repr tag)) 
                else (Vint (Int.repr tag) :: (map Vint (map Int.repr (tags td))))) ++
                default_val (tarray tuint (16 - (len (tags td)) - 1))) 
               v_tags_buf_scratch;
  data_at Tsh type_descriptor_s
          (r, (r0, (r1, (tags_p, (Vint (Int.repr (len (tags td))), m3))))) td_p;
  func_ptr' dummy_callback_spec cb; data_at_ Tsh enc_key_s app_key; 
  valid_pointer cb)).
 (* **
  repeat forward.
  forward_if (temp _t'1 (Vint t1));
    repeat forward; try rewrite_if_b; try entailer!.
  1-2: admit.
  forward_if (temp _t'2 (Vint t1)); 
    repeat forward; try rewrite_if_b; try entailer!.
  1-2: admit.
  repeat break_if; try rep_omega.
  all: unfold Int.neg;
    try rewrite Int.signed_repr;
  try rewrite Int.unsigned_repr;
  autorewrite with norm;
  try rep_omega.
  erewrite Int.signed_one;
  rep_omega.
  (* loop 1 *)
  deadvars!.
  cbn in H2.
  rewrite H2. 
  remember (Int.unsigned t1) as stag_offset.
  remember (tags td) as tags.
  forward_loop  (
  EX i : Z,
  PROP (0 <= i <= len tags + 1 - stag_offset) 
  LOCAL (temp _i (Vint (Int.repr (i + 1)));
  temp _stag_offset (Vint (Int.repr (- (1)) + t1))%int;
  temp _tags_count (Vint (Int.repr (len tags + 1) - t1)%int); 
  temp _tags_buf v_tags_buf_scratch;
  temp _t'17 (Vint (Int.repr (len tags)));
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
       data_at Tsh (tarray tuint (len tags)) 
               (map Vint (map Int.repr tags)) tags_p;
       data_at Tsh (tarray tuint 16) 
       (if ((Int.repr tag_mode == (Int.neg (Int.repr 1)))%int &&
               (negb (Int.eq (Int.repr (len tags)) Int.zero)))%bool 
        then map Vint (map Int.repr (tag :: sublist 1 (i + 1) tags))
                      ++ default_val (tarray tuint (16 - i - 1)) 
        else (map Vint (map Int.repr (tag :: sublist 0 i tags))) 
         ++ default_val (tarray tuint (16 - i - 1))) 
       v_tags_buf_scratch;
  data_at Tsh type_descriptor_s 
          (r, (r0, (r1, (tags_p, (Vint (Int.repr (len tags)), m3))))) td_p;
  func_ptr' dummy_callback_spec cb;
  data_at_ Tsh enc_key_s app_key; 
  valid_pointer cb))%assert
               
break:  
 (PROP ()
  LOCAL (temp _i (Vint (Int.repr (len tags + 1) - t1)%int);
  temp _stag_offset (Vint (Int.repr (- (1)) + t1))%int;
  temp _tags_count (Vint (Int.repr (len tags + 1) - t1)%int); 
  temp _tags_buf v_tags_buf_scratch;
  temp _t'17 (Vint (Int.repr (len tags)));
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
       data_at Tsh (tarray tuint (len tags))
               (map Vint (map Int.repr tags)) tags_p;
       data_at Tsh (tarray tuint 16) 
                ((if ((Int.repr tag_mode == (Int.neg (Int.repr 1)))%int &&
               (negb (Int.eq (Int.repr (Zlength (tags))) Int.zero)))%bool
                then upd_Znth 0 (map Vint (map Int.repr tags)) (Vint (Int.repr tag)) 
                else (Vint (Int.repr tag) :: (map Vint (map Int.repr tags)))) ++
                default_val (tarray tuint (16 - (len tags) - 1))) 
               v_tags_buf_scratch;
  data_at Tsh type_descriptor_s (r, (r0, (r1, (tags_p, (Vint (Int.repr (len tags)), m3))))) td_p;
  func_ptr' dummy_callback_spec cb; data_at_ Tsh enc_key_s app_key; valid_pointer cb)). 
  + forward.
    Exists 0.
    entailer!.
    Ltac strip_repr :=
      autorewrite with norm;
      unfold Int.add; unfold Int.mul; unfold Int.neg;
      unfold Int.sub;
      try erewrite Int.unsigned_zero;
      try erewrite Int.unsigned_one;
      repeat rewrite Int.unsigned_repr;  
      repeat rewrite Int.signed_repr;     
      try rep_omega; auto. 
    repeat break_if; strip_repr.
    repeat break_if;
      try erewrite sublist_nil;
      repeat erewrite upd_Znth_unfold;
      try erewrite Int.unsigned_zero;
      try erewrite Int.unsigned_one;
      pose proof (Zlength_nonneg (tags td));
      cbn; try nia; entailer!.    
  + Intro i.
    forward_if.
    assert (i + 1 < len tags + 1 - Int.unsigned t1) as S.
    { generalize H5.
      subst.
      repeat break_if; strip_repr. }
    forward.
    unfold isptr in H.
    destruct tags_p; try contradiction. 
    assert ((0 <= Int.unsigned (Int.repr (i + 1) +
                               (Int.repr (-1) + t1))%int
             < len tags)) as S1.
    { subst.
      repeat break_if;
        normalize;
        try rep_omega.
      replace 1%int with (Int.repr 1) by auto with ints.
      normalize.
      erewrite Int.unsigned_one in *.
      rep_omega. }
    forward.
    entailer!.
    repeat break_if; strip_repr.
    forward.
    entailer!.
    forward.
    Exists (i + 1).
    entailer!.
    break_if.
    { replace (Int.unsigned (Int.repr (i + 1) + (Int.repr (-1) + 1))%int)
        with (i + 1) in *.
      erewrite upd_Znth_unfold.
      replace (sublist 0 (i + 1)
       ((Vint (Int.repr tag) ::
              map Vint (map Int.repr (sublist 1 (i + 1) (tags td)))) ++
        default_val (tarray tuint (16 - i - 1)))) with
          ((Vint (Int.repr tag) ::
                 map Vint (map Int.repr (sublist 1 (i + 1) (tags td))))).
      replace ((len
          ((Vint (Int.repr tag) ::
                 map Vint (map Int.repr (sublist 1 (i + 1) (tags td)))) ++
           default_val (tarray tuint (16 - i - 1))))) with 16.
      autorewrite with sublist.
      assert (sublist 1 (16 - Z.succ i) (default_val (tarray tuint (16 - i - 1)))
        =  (default_val (tarray tuint (16 - i - 1 - 1)))) as B.
      { 
      unfold default_val; simpl.
        erewrite sublist_list_repeat.
         replace (16 - Z.succ i - 1) with (16 - i - 1 - 1) by nia.
         all: try nia.
      auto. }
      setoid_rewrite B.
      assert ((map Vint (map Int.repr (sublist 1 (i + 1) (tags td)))) ++
     [Vint (Int.repr (Znth (i + 1) (tags td)))] =
        (map Vint (map Int.repr (sublist 1 (i + 1 + 1) (tags td))))).
      replace [Vint (Int.repr (Znth (i + 1) (tags td)))] 
        with (map Vint (map Int.repr [Znth (i + 1) (tags td)])).
      do 2 erewrite <- map_app.
      do 2 f_equal.
      erewrite <- sublist_last_1.
      reflexivity.
      1-2: try nia.
      reflexivity.
      setoid_rewrite <- H1.
      replace (16 - (i + 1) - 1) with (16 - i - 1 - 1) by nia.
      erewrite app_assoc.
      entailer!.
      autorewrite with sublist.
      autorewrite with sublist.
      unfold default_val; simpl. rewrite Zlength_list_repeat; nia.
      erewrite sublist_app1.
      setoid_rewrite sublist_same with (lo := 0) (hi := i + 1).
      repeat f_equal.
      nia.
       all:
        try erewrite Int.unsigned_one in *;
      autorewrite with sublist;
      try nia.
        unfold default_val; simpl. rewrite Zlength_list_repeat; nia.
        unfold Int.add.
        normalize. }

    assert (upd_Znth (i + 1)
       ((Vint (Int.repr tag) :: map Vint (map Int.repr (sublist 0 i (tags td)))) ++
        default_val (tarray tuint (16 - i - 1)))
       (Vint
          (Int.repr (Znth (Int.unsigned (Int.repr (i + 1)
                                         + (Int.repr (-1) + 0))%int) (tags td)))) =
           ((Vint (Int.repr tag) :: map Vint (map Int.repr (sublist 0 (i + 1) (tags td)))) ++
         default_val (tarray tuint (16 - (i + 1) - 1)))).
    { erewrite upd_Znth_unfold.
      replace (sublist 0 (i + 1)
       ((Vint (Int.repr tag) :: map Vint (map Int.repr (sublist 0 i (tags td)))) ++
        default_val (tarray tuint (16 - i - 1)))) with
          ((Vint (Int.repr tag) :: map Vint (map Int.repr (sublist 0 i (tags td))))).
      replace ( (len
          ((Vint (Int.repr tag) :: map Vint (map Int.repr (sublist 0 i (tags td)))) ++
           default_val (tarray tuint (16 - i - 1))))) with 16.
      replace (sublist (i + 1 + 1) 16
       ((Vint (Int.repr tag) :: map Vint (map Int.repr (sublist 0 i (tags td)))) ++
        default_val (tarray tuint (16 - i - 1)))) 
        with (default_val (tarray tuint (16 - i - 1 - 1))).
      replace (Int.unsigned (Int.repr (i + 1) + (Int.repr (-1) + 0))%int) with (i).
      assert ((map Vint (map Int.repr (sublist 0 i (tags td)))) ++
     [Vint (Int.repr (Znth i (tags td)))] =
        (map Vint (map Int.repr (sublist 0 (i + 1) (tags td))))).
      replace [Vint (Int.repr (Znth i (tags td)))] 
        with (map Vint (map Int.repr [Znth i (tags td)])).
        try erewrite Int.unsigned_zero in *.

      do 2 erewrite <- map_app.
      do 2 f_equal.
      erewrite <- sublist_last_1.
      reflexivity.
      
      1-2: try nia.
      reflexivity.
      setoid_rewrite <- H1.
      replace (16 - (i + 1) - 1) with (16 - i - 1 - 1) by nia.
      erewrite app_assoc.
      auto.
      normalize.
      nia.
      erewrite sublist_app2.
      autorewrite with sublist.
      cbn -[sublist].
      erewrite sublist_list_repeat.
        try erewrite Int.unsigned_zero in *.
        replace (16 - i - 1 - 1)  with (16 - Z.succ i - 1) by nia.
         autorewrite with sublist.
      reflexivity.
       try erewrite Int.unsigned_zero in *.
       autorewrite with sublist.
       nia.
       all:  replace (Int.repr (len (tags td)) == 0)%int with false in * by admit;
        try erewrite Int.unsigned_zero in *;
      autorewrite with sublist;
      try nia.
      unfold default_val; simpl; rewrite Zlength_list_repeat; nia.
      setoid_rewrite sublist_same with (lo := 0) (hi := i + 1).
      reflexivity.
      nia.
       autorewrite with sublist;
      try nia.
         unfold default_val; simpl; rewrite Zlength_list_repeat; try nia. }
    erewrite H1.
    entailer!.
    forward.
    entailer!.
    remember  (if
            ((Int.repr tag_mode == Int.repr (- (1)))
               && negb (Int.repr (len (tags td)) == 0))%bool
           then 1
           else 0)%int as t1.
    assert (i + 1 =
       Int.signed
         (Int.repr (len (tags td) + 1) - t1)%int).
    { generalize H5.
      subst.
      break_if;
      strip_repr;
      try nia.
      intro.
      all: 
        try erewrite Int.unsigned_zero in *;
        try erewrite Int.unsigned_one in *;
        try nia. 
      admit.
      admit.
      
}
    erewrite H1.
    erewrite Int.repr_signed.
    auto.
    remember (if
            ((Int.repr tag_mode == Int.repr (- (1)))%int
               && negb (Int.repr (len (tags td)) == 0)%int)%bool
           then 1
           else 0) as t1.

    assert (i + 1  = Int.signed (Int.repr (len (tags td) + 1) - (Int.repr t1))%int).
    { generalize H5.
      subst.
      repeat break_if;
      strip_repr;
      try nia.
      all: try erewrite Int.unsigned_zero in *;
        try erewrite Int.unsigned_one in *;
        try nia. all: admit. }
    erewrite H1.
    break_if;
    normalize.
    { replace (Int.signed (Int.repr (len (tags td) + 1) - 1)%int)
              with (len (tags td)) by strip_repr.
      erewrite upd_Znth0_old.
      autorewrite with sublist list norm.
      replace i with (len (tags td)).
      repeat erewrite map_sublist.
      entailer!.
      admit. 
      admit.
      admit. }
    { replace i with (len (tags td)).
      erewrite sublist_same; try nia.
      entailer!; nia.
      admit. }
  + forward.
    rewrite_if_b.
    repeat f_equal.
    strip_repr.
    entailer!.
    admit.
  ** (* tag_mode = 0 *)
  repeat forward.
  rewrite_if_b.
  entailer!.
  **
  forward_if.
  forward.
  entailer!.
  admit.
  repeat forward.
  (* loop 2 *)
  forward_loop (PROP ( )
  LOCAL (temp _i
           (Vint
              (Int.repr
                 (if eq_dec (Int.repr tag_mode) 0
                  then len (tags td)
                  else (len (tags td) + 1 - Int.unsigned t1)%Z) - Int.repr 1)%int);
  temp _overall_length (Vint (Int.repr struct_len));
  temp _tags_count
    (Vint
       (Int.repr
          (if eq_dec (Int.repr tag_mode) 0%int
           then len (tags td)
           else len (tags td) + 1 - Int.unsigned t1)));
  temp _t'17 (Vint (Int.repr (len (tags td)))); lvar _lens (tarray tint 16) v_lens;
  lvar _tags_buf_scratch (tarray tuint 16) v_tags_buf_scratch; temp _sd td_p;
  temp _struct_length (Vint (Int.repr struct_len)); temp _tag_mode (Vint (Int.repr tag_mode));
  temp _last_tag_form (Vint (Int.repr last_tag_form)); temp _tag (Vint (Int.repr tag));
  temp _cb cb; temp _app_key app_key)
  SEP (data_at_ Tsh (tarray tint 16) v_lens; data_at_ Tsh (tarray tuint 16) v_tags_buf_scratch;
  data_at Tsh type_descriptor_s (r, (r0, (r1, (r2, (Vint (Int.repr (len (tags td))), m3))))) td_p;
  data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
  func_ptr' dummy_callback_spec cb; data_at_ Tsh enc_key_s app_key; valid_pointer cb)) break: (PROP()LOCAL()SEP()). 
  + repeat forward.
    entailer!.
    admit.
    entailer!.
  + forward_if.
    repeat forward.
  admit. (* tags_p should be a pointer *)
  entailer!.
  admit. *) 
  ** admit.
  ** admit.
  ** 
  forward_if.
  forward.
  entailer!.
  admit.
  entailer!.
  break_if; entailer!.
  repeat forward.
  (* loop 2 *) 
  forward_loop (
  EX j : Z,
  PROP (0 <= j <= len (tags td))
  LOCAL (
  temp _tags v_tags_buf_scratch;  
  temp _i
           (Vint
              (Int.repr
                 (if eq_dec (Int.repr tag_mode) 0
                  then len (tags td)
                  else (len (tags td) + 1 - Int.unsigned t1)%Z) - Int.repr j)%int);
  temp _overall_length (Vint (Int.repr struct_len));
  temp _tags_count
    (Vint
       (Int.repr
          (if eq_dec (Int.repr tag_mode) 0%int
           then len (tags td)
           else len (tags td) + 1 - Int.unsigned t1)));
  temp _t'17 (Vint (Int.repr (len (tags td)))); lvar _lens (tarray tint 16) v_lens;
  lvar _tags_buf_scratch (tarray tuint 16) v_tags_buf_scratch; temp _sd td_p;
  temp _struct_length (Vint (Int.repr struct_len)); temp _tag_mode (Vint (Int.repr tag_mode));
  temp _last_tag_form (Vint (Int.repr last_tag_form)); temp _tag (Vint (Int.repr tag));
  temp _cb cb; temp _app_key app_key)
  SEP (data_at_ Tsh (tarray tint 16) v_lens; 
       if eq_dec (Int.repr tag_mode) 0%int
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
         default_val (tarray tuint (16 - len (tags td) - 1))) v_tags_buf_scratch;
  data_at Tsh type_descriptor_s (r, (r0, (r1, (r2, (Vint (Int.repr (len (tags td))), m3))))) td_p;
  data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
  func_ptr' dummy_callback_spec cb;
  data_at_ Tsh enc_key_s app_key;
  valid_pointer cb;
  valid_pointer nullval))%assert 
               break:
 (PROP ( )
  LOCAL (temp _tags v_tags_buf_scratch;
  temp _i Vzero;
  temp _overall_length (Vint (Int.repr struct_len));
  temp _tags_count (Vint (Int.repr (len (tags td))));
  temp _t'17 (Vint (Int.repr (len (tags td)))); lvar _lens (tarray tint 16) v_lens;
  lvar _tags_buf_scratch (tarray tuint 16) v_tags_buf_scratch; temp _sd td_p;
  temp _struct_length (Vint (Int.repr struct_len)); temp _tag_mode (Vint (Int.repr tag_mode));
  temp _last_tag_form (Vint (Int.repr last_tag_form)); temp _tag (Vint (Int.repr tag));
  temp _cb cb; temp _app_key app_key)
  SEP (data_at_ Tsh (tarray tint 16) v_lens;
  data_at Tsh (tarray tuint 16)
    (map Vint (map Int.repr (tags td)) ++
         default_val (tarray tuint (16 - len (tags td))))
    v_tags_buf_scratch;
  data_at Tsh type_descriptor_s 
          (r, (r0, (r1, (r2, (Vint (Int.repr (len (tags td))), m3))))) td_p;
  data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
  func_ptr' dummy_callback_spec cb;
  data_at_ Tsh enc_key_s app_key;
  valid_pointer cb;
  valid_pointer nullval)).
  + repeat forward.
    entailer!.
    admit.
    Exists 1.
    entailer!.
    admit.
    entailer!.
    admit.
  + break_if.
    ++ Intro j.
    forward_if.
    forward.
    entailer!.
    admit.
    remember (force_int ((Znth (len (tags td) - j)
                 (map Vint (map Int.repr (tags td)) ++
                  default_val (tarray tuint (16 - len (tags td))))))) as fi.
    forward_call (fi, Int.repr struct_len, nullval, nullval, Int.zero).
    entailer!.
    f_equal.
    cbn.
    hint.
    admit.
    rewrite_if_b.
    unfold Frame.
    instantiate (1 := [data_at_ Tsh (tarray tint 16) v_lens ;
   data_at Tsh (tarray tuint 16)
     (map Vint (map Int.repr (tags td))
          ++ default_val (tarray tuint (16 - len (tags td))))
     v_tags_buf_scratch ;
   data_at Tsh type_descriptor_s (r, (r0, (r1, (r2, (Vint (Int.repr (len (tags td))), m3)))))
     td_p ;
   data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td)))
     (get_tags (r, (r0, (r1, (r2, (Vint (Int.repr (len (tags td))), m3)))))) ;
   func_ptr' dummy_callback_spec cb ; data_at_ Tsh enc_key_s app_key ; 
   valid_pointer cb]).
    unfold fold_right_sepcon.
    entailer!.
    forward.
    forward.
    entailer!.
    admit.
    forward_if.
    forward.
    hint.
    rewrite if_true by auto.
    clear Delta.
    entailer!.
    admit.
    admit. (* add valid_pointer nullval in LI *)
    repeat forward.
    remember (Int.repr
                match
                  evalErrW
                    (Der_write_TL_m.der_write_TL_m fi (Int.repr struct_len)
                       (if Val.eq nullval nullval then 0 else 32) 0%int) []
                with
                | Some {| encoded := v0 |} => v0
                | None => -1
                end) as res.
    Exists (j + 1).
    entailer!.
    split. 
    admit.
    split.
    do 2 f_equal.
    nia.
    admit.
    rewrite_if_b.
    entailer!.
    forward.
    entailer!.
    ++ admit.
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
