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
    PROP(
      0 <= Zlength (tags td) + 1 <= Int.max_unsigned;
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


Definition Gprog := ltac:(with_library prog [der_write_tags_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog (normalize_function f_der_write_tags composites)
                                     der_write_tags_spec.
Proof.
  start_function.
  unfold get_tags_count in H0.
  repeat break_let.
  forward.
  rewrite H0.
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
  remember (if eq_dec (Int.repr tag_mode) (Int.neg (Int.repr 1))
            then (if Int.eq (Int.repr (Zlength (tags td))) Int.zero 
                  then Int.zero else Int.one)
            else Int.zero) as t1.
  forward_if (temp _tags_count (Vint (Int.repr (len (tags td)) + 1 + t1)%int)).
  **
  repeat forward.
  forward_if ((temp _t'1
           (Vint (
                if eq_dec (Int.repr tag_mode) (Int.neg (Int.repr 1))
                then (if Int.eq (Int.repr (Zlength (tags td))) Int.zero 
                  then Int.zero else Int.one)
                else Int.zero))));
    repeat forward; try rewrite_if_b; try entailer!.
  forward_if (((temp _t'2
           (Vint (
                if eq_dec (Int.repr tag_mode) (Int.neg (Int.repr 1))
                then (if Int.eq (Int.repr (Zlength (tags td))) Int.zero 
                  then Int.zero else Int.one)
                else Int.zero))))); repeat forward; try rewrite_if_b; try entailer!.
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
  cbn in H1.
  rewrite H1. 
  remember (Int.unsigned t1) as stag_offset.
  forward_loop  (
  EX i : Z,
  PROP ()
  LOCAL (temp _i (Vint (Int.repr (i + 1)));
  temp _stag_offset (Vint (Int.repr (- (1)) + t1))%int;
  temp _tags_count (Vint (Int.repr (len (tags td) + 1) - t1)%int); 
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
       data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
       data_at Tsh (tarray tuint 16) 
       (if eq_dec (Int.repr tag_mode) (Int.neg (Int.repr 1)) 
        then upd_Znth 0 ((map Vint (map Int.repr (sublist 0 i (tags td))))
                      ++ default_val (tarray tuint (16 - i))) 
                                             (Vint (Int.repr tag)) 
        else (Vint (Int.repr tag) :: 
                   (map Vint (map Int.repr (sublist 0 i (tags td)))) 
         ++ default_val (tarray tuint (16 - i)))) 
       v_tags_buf_scratch;
  data_at Tsh type_descriptor_s (r, (r0, (r1, (tags_p, (Vint (Int.repr (len (tags td))), m3))))) td_p;
  func_ptr' dummy_callback_spec cb; data_at_ Tsh enc_key_s app_key; valid_pointer cb))%assert
               
break:  
 (PROP ()
  LOCAL (temp _i (Vint (Int.repr (len (tags td) + 1) - t1)%int);
  temp _stag_offset (Vint (Int.repr (- (1)) + t1))%int;
  temp _tags_count (Vint (Int.repr (len (tags td) + 1) - t1)%int); 
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
       data_at Tsh (tarray tuint (len (tags td))) (map Vint (map Int.repr (tags td))) tags_p;
       data_at Tsh (tarray tuint 16) 
                (if eq_dec (Int.repr tag_mode) (Int.neg (Int.repr 1)) 
                then upd_Znth 0 (map Vint (map Int.repr (tags td))) (Vint (Int.repr tag)) 
                else (Vint (Int.repr tag) :: (map Vint (map Int.repr (tags td))))) 
               v_tags_buf_scratch;
  data_at Tsh type_descriptor_s (r, (r0, (r1, (tags_p, (Vint (Int.repr (len (tags td))), m3))))) td_p;
  func_ptr' dummy_callback_spec cb; data_at_ Tsh enc_key_s app_key; valid_pointer cb)).
  + forward.
    Exists 0.
    entailer!.
    break_if.
    entailer!.
    erewrite upd_Znth_unfold.
    autorewrite with sublist.
    entailer!.
    all: admit.
  + Intro i.
    forward_if.
    forward.
    assert (isptr tags_p) as T by admit.
    unfold isptr in T.
    destruct tags_p; try contradiction.
    assert ((0 <= Int.unsigned (Int.repr (i + 1) + (Int.repr (-1) + t1))%int
             < len (map Int.repr (tags td)))) by admit.
    assert ((0 <= Int.unsigned (Int.repr (i + 1) + (Int.repr (-1) + t1))%int
             < len (tags td))) by admit.
    forward.
    entailer!.
    admit.
    rewrite if_false.
    forward.
    admit.
    forward.
    entailer!.
    admit.
    Exists (i + 1).
    entailer!.
    remember (if eq_dec (Int.repr tag_mode) (Int.repr (- (1)))
                    then if (Int.repr (len (tags td)) == 0)%int then 0%int else 1%int
                    else 0%int) as t1.
    all: admit.
 (*   

  **
  repeat forward.
  entailer!.
  admit. (* tags_p should be a pointer *)
  entailer!.
  admit.
  **
  forward_if.
  forward.
  entailer!.
  admit. (* fix spec *)
  repeat forward.
  (* loop 1 *) *)
Admitted.

End Der_write_tags.
