Require Import Coq.Program.Basics.
Require Import Clight.ptrs.
Require Import StructTact.StructTactics.
Require Import VST.floyd.proofauto.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope program_scope.

Definition ptr_test_spec : ident * funspec :=
  DECLARE _ptr_test
    WITH sh: share,
         b1 : block, b2 : block, b3 : block,
         ofs1 : ptrofs, ofs2 : ptrofs, ofs3 : ptrofs,
         c1 : int, c2 : int                                                                    
    PRE [_ptr1 OF (tptr tschar), _ptr2 OF (tptr (tptr tschar))]
      PROP (readable_share sh)
      LOCAL (temp _ptr1 (Vptr b1 ofs1); 
            temp _ptr2 (Vptr b2 ofs2))
      SEP (data_at sh  (tschar) (Vint c1) (Vptr b1 ofs1);  
          data_at sh  (tschar) (Vint c2) (Vptr b1 ofs3);
          data_at sh (tptr tschar) (Vptr b1 ofs3) (Vptr b2 ofs2))
    POST [tint]
      PROP ()
      LOCAL (temp ret_temp Vzero)
      SEP (data_at sh (tschar) (Vint c1) (Vptr b1 ofs1);  
          data_at sh (tschar) (Vint c2) (Vptr b1 ofs3);
          data_at sh (tptr tschar) (Vptr b1 ofs3) (Vptr b2 ofs2)).

Definition Gprog := ltac:(with_library prog [ptr_test_spec]).

Lemma body_str_test: semax_body Vprog Gprog f_ptr_test ptr_test_spec.
Proof.
  start_function.
  forward.
  forward_if.
  unfold test_order_ptrs.
  unfold sameblock.
  destruct peq; [simpl|contradiction].
  eapply andp_right.
  - assert ( data_at sh tschar (Vint c1) (Vptr b1 ofs1) *
             data_at sh tschar (Vint c2) (Vptr b1 ofs3) *
             data_at sh (tptr tschar) (Vptr b1 ofs3) (Vptr b2 ofs2)
                     |-- valid_pointer (Vptr b1 ofs1)) by entailer!.
    pose proof (valid_pointer_weak (Vptr b1 ofs1)).
    eapply derives_trans with (Q := valid_pointer (Vptr b1 ofs1)).
    eassumption.
    eapply (valid_pointer_weak (Vptr b1 ofs1)).
  - erewrite sepcon_assoc.
    assert ( 
        data_at sh tschar (Vint c2) (Vptr b1 ofs3) *
        data_at sh tschar (Vint c1) (Vptr b1 ofs1) *
        data_at sh (tptr tschar) (Vptr b1 ofs3) (Vptr b2 ofs2)
                |-- valid_pointer (Vptr b1 ofs3)) by entailer!.
    pose proof (valid_pointer_weak (Vptr b1 ofs3)).
    eapply derives_trans with (Q := valid_pointer (Vptr b1 ofs3)).
    erewrite pull_left_special.
    erewrite <- sepcon_assoc.
    eassumption.
    eapply (valid_pointer_weak (Vptr b1 ofs3)).
    - forward.
    - forward.
Qed.

Definition ptr_test_2_fun_spec (ofs1 ofs2 : ptrofs) :=
  if Ptrofs.unsigned ofs1 <=? Ptrofs.unsigned ofs2
  then 1
  else 2.


Definition ptr_test_2_spec : ident * funspec :=
  DECLARE _ptr_test_2
    WITH b : block, ptr1 : ptrofs, ptr2 : ptrofs,
         sh : share, ch1 : Z, ch2 : Z
    PRE [_ptr1 OF (tptr tschar), _ptr2 OF (tptr tschar)]
      PROP(readable_share sh)
      LOCAL(temp _ptr1 (Vptr b ptr1);
            temp _ptr2 (Vptr b ptr2))
      SEP(data_at sh tschar (Vint (Int.repr ch1)) (Vptr b ptr1);
          data_at sh tschar (Vint (Int.repr ch2)) (Vptr b ptr2))
    POST [tint]
      PROP()
      LOCAL(temp ret_temp (Vint (Int.repr (ptr_test_2_fun_spec ptr1 ptr2))))
      SEP(data_at sh tschar (Vint (Int.repr ch1)) (Vptr b ptr1);
          data_at sh tschar (Vint (Int.repr ch2)) (Vptr b ptr2)).

Definition Gprog_2 := ltac:(with_library prog [ptr_test_2_spec]).

Lemma typed_true_ptr_le : forall b ptr1 ptr2, 
        typed_true tint (force_val (sem_cmp_pp Cle (Vptr b ptr1) (Vptr b ptr2))) ->
        Ptrofs.unsigned ptr1 <=? Ptrofs.unsigned ptr2 = true.
Proof.
  intros.
  unfold typed_true, force_val, sem_cmp_pp in H.
  unfold Archi.ptr64, strict_bool_val in H.
  simpl in H.
  destruct eq_block in H; [simpl in H|contradiction].
  unfold negb, Ptrofs.ltu in H.
  destruct zlt in H; simpl in H; try discriminate.
  apply Z.ge_le in g.
  apply Zle_imp_le_bool.
  assumption.
Qed.

Lemma typed_false_ptr_le : forall b ptr1 ptr2, 
        typed_false tint (force_val (sem_cmp_pp Cle (Vptr b ptr1) (Vptr b ptr2))) ->
        Ptrofs.unsigned ptr2 <? Ptrofs.unsigned ptr1 = true.
Proof.
  intros.
  unfold typed_false, force_val, sem_cmp_pp in H.
  unfold Archi.ptr64, strict_bool_val in H.
  simpl in H.
  destruct eq_block in H; [simpl in H|contradiction].
  unfold negb, Ptrofs.ltu in H.
  destruct zlt in H; simpl in H; try discriminate.
  apply Fcore_Zaux.Zlt_bool_true.
  assumption.
Qed.

Lemma body_ptr_test_2: semax_body Vprog Gprog_2 f_ptr_test_2 ptr_test_2_spec.
Proof.
  start_function.
  forward_if.
  unfold test_order_ptrs.
  unfold sameblock.
  destruct peq; [simpl|contradiction].
  apply andp_right.
  -
    assert (data_at sh tschar (Vint (Int.repr ch1)) (Vptr b ptr1) * 
            data_at sh tschar (Vint (Int.repr ch2)) (Vptr b ptr2) 
                    |-- valid_pointer (Vptr b ptr1)) by entailer!.
    pose proof (valid_pointer_weak (Vptr b ptr1)).
    apply derives_trans with (Q := valid_pointer (Vptr b ptr1)); assumption.
  -
    assert (data_at sh tschar (Vint (Int.repr ch1)) (Vptr b ptr1) * 
            data_at sh tschar (Vint (Int.repr ch2)) (Vptr b ptr2) 
                    |-- valid_pointer (Vptr b ptr2)) by entailer!.
    pose proof (valid_pointer_weak (Vptr b ptr2)).
    apply derives_trans with (Q := valid_pointer (Vptr b ptr2)); assumption.
  - forward.
    pose proof typed_true_ptr_le b ptr1 ptr2 H.
    unfold ptr_test_2_fun_spec.
    rewrite H4.
    entailer!.
  - forward.
    pose proof typed_false_ptr_le b ptr1 ptr2 H.
    unfold ptr_test_2_fun_spec.
    rewrite Z.leb_antisym.
    rewrite H4.
    simpl.
    entailer!.
Qed.  
  
Require Import strtoimax_part.

(* int asn_strtoimax_lim(const char *str, const char **end, int *intp) {

    int sign = 1;

    if(str >= *end) return 0;

    switch( *str) {
    case '-':
        sign = -1;
        /* FALL THROUGH */
    case '+':
        str++;
        if(str >= *end) {
            *end = str;
            return 1;
        }
    }

    *end = str;
    *intp = sign;
    return 2;
}
 *)

Definition strtoimax_part_fun_spec (str fin : ptrofs) (ls : list byte) :=
  if Ptrofs.unsigned fin <=? Ptrofs.unsigned str
  then 0
  else       
    match ls with
    | [] => 3 
    | [ch] => if orb (Byte.eq ch (Byte.repr 43)) (Byte.eq ch (Byte.repr 45))
              then if Ptrofs.unsigned fin <=? Ptrofs.unsigned (Ptrofs.add str Ptrofs.one)
                   then 1
                   else 2
              else 2
    | _ => 2
    end. 

Definition strtoimax_part_spec : ident * funspec :=
  DECLARE _asn_strtoimax_lim
    WITH str_b : block, str_ofs : ptrofs,
         end_b : block, end_ofs : ptrofs,
         end'_b : block, end'_ofs : ptrofs,
         intp_b : block, intp_ofs : ptrofs,
         sh : share, sh' : share,
         contents : list byte,
         ch : val,
         sign : val
    PRE [_str OF (tptr tschar), _end OF (tptr (tptr tschar)), _intp OF (tptr tint)]
      PROP (readable_share sh; 
            writable_share sh';
            str_b = end'_b;
            (Ptrofs.unsigned str_ofs < Ptrofs.unsigned end'_ofs) ->
            (Vptr str_b str_ofs <> nullval))
      LOCAL (temp _str (Vptr str_b str_ofs);
             temp _end (Vptr end_b end_ofs); 
             temp _intp (Vptr intp_b intp_ofs))
      SEP (
        data_at sh tschar ch (Vptr end'_b end'_ofs);
           data_at sh (tarray tschar (Zlength contents))
                   (map Vbyte contents) (Vptr str_b str_ofs);
           data_at sh' (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs))
    POST [tint]
      PROP()
      LOCAL (temp ret_temp ((Vint ∘ Int.repr) 
                           (strtoimax_part_fun_spec str_ofs end'_ofs contents)))
      SEP (
        data_at sh tschar ch (Vptr end'_b end'_ofs);
           data_at sh (tarray tschar (Zlength contents))
                   (map Vbyte contents) (Vptr str_b str_ofs);
           let i := strtoimax_part_fun_spec str_ofs end'_ofs contents in
           if i =? 0 
           then data_at sh' (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs)
           else 
             if i =? 1 
             then data_at sh' (tptr tschar) 
                          (Vptr str_b (Ptrofs.add str_ofs Ptrofs.one))
                          (Vptr end_b end_ofs) 
             else 
               if i =? 2 
               then
                 data_at sh' (tptr tschar) 
                         (Vptr str_b (Ptrofs.add str_ofs Ptrofs.one))
                         (Vptr end_b end_ofs) *
                 data_at sh' tint sign (Vptr intp_b intp_ofs)
               else data_at sh' (tptr tschar) (Vptr end'_b end'_ofs) 
                                    (Vptr end_b end_ofs)).

Definition Gprog_3 := ltac:(with_library prog [strtoimax_part_spec]).

Lemma body_strtoimax_part : semax_body Vprog Gprog_3 f_asn_strtoimax_lim strtoimax_part_spec.
  Proof.
    start_function.
    repeat forward.
    forward_if.
    unfold test_order_ptrs.
    unfold sameblock.
    destruct peq; [simpl|contradiction].
    eapply andp_right.
    erewrite sepcon_assoc.
    assert (data_at sh (tarray tschar (Zlength contents)) 
                    (map Vbyte contents) (Vptr end'_b str_ofs) *
            data_at sh tschar ch (Vptr end'_b end'_ofs) *
            data_at sh' (tptr tschar) (Vptr end'_b end'_ofs) (Vptr end_b end_ofs)
                    |-- valid_pointer (Vptr end'_b str_ofs)).
    admit. (* need 0 < Zlength contents *) 
    pose proof (valid_pointer_weak (Vptr end'_b str_ofs)).
    eapply derives_trans with (Q := valid_pointer (Vptr end'_b str_ofs)).
    erewrite pull_left_special.
    erewrite <- sepcon_assoc.
    eassumption.
    eapply (valid_pointer_weak (Vptr end'_b str_ofs)).
    assert ( data_at sh tschar ch (Vptr end'_b end'_ofs) *
             data_at sh (tarray tschar (Zlength contents))
                     (map Vbyte contents) (Vptr end'_b str_ofs) *
             data_at sh' (tptr tschar) (Vptr end'_b end'_ofs)
                     (Vptr end_b end_ofs)
                     |-- valid_pointer (Vptr end'_b end'_ofs)) by entailer!.
    pose proof (valid_pointer_weak (Vptr end'_b end'_ofs)).
    eapply derives_trans with (Q := valid_pointer (Vptr end'_b end'_ofs)).
    eassumption.
    eapply (valid_pointer_weak (Vptr end'_b end'_ofs)).
    forward.
    entailer!.
    unfold strtoimax_part_fun_spec.
    admit. (* true from H1 *)
    assert (strtoimax_part_fun_spec str_ofs end'_ofs contents =? 0 = true) by admit.
    (* from H1 *)
    rewrite H.
    entailer.
    
    Search data_at tarray. 
    Variable c : byte.
    Variable tl : list byte.
    replace (map Vbyte contents) with ([Vbyte c] ++ (map Vbyte tl)).
    erewrite split2_data_at_Tarray_app with (mid := 1).
    Intros.
    Search data_at 1.
    erewrite data_at_singleton_array_eq.
    instantiate (1 := Vbyte c).
    forward.
    admit.

    
    
  


  
