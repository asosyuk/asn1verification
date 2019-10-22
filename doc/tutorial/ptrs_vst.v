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
  then 0
  else 2.

  
Definition ptr_test_2_spec : ident * funspec :=
  DECLARE _ptr_test_2
    WITH sh: share,
         b1 : block, b2 : block, b3 : block,
         ofs1 : ptrofs, ofs2 : ptrofs, ofs3 : ptrofs,
         c1 : int, c2 : int
    PRE [_ptr1 OF (tptr tschar), _ptr2 OF (tptr (tptr tschar))]
      PROP (readable_share sh;
            b1 = b3)
      LOCAL (temp _ptr1 (Vptr b1 ofs1); 
             temp _ptr2 (Vptr b2 ofs2))
      SEP (data_at sh  (tschar) (Vint c1) (Vptr b1 ofs1);  
           data_at sh  (tschar) (Vint c2) (Vptr b3 ofs3);
           data_at sh (tptr tschar) (Vptr b3 ofs3) (Vptr b2 ofs2))
    POST [tint]
      PROP ()
      LOCAL (temp ret_temp ((Vint ∘ Int.repr)(ptr_test_2_fun_spec ofs1 ofs3)))
      SEP (data_at sh (tschar) (Vint c1) (Vptr b1 ofs1);  
           data_at sh (tschar) (Vint c2) (Vptr b3 ofs3);
           data_at sh (tptr tschar) (Vptr b3 ofs3) (Vptr b2 ofs2)).

Lemma body_str_test_2: semax_body Vprog Gprog f_ptr_test ptr_test_spec.
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
  
  
  

  
