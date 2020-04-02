Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Clightgen_struct_assign.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition complex_int_t  := (Tstruct _complex_int_s noattr).
Definition complex_int_rt := reptype complex_int_t.

Definition complex_int_zero_ptr_Cspec : ident * funspec :=
  DECLARE _complex_int_zero_ptr
    WITH sh : share, _res : val
    PRE [ __res OF (tptr complex_int_t) ]
      PROP  (writable_share sh)
      LOCAL (temp __res _res)
      SEP   (data_at_ sh complex_int_t _res)
    POST [ tvoid ]
      PROP  ()
      LOCAL ()
      SEP   (
        data_at sh complex_int_t (Vint (Int.repr 0), Vint (Int.repr 0)) _res
      )
.

Definition complex_int_zero_ptr_eva_Cspec : ident * funspec :=
  DECLARE _complex_int_zero_ptr_eva
    WITH sh : share, _res : val
    PRE [ __res OF (tptr complex_int_t) ]
      PROP  (writable_share sh)
      LOCAL (temp __res _res)
      SEP   (data_at_ sh complex_int_t _res)
    POST [ tvoid ]
      PROP  ()
      LOCAL ()
      SEP   (
        data_at sh complex_int_t (Vint (Int.repr 0), Vint (Int.repr 0)) _res
      )
.

Definition Gprog : funspecs := ltac:(with_library prog [ complex_int_zero_ptr_Cspec]).

Require Import StructNormalizer.

Definition normalize_function f :=
  mkfunction (fn_return f) (fn_callconv f) (fn_params f) (fn_vars f) ((900%positive, tint) :: (901%positive, tint) :: nil)
             (struct_normalize (fn_body f) composites).

Eval simpl in struct_normalize (fn_body f_complex_int_zero_ptr) composites.
Eval simpl in (fn_body f_complex_int_zero_ptr_eva).

Lemma complex_int_zero_ptr_correct: semax_body Vprog Gprog
                                               (normalize_function f_complex_int_zero_ptr)
                                               complex_int_zero_ptr_Cspec.
Proof.
  start_function.
  repeat forward.
  entailer!.
Qed.

Lemma complex_int_zero_ptr_eva_correct: semax_body Vprog Gprog f_complex_int_zero_ptr_eva complex_int_zero_ptr_eva_Cspec.
Proof.
  start_function.
  repeat forward.
  entailer!.
Qed.
