Require Import Clight.strlen_GNU.
Require Import Coq.Program.Basics ZArith Psatz.

Require Import VST.floyd.proofauto.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope program_scope.

Locate cstring.

Definition strlen_spec : ident * funspec :=
  DECLARE _strlen
    WITH sh: share, b : block, ofs : ptrofs, contents : list byte
    PRE [_s OF (tptr tschar)]
      PROP (readable_share sh;
            Ptrofs.unsigned ofs + Zlength contents + 1 < Ptrofs.modulus)
      LOCAL (temp _s (Vptr b ofs))
      SEP (cstring sh contents (Vptr b ofs))
    POST [ tuint ]
      PROP ()
      LOCAL (temp ret_temp ((Vptrofs ∘ Ptrofs.repr) (Zlength contents)))
      SEP (cstring sh contents (Vptr b ofs)).

Definition Gprog := ltac:(with_library prog [strlen_spec]).

Lemma body_strlen: semax_body Vprog Gprog f_strlen strlen_spec.
  Proof.
    start_function.

    forward.
    forward_loop 
      (EX i : Z, 
              PROP (0 <= i < Zlength contents + 1)
              LOCAL (temp _s (Vptr b (Ptrofs.add ofs (Ptrofs.repr i)));
                                temp _i (Vptrofs (Ptrofs.repr i)))
              SEP (cstring sh contents (Vptr b ofs)))
      break: (EX i : Z, PROP (i = Zlength contents)
                        LOCAL (temp _s (Vptr b (Ptrofs.add 
                                                  ofs (Ptrofs.repr (i + 1))));
                                         temp _i (Vptrofs (Ptrofs.repr i)))
                        SEP (cstring sh contents (Vptr b ofs))).
    all: unfold cstring in *.
    entailer.
    Exists 0.
    entailer.
    Intros i.
    forward.
    forward.
    normalize.
    assert_PROP (Vptr b (Ptrofs.add ofs (Ptrofs.repr i)) 
                 = field_address (tarray tschar (Zlength contents + 1)) 
                                         [ArraySubsc i]  (Vptr b ofs)).
    entailer!.
    { 
     rewrite field_address_offset.
     simpl.
     normalize. 
     econstructor.
     simpl; auto.
     simpl.
     normalize.
     repeat split.
     all: try (simpl; nia; auto with zarith).
     constructor.
     intros. 
     econstructor.
     constructor.
     simpl; normalize.
     auto with zarith. }
    forward.
    forward_if.
    forward.
    entailer.
    entailer!.
    Exists (i + 1).
    autorewrite with sublist in *|-.
    entailer!.
    cstring.
    forward.
    Exists (Zlength contents).
    entailer.
    autorewrite with sublist in *|-.
    entailer!.
    repeat split; repeat f_equal; try cstring.
    normalize.
    Intro i.
    forward.
Qed.
    
