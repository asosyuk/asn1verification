Require Import Core.Core.
Import ListNotations.

Fixpoint find_struct_fields (id : ident) (c : list composite_definition) :=
  match c with
  | [] => []
  | h :: tl => match h with
             | Composite id' _ ls _ => if (id =? id')%positive
                                      then ls
                                      else find_struct_fields id tl
             end
  end.

Fixpoint ls_to_seq (ls : list statement) :=
  match ls with
  | [] => Sskip
  | [h] => h
  | h1 :: h2 :: tl => Ssequence h1 (Ssequence h2 (ls_to_seq tl))
  end.

Fixpoint copy_by_fields (p : positive) (id1 id2 : ident) (ty : type) (ls : members) :=
  match ls with
  | [] => []
  | h :: tl => let f := fst h in
             let t := snd h in
             let s := Ssequence
                        (Sset p (Efield (Evar id2 ty) f t))
                        (Sassign  (Efield (Ederef (Etempvar id1 (tptr ty)) ty) f t) (Etempvar p t))
             in
             s :: copy_by_fields (p + 1)%positive id1 id2 ty tl
  end.

Fixpoint struct_normalize (s : statement) (c : list composite_definition) :=
  match s with
  | Ssequence s1 s2 => Ssequence (struct_normalize s1 c) (struct_normalize s2 c)
  | Sloop s1 s2 => Sloop (struct_normalize s1 c) (struct_normalize s2 c)
  | Sifthenelse e s1 s2 => Sifthenelse e (struct_normalize s1 c) (struct_normalize s2 c)
  | Sswitch e ls => Sswitch e ((fix switch_normalize ls :=
                                 match ls with
                                 | LSnil => LSnil
                                 | LScons z s ls' => LScons z (struct_normalize s c) (switch_normalize ls')
                                 end) ls)
  | Slabel l s => Slabel l (struct_normalize s c)
  | Sassign (Evar id1 ty1) (Evar id2 ty2)
  | Sassign (Etempvar id1 ty1) (Evar id2 ty2)
  | Sassign (Ederef (Evar id1 ty1) _) (Evar id2 ty2)
  | Sassign (Ederef (Etempvar id1 ty1) _) (Evar id2 ty2) =>
    match ty2 with
      | Tstruct _struct _ => let ls := find_struct_fields _struct c in 
                            ls_to_seq (copy_by_fields 900%positive id1 id2 (Tstruct _struct noattr) ls)
      | _ => s
    end
  | s => s 
  end.
