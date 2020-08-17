Require Import Core.

Fixpoint find_struct_fields (id : ident) (c : list composite_definition) :=
  match c with
  | [] => []
  | h :: tl => match h with
             | Composite id' _ ls _ => 
               if (id =? id')%positive
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

Fixpoint copy_by_fields (p : positive) (e : expr) (id2 : ident) (ty : type) (ls : members) :=
  match ls with
  | [] => []
  | h :: tl => let f := fst h in
             let t := snd h in
             let p' := (p + f)%positive in
             let s :=
                 Ssequence
                   (Sset p' (Efield (Evar id2 ty) f t))
              match e with 
                | (Evar id1 ty1) => (Sassign (Efield (Evar id1 ty) f t)
                                            (Etempvar p' t))
                | (Etempvar id1 ty1) => (Sassign (Efield (Etempvar id1 ty) f t) 
                                                (Etempvar p' t))
                | (Ederef (Evar id1 ty1) _) => 
                  (Sassign  (Efield (Ederef (Evar id1 (tptr ty)) ty) f t) 
                            (Etempvar p' t))
                | (Ederef (Etempvar id1 ty1) _) =>
                  (Sassign  (Efield (Ederef (Etempvar id1 (tptr ty)) ty) f t) 
                            (Etempvar p' t))
                | _ => Sskip
              end in
             s :: copy_by_fields p e id2 ty tl
  end.

Fixpoint struct_normalize (s : statement) (c : list composite_definition) (p : positive) :=
  match s with
  | Ssequence s1 s2 =>
    Ssequence (struct_normalize s1 c p) (struct_normalize s2 c p)
  | Sloop s1 s2 => Sloop (struct_normalize s1 c p) (struct_normalize s2 c p)
  | Sifthenelse e s1 s2 => Sifthenelse e (struct_normalize s1 c p) (struct_normalize s2 c p)
  | Sswitch e ls =>
    Sswitch e ((fix switch_normalize ls :=
                  match ls with
                  | LSnil => LSnil
                  | LScons z s ls' => LScons z (struct_normalize s c p) (switch_normalize ls')
                  end) ls)
  | Slabel l s => Slabel l (struct_normalize s c p)
  | Sassign e (Evar id2 ty2) =>
    match ty2 with
    | Tstruct _struct _ => 
      let ls := find_struct_fields _struct c in 
      ls_to_seq (copy_by_fields p e id2 (Tstruct _struct noattr) ls)
    | _ => s
    end
  | Scall id e le => 
    match e with
    | Evar v (Tfunction tl t cc) => 
      Scall id (Evar v (Tfunction tl t (mkcallconv (cc_vararg cc)
                                                   (cc_unproto cc) false))) le
    | _ => s
    end
  | s => s 
  end.

Definition fresh_ident f := 
   (Z.to_pos (Zlength (fn_temps f)) * last (map fst (fn_temps f)) 1)%positive. 

Fixpoint new_fn_temps p fs c :=
match fs with
| [] => []
| h :: tl =>
  (fix new_fn_temps_loop  (f : list (ident * type))  c :=
      match f with
      | [] => []
      | h :: tl =>
        match snd h with
           | Tstruct id _ =>
        let ls := find_struct_fields id c in
        map (fun t => ((fun x => p + x)%positive (fst t), snd t)) ls
                                  ++ new_fn_temps_loop tl c
           | _ => new_fn_temps_loop tl c
        end
      end) h c ++ new_fn_temps p tl c
end.

Definition normalize_function f c :=
  mkfunction (fn_return f) (fn_callconv f) (fn_params f) (fn_vars f)
             ((fn_temps f) ++ new_fn_temps (fresh_ident f)
                           [(fn_temps f); (fn_vars f);
                              (fn_params f)] c)
             (struct_normalize (fn_body f) c (fresh_ident f)).
