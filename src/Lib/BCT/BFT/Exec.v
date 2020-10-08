Require Import Core.Core Core.Notations Types.

Fixpoint aux_loop (ptr : list Z) (val skip size tclass tag sizeofval : Z) := 
  match ptr with
  | oct :: xs => if skip <=? size
                then if negb (oct & 128 =? 0)
                     then let val' := (val << 7) or (oct & 127) in
                          if negb (val >> (8 * sizeofval - 9) =? 0)
                          then (-1, tag)
                          else aux_loop xs val' (skip + 1) size tclass tag sizeofval
                     else let val' := (val << 7) or oct in
                         (skip, (val' << 2) or tclass)
               else (0, tag)
  | nil => (0, tag)
  end.

Definition bft_loop (ptr : list Z) (val size tclass tag sizeofval : Z) 
  := aux_loop (skipn 1 ptr) val 2 size tclass tag sizeofval.

Definition ber_fetch_tags (ptr : list Z) (size tag sizeofval : Z) :=
  if size =? 0
  then (0, tag)
  else let val := hd 0 ptr in 
       let tclass := val >> 6 in 
       if negb ((val & 31) =? 31)
       then (1, ((val & 31) << 2) or tclass)
       else bft_loop ptr 0 size tclass tag sizeofval.
