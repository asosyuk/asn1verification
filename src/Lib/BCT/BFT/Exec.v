Require Import Core.Core Core.Notations Types.

Fixpoint aux_loop (ptr : list Z) (val skip size tclass tag sizeofval : Z) 
  : (Z * Z) := 
  match ptr with
  | oct :: xs => if skip <=? size
               then if negb (Z.land oct 128 =? 0)
                    then let val' := (Z.lor (Z.shiftl val 7) (Z.land oct 127)) in
                         if negb (Z.shiftr val (8 * sizeofval - 9) =? 0)
                         then (-1, tag)
                         else aux_loop xs val' (skip + 1) size tclass tag sizeofval
                    else let val' := Z.lor (Z.shiftl val 7) oct in
                         (skip, Z.lor (Z.shiftl val' 2) tclass)
               else (0, tag)
  | nil => (0, tag)
  end.

Definition bft_loop (ptr : list Z) (val size tclass tag sizeofval : Z) 
  : (Z * Z) := aux_loop (skipn 1 ptr) val 2 size tclass tag sizeofval.

Definition ber_fetch_tags (ptr : list Z) (val size tag sizeofval : Z) 
  : (Z * Z) :=
  if size =? 0
  then (0, tag)
  else let val := hd 0 ptr in 
       let tclass := Z.shiftr val 6 in 
       if negb ((Z.land val 31) =? 31)
       then (1, Z.lor (Z.shiftl (Z.land val 31) 2) tclass)
       else bft_loop ptr 0 size tclass tag sizeofval.
