Require Import Core.Core Core.Notations Types.

Fixpoint aux_loop (ptr : list Z) (len len_r skip oct size sizeofval : Z)
  : (Z * Z * Z * Z) := 
  match ptr with
  | x :: xs => if (negb (oct =? 0)) && ((skip + 1) <=? size)
              then if (Z.shiftr len ((8 * sizeofval) - (8 + 1))) =? 0
                   then let len' := Z.lor (Z.shiftl len 8) x in
                        aux_loop xs len' len_r (skip + 1) (oct - 1) size sizeofval
                   else (-1, oct, len, skip)
              else (0, oct, len, skip)
  | nil => (0, 0, 0, 0)
  end.

Definition bfl_loop (ptr : list Z) (len len_r skip oct size sizeofval : Z) 
  := aux_loop ptr len len_r skip oct size sizeofval.

Definition ber_fetch_len (ptr : list Z) (isc len_r size sizeofval rssizem : Z) 
  : (Z * Z) :=
  if size =? 0
  then (0, len_r)
  else let oct := hd 0 ptr in 
       if (Z.land oct 128) =? 0
       then (1, oct)
       else if (negb (isc =? 0)) && (oct =? 128) 
            then (1, -1)
            else if oct =? 255
                 then (-1, len_r)
                 else let oct := Z.land oct 127 in
                      match bfl_loop (skipn 1%nat ptr) 0 len_r 1 oct size sizeofval with
                      | (-1, _, _, _) => (-1, len_r)
                      | (_, oct, len, skip) => if oct =? 0 
                                              then if (len <? 0) || (len >? rssizem)
                                                   then (-1, len_r)
                                                   else (skip, len)
                                              else (0, len_r)
                      end.
