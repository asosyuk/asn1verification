Require Import VST.floyd.proofauto.
Require Import Core.Core Core.Notations Types.


Open Scope int.
Fixpoint aux_loop ptr len skip oct size sizeofval :
   (int * int * int * int) := 
  match ptr with
  | x :: xs => if (negb (oct == 0)) && ((skip + 1) <=u size)
              then if (len >> ((Int.repr 8 * sizeofval) - (Int.repr 8 + 1))) == 0
                   then let len' := Int.or (len << Int.repr 8) x in
                        aux_loop xs len' (skip + 1) (oct - 1) size sizeofval
                   else (Int.neg 1, oct, len, skip)
              else (0, oct, len, skip)
  | nil => (0, 0, 0, 0)
  end.

Definition bfl_loop ptr len  skip oct size sizeofval
  := aux_loop ptr len skip oct size sizeofval.


Definition ber_fetch_len ptr isc len_r size sizeofval rssizem : 
   (int * int) :=
  if eq_dec size 0
  then (0, len_r)
  else let oct := Znth 0 ptr in 
       if eq_dec (oct & Int.repr 128) 0
       then (1, oct)
       else if (negb (isc =? 0)) && (oct == Int.repr 128) 
            then (1, Int.neg 1)
            else if eq_dec oct (Int.repr 255)
                 then (Int.neg 1, len_r)
                 else let oct := oct & (Int.repr 127) in
                      match bfl_loop (skipn 1%nat ptr) 0 1 oct size sizeofval with
                      | (z, oct, len, skip) => if eq_dec z (Int.neg 1) 
                                       then (z, len_r)
                                       else 
                                         if eq_dec oct 0 
                                              then if (len < 0) || (rssizem < len)
                                                   then (Int.neg 1, len_r)
                                                   else (skip, len)
                                              else (0, len_r)
                      end.

(* Fixpoint aux_loop (ptr : list Z) (len len_r skip oct size sizeofval : Z)
  : (Z * Z * Z * Z) := 
  match ptr with
  | x :: xs => if (negb (oct =? 0)) && ((skip + 1) <=? size)
              then if (len >> ((8 * sizeofval) - (8 + 1))) =? 0
                   then let len' := (len << 8) or x in
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
       if (oct & 128) =? 0
       then (1, oct)
       else if (negb (isc =? 0)) && (oct =? 128) 
            then (1, -1)
            else if oct =? 255
                 then (-1, len_r)
                 else let oct := oct & 127 in
                      match bfl_loop (skipn 1%nat ptr) 0 len_r 1 oct size sizeofval with
                      | (-1, _, _, _) => (-1, len_r)
                      | (_, oct, len, skip) => if oct =? 0 
                                              then if (len <? 0) || (len >? rssizem)
                                                   then (-1, len_r)
                                                   else (skip, len)
                                              else (0, len_r)
                      end.

Lemma ber_fetch_len_bounds : 
  forall ptr isc len_r size sizeofval,
   Int.min_signed <= hd 0 ptr <= Int.max_signed ->
   Int.min_signed <= len_r <= Int.max_signed ->
   Int.min_signed <= snd (ber_fetch_len ptr isc len_r size sizeofval Int.max_signed) <= Int.max_signed.
Proof.
  intros. 
  unfold ber_fetch_len.
  repeat break_match; simpl; try lia.
  cbn. lia. 
  Require Import VstTactics Core.Tactics.
  all: destruct_orb_hyp;
  repeat Zbool_to_Prop;
  erewrite Z.gtb_ltb in H2;
  Zbool_to_Prop;
  strip_repr.
Qed.
*)
