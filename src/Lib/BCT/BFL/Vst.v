Require Import Core.Core Core.StructNormalizer VstLib.
Require Import VST.floyd.proofauto.
(* Require Import BFL.Exec. *)
Require Import Clight.ber_tlv_length.
Require Import Core.Notations Core.SepLemmas Core.Tactics Core.VstTactics.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Section Ber_fetch_len.

Open Scope  bool.
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

Open Scope Z.

Definition ber_fetch_len_spec : ident * funspec :=
  DECLARE _ber_fetch_length
    WITH c : Z,  b : block, i : ptrofs,
         size : int, data : list int,
         len_r : val
    PRE [tint, tptr tvoid, tuint, tptr tint]
      PROP ((* isptr buf_p; *)
            (* isptr len_r;
            Zlength data = size; *)
        c = 0;
        Ptrofs.unsigned i + len data < Ptrofs.modulus;
        Forall (fun x => 0 <= Int.unsigned x <= Byte.max_unsigned) data;
            0 < len data)
      PARAMS (Vint (Int.repr 0); (Vptr b i); Vint size; len_r)
      GLOBALS ()
      SEP (data_at Tsh (tarray tuchar (Zlength data)) 
                   (map Vint data) (Vptr b i);
           data_at_ Tsh tint len_r)
    POST [tint]
      let r := ber_fetch_len data c 0%int size (Int.repr (sizeof tuint))
       (Int.repr (Int.max_unsigned)) in
      PROP ()
      LOCAL (temp ret_temp (Vint ((fst r))))
      SEP (data_at Tsh (tarray tuchar (Zlength data)) 
                   (map Vint (data)) (Vptr b i);
           if eq_dec (fst r) 0%int                     
           then  data_at_ Tsh tint len_r
           else if eq_dec (fst r) (Int.neg 1%int)
                then  data_at_ Tsh tint len_r
                else 
                  data_at Tsh tint (Vint (snd r)) len_r).

Definition Gprog := ltac:(with_library prog [ber_fetch_len_spec]).

Theorem ber_fetch_len_corr : semax_body Vprog Gprog 
                                          (normalize_function f_ber_fetch_length
                                                              composites) 
                                          ber_fetch_len_spec.
Proof.
start_function.
forward.
forward_if.
forward.
erewrite split_non_empty_list 
  with (i := Vint (Znth 0 data)) 
       (j2 := len data - 1) 
       (ls' := sublist 1 (len data) (map Vint data)).
Intros.
forward.
admit. (*entailer!.
eapply Forall_Znth with (i0 := 0) in H; try lia.
strip_repr. *)
forward_if.
- admit.
 (* forward.
  forward.
  unfold ber_fetch_len.
  repeat rewrite_if_b.
  simpl.
  erewrite <- split_non_empty_list
    with (i := Vint (Znth 0 data))
         
         (ls' := sublist 1 (len data) (map Vint data)).
  entailer!.
  erewrite <- map_sublist.
  erewrite <- map_cons.
  f_equal.
  assert (Znth_0_cons_sublist :  forall (ls : list int), 
             0 < len ls ->
             Znth 0 ls :: sublist 1 (len ls) ls = ls).
  { intros.
    erewrite Znth_cons_sublist.
    autorewrite with sublist.
    auto. lia. }
  erewrite Znth_0_cons_sublist; auto; try lia.
  1-2: autorewrite with sublist; rep_omega.
  auto. *)
- forward_if (temp _t'1 Vzero); try contradiction.
  + admit.
    (* forward.
       entailer!. *)
  + forward_if; try contradiction.
    forward_if.
    * admit. (* forward.
      { unfold ber_fetch_len.
        repeat rewrite_if_b.
        simpl.
        entailer!.
        admit. (* split as before *) } *)
    * repeat forward.
      (* Loop *)
Admitted.

End Ber_fetch_len.
