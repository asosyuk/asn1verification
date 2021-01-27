Require Import Core.Core Core.StructNormalizer VstLib.
Require Import VST.floyd.proofauto.
Require Import BFL.Exec. 
Require Import Clight.ber_tlv_length.
Require Import Core.Notations Core.SepLemmas Core.Tactics Core.VstTactics.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.

Section Ber_fetch_len.

Open Scope  bool.

Open Scope Z.

Definition ber_fetch_len_spec : ident * funspec :=
  DECLARE _ber_fetch_length
    WITH c : Z,  b : block, i : ptrofs,
         size : int, data : list int,
         len_r : val
    PRE [tint, tptr tvoid, tuint, tptr tint]
      PROP ((* short definite length *)
           (Znth 0 data & Int.repr 128)%int = 0%int;
             (* primitive tag *)
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
      let r := ber_fetch_len data c 0%int size
                             (Int.repr (sizeof tuint))
       (Int.repr (Int.max_signed)) in
      PROP ()
      LOCAL (temp ret_temp (Vint ((fst r))))
      SEP (data_at Tsh (tarray tuchar (Zlength data)) 
                   (map Vint (data)) (Vptr b i);
           if ((fst r == 0%int) || (fst r == Int.repr (-1)))%bool         
           then data_at_ Tsh tint len_r
           else data_at Tsh tint (Vint (snd r)) len_r).

Definition Gprog := ltac:(with_library prog [ber_fetch_len_spec]).

Lemma Znth_0_cons_sublist :  forall (ls : list int), 
             0 < len ls ->
             Znth 0 ls :: sublist 1 (len ls) ls = ls.
  { intros.
    erewrite Znth_cons_sublist.
    autorewrite with sublist.
    auto. lia. }
Qed.

Theorem ber_fetch_len_correctness : semax_body Vprog Gprog 
                                          (normalize_function f_ber_fetch_length
                                                              composites) 
                                          ber_fetch_len_spec.
Proof.
  start_function.
  forward.
  forward_if.
  forward.
  assert (data_at Tsh (tarray tuchar (len data)) (map Vint data) (Vptr b i) =
          (data_at Tsh tuchar (Vint (Znth 0 data)) (Vptr b i) *
          data_at Tsh (tarray tuchar (len data - 1)) 
                  (sublist 1 (len data) (map Vint data))
                  (Vptr b (i + 1)%ptrofs))%logic) as D.
  { erewrite split_non_empty_list 
      with (i := Vint (Znth 0 data)) 
           (j2 := len data - 1) 
           (ls' := sublist 1 (len data) (map Vint data)).
    auto. erewrite <- map_sublist;
            erewrite <- map_cons;
            f_equal; erewrite Znth_0_cons_sublist; try lia; auto.
    all: autorewrite with sublist; strip_repr. }
  erewrite D.
  Intros.
  forward.
  entailer!.
  eapply Forall_Znth with (i0 := 0) in H2; try lia.
  forward_if; try contradiction.
  forward.
  forward.
  unfold ber_fetch_len.
  repeat rewrite_if_b.
  simpl.
  erewrite <- D.
  entailer!.
Qed.

(* Indefinite length branch:  
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
       match goal with
       | [ _ : _ |-  semax _ ?P ?C ?Post ] =>
         forward_loop (PROP ( )
                       LOCAL (temp _skipped (Vint (Int.repr 1));
                              temp _buf (Vptr b (i + 1)%ptrofs);
                              temp _len (Vint (Int.repr 0)); 
                              temp _oct (Vint (Znth 0 data & Int.repr 127)%int);
                              temp _t'1 Vzero;
                              temp __is_constructed (Vint (Int.repr 0)); 
                              temp _bufptr (Vptr b i);
                              temp _size (Vint size); 
                              temp _len_r len_r)
                       SEP (data_at Tsh tuchar (Vint (Znth 0 data)) (Vptr b i);
                            data_at Tsh (tarray tuchar (len data - 1))
                                    (sublist 1 (len data) (map Vint data))
                                    (Vptr b (i + 1)%ptrofs); data_at_ Tsh tint len_r))
         break: P
        end.
       -- (* PRE to LI *) 
         entailer!.
       -- (* LI C LI *)
         forward_if [temp _skipped (if eq_dec (Znth 0 data & Int.repr 127)%int 0%int 
                                   then Vone
                                   else (Vint (1 + 1)%int)) ;
                     temp _t'2 (if eq_dec (Znth 0 data & Int.repr 127)%int 0%int 
                                then Vzero
                                else Val.of_bool ((1 + 1)%int <=u size))].
         ++ repeat forward.
            repeat rewrite_if_b.
            entailer!.
         ++ forward.
            repeat rewrite_if_b.
            entailer!.
         Arguments eq_dec : simpl never.
         ++ forward_if.
            ** forward_if; try discriminate.
               normalize.
               erewrite split_non_empty_list
                 with (i := Vint (Znth 1 data))
                      (j2 := len data - 2)
                      (ls' := sublist 2 (len data) (map Vint data)).
               Intros.
               forward.
               entailer!.
               eapply Forall_Znth with (i0 := 1) in H1; try lia.
               admit. (* 0 <= 1 < len data *)
               repeat forward.
               entailer!.
               1-5: admit.
            ** forward.
               entailer!.
               admit.
       -- (* BREAK rest POST *)
         forward_if.
         forward_if (temp _t'4 (if (0 <? 0)
                                then Vone 
                                else (Val.of_bool ((-1) >> 1 >> 1 <? 0)))).
         ** forward.
            entailer!.
         ** forward.
            entailer!.
            admit.
         ** forward_if.
            --- forward.
                entailer!.
                admit.
                admit.
            --- forward.
                forward.
                entailer!.
                admit.
                admit.
         ** forward.
            entailer!.
            admit.
            admit.
Admitted.
*)

End Ber_fetch_len.
