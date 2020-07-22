Require Import Core.Core Core.Notations Core.Tactics Types
        Exec.Der_write_tags BCT.Exec.
From ExtLib.Structures Require Import Monad MonadWriter.
From ExtLib.Data Require Import Monads.OptionMonad.

Require Export Types.
Require Export ExtLib.Structures.Monad.
From ExtLib.Data Require Export Monads.OptionMonad.

Open Scope monad.

Definition primitive_decoder td ls : option (list int * Z) :=
    match ls with
    | [] => None
    | _ => ber_check_tags td ls >>=
                        fun x => let c := tag_consumed x in 
                              let l := tag_length x in 
                              if (Zlength ls - c <? l)
                              then None 
                              else let y := skipn (Z.to_nat c) ls in
                                    Some (y, c + 1)    
    end.

(* writes tags, copies ls and outputs the number of encoded bytes *)
(* Definition primitive_encoder td ls : errW1 asn_enc_rval :=
  x <- der_write_tags td  ;; 
  tell ls ;;
  ret (encode (Zlength ls + encoded x)). *)

Definition ZeroChar := Byte.repr 48.

Definition bool_of_byte (b : byte) := 
  if (b == default_byte)%byte then false else true.
Definition byte_of_bool (b : bool) := Byte.repr (if b then 255 else 0).
Definition int_of_bool (b : bool) := Int.repr (if b then 255 else 0).
Definition bool_of_int (i : int) := 
  if (i == 0)%int then false else true.

(* Find composite *)
Fixpoint find_cs (id : ident) cs : option composite_definition :=
  match cs with
  | Composite i s_u m a :: css => if (i =? id)%positive
                             then Some (Composite i s_u m a)
                             else find_cs id css
  | [] => None
  end.

