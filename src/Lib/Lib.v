Require Import Core.Core Core.Notations Core.Tactics Types.

Require Export Types.

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

