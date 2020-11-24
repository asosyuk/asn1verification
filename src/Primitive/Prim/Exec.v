Require Import Core.Core Core.Notations Lib.Lib  Lib.DWT.Exec.Der_write_tags.
From ExtLib.Structures Require Import Monad MonadWriter MonadExc.
From ExtLib.Data Require Import Monads.OptionMonad.


Section Encoder.

(* writes tags, copies ls and outputs the number of encoded bytes *)
Definition primitive_encoder td struct_len buf_size ls : errW1 Z :=
  der_write_tags td struct_len 0 0 0 buf_size >>= 
                 fun x => tell ls >>= 
                            fun _ => ret (encoded x + struct_len).

End Encoder.

