Require Import Core.Core Core.Notations Lib.Lib  Lib.DWT.Exec Lib.BCT.Exec.
From ExtLib.Structures Require Import Monad MonadWriter MonadExc.
From ExtLib.Data Require Import Monads.OptionMonad.

Require Export ExtLib.Structures.Monad.
From ExtLib.Data Require Export Monads.OptionMonad.

Import MonadNotation.

Section Encoder.

(* writes tags, copies ls and outputs the number of encoded bytes *)
Definition primitive_encoder td ls : errW1 Z :=
  der_write_tags td >>= 
                 fun x => tell ls >>= 
                            fun _ => ret (len ls +  x).

End Encoder.

Section Decoder.

Definition primitive_decoder td ls : option (list byte * Z) :=
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

End Decoder.
