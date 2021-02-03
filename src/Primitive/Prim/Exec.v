Require Import Core.Core Core.Notations Lib.Lib  Lib.DWT.Exec.Der_write_tags
       Lib.BCT.Exec.
From ExtLib.Structures Require Import Monad MonadWriter MonadExc.
From ExtLib.Data Require Import Monads.OptionMonad.

Section Encoder.

(* writes tags, copies ls and outputs the number of encoded bytes *)
Definition primitive_encoder td struct_len buf_size ls : errW1 Z :=
  x <- der_write_tags td struct_len 0 0 0 buf_size ;; 
             tell ls ;; 
            ret (encoded x + struct_len)%Z.

End Encoder.


Section Decoder.

Definition primitive_decoder td ctx size sizeofval sizemax ls :
  option (list int * Z) :=
    match ls with
    | [] => None
    | _ => '(c, l) <- ber_check_tags_primitive ls
           td ctx size sizeofval sizemax ;;
           if (Zlength ls - Int.signed l <? Int.signed c)
           then None 
           else let y := skipn (Z.to_nat (Int.signed c)) ls in
                Some (y, Int.signed c + 1)%Z    
    end.

End Decoder.

