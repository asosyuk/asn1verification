Require Import Core.Core Core.Notations Core.Notations Types.
Require Import ExtLib.Structures.Monad.

Import MonadNotation.

(* checks the tag, outputs consumed length and expected length *)
Definition ber_check_tags (td : TYPE_descriptor) 
           (ls : list byte) : option check_tag_r :=
  match decoder_type td with
  | BOOLEAN_t => match ls with
                | x1::x2::_ => if ((x1 == Byte.one) && (x2 == Byte.one))%byte
                            then Some (mk_check_tag_rval 2 1 )
                            else None
                | _ => None
                end
  | _ => None
  end.
  
