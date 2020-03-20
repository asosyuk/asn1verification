Require Import Core.Core Core.Notations Lib ErrorWithWriter.
From ExtLib.Structures Require Import Monad MonadWriter Monoid.
From ExtLib.Data Require Import List Monads.OptionMonad.

Import MonadNotation.
Import ListNotations.

Open Scope monad.

Section Encoder.

Existing Class Monoid.
Existing Instance Monoid_list_app.

Definition real_prim_encoder (td : TYPE_descriptor) (r : list Z) : errW1 asn_enc_rval :=
  let r := map (Byte.repr) r in
  der_write_tags td >>= fun x => tell r >>= fun _ => ret (encode (1 + encoded x)).

End Encoder.

Section Decoder.

Definition bool_decoder (td : TYPE_descriptor) (ls : list byte) : option (byte * Z) :=
    match ls with
    | [] => None
    | _ => ber_check_tag td ls >>=
                        fun x => let c := tag_consumed x in 
                              let e := tag_expected x in 
                              if (Zlength ls - c <? e) || negb (e =? 1) 
                              then None 
                              else (hd_error (skipn (Z.to_nat c) ls)) 
                                     >>= fun y => Some (y, c + 1)
    end.

End Decoder.
