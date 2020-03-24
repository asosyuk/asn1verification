Require Import Core.Core Core.Notations Lib.

Section Encoder.

Definition bool_encoder := 
  fun td (b : bool) => let t := if b then (Byte.repr 255) else (Byte.repr 0) in 
                 primitive_encoder td (cons t nil).

End Encoder.

Section Decoder.

Definition bool_decoder := primitive_decoder.

End Decoder.
