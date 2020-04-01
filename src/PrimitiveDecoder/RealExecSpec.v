Require Import Core.Core Core.Notations Lib.Lib Lib.ErrorWithWriter.

Section Encoder.

Definition real_encoder := 
  fun td (ls : list byte) => primitive_encoder td ls.

End Encoder.

Section Decoder.

Definition real_decoder := primitive_decoder.

End Decoder.
