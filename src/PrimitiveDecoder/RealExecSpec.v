Require Import Core.Core Core.Notations Lib ErrorWithWriter.

Section Encoder.

Definition real_encoder := 
  fun td (r : list Z) => let r := map (Byte.repr) r in primitive_encoder td r.

End Encoder.

Section Decoder.

Definition real_decoder := primitive_decoder.

End Decoder.
