Require Import VST.floyd.proofauto.

Lemma data_at_succ_sublist: forall (cs : compspecs) j i ls sh_str end'_b str_ofs,
data_at sh_str (tarray tschar j) (map Vbyte (sublist 0 j ls))
    (Vptr end'_b (Ptrofs.add str_ofs Ptrofs.one))
  |-- data_at sh_str (tarray tschar j) (map Vbyte (sublist 1 (j + 1) (i :: ls)))
        (Vptr end'_b (Ptrofs.add str_ofs Ptrofs.one)).
