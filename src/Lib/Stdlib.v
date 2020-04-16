Require Import Core.Core.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Definition calloc_spec {cs : compspecs} :=
   WITH m : Z, n : Z
   PRE [ size_t, size_t ]
       PROP (0 <= m <= Ptrofs.max_unsigned ;
             0 <= n <= Ptrofs.max_unsigned ;
             0 <= m * n <= Ptrofs.max_unsigned)
       PARAMS (Vptrofs (Ptrofs.repr m); 
               Vptrofs (Ptrofs.repr n)) 
       GLOBALS()
       SEP ()
    POST [ tptr tvoid ] EX p : val, EX t : type, EX ls : list byte, 
       PROP (Zlength ls = (m * n)%Z;
               Forall (fun x => x = Byte.zero) ls)
       LOCAL (temp ret_temp p)
       SEP (if eq_dec p nullval then emp
            else malloc_token Ews t p * (* p is valid and malloc_compatible for t *)
                  data_at Ews (tarray tschar m) (map Vbyte ls) p).

Definition memcpy_spec {cs : compspecs} :=
    WITH qsh : share, psh: share, p: val, q: val, n: Z, contents: list int
   PRE [ tptr tvoid, tptr tvoid, tuint ]
       PROP (readable_share qsh; writable_share psh; 0 <= n <= Int.max_unsigned)
       PARAMS (p; q; Vint (Int.repr n))
       GLOBALS()
       SEP (data_at qsh (tarray tuchar n) (map Vint contents) q;
              memory_block psh n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at qsh (tarray tuchar n) (map Vint contents) q;
             data_at psh (tarray tuchar n) (map Vint contents) p).

Definition memset_spec {cs : compspecs}:=
   WITH sh : share, p: val, n: Z, c: int
   PRE [ tptr tvoid, tint, tuint ]
       PROP (writable_share sh; 0 <= n <= Int.max_unsigned)
       PARAMS (p; Vint c; Vint (Int.repr n))
       GLOBALS()
       SEP (memory_block sh n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint c)) p).
