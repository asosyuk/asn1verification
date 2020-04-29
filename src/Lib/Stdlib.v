Require Import Core.Core.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library. (* contains malloc, exit and free specs *)

Definition calloc_spec {cs : compspecs} :=
   WITH m : Z, n : Z, t : type
   PRE [ size_t, size_t ]
       PROP (0 <= m <= Ptrofs.max_unsigned ;
             0 <= n <= Ptrofs.max_unsigned ;
             0 <= m * n <= Ptrofs.max_unsigned;
             sizeof t = n)
       PARAMS (Vptrofs (Ptrofs.repr m); 
               Vptrofs (Ptrofs.repr n)) 
       GLOBALS()
       SEP ()
    POST [ tptr tvoid ] EX p : val, EX ls : list int, 
       PROP (Zlength ls = m;
             Forall (fun x => x = Int.zero) ls)
       LOCAL (temp ret_temp p)
       SEP (if eq_dec p nullval then emp
            else data_at Ews (tarray tint m) (map Vint ls) p).

(* Definition calloc_spec {cs : compspecs} :=
   WITH m : Z, n : Z
   PRE [ size_t, size_t ]
       PROP (0 <= m <= Ptrofs.max_unsigned ;
             0 <= n <= Ptrofs.max_unsigned ;
             0 <= m * n <= Ptrofs.max_unsigned)
       PARAMS (Vptrofs (Ptrofs.repr m); 
               Vptrofs (Ptrofs.repr n)) 
       GLOBALS()
       SEP ()
    POST [ tptr tvoid ] EX p : val, EX ls : list byte, 
       PROP (Zlength ls = (m * n)%Z;
               Forall (fun x => x = Byte.zero) ls)
       LOCAL (temp ret_temp p)
       SEP (if eq_dec p nullval then emp
            else (* malloc_token Ews (tarray tuchar m) p *
                 (* p is valid and malloc_compatible for t *) *)
                  data_at Ews (tarray tuchar m) (map Vubyte ls) p). *)

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

Definition memcmp_spec {cs : compspecs} :=
    WITH qsh : share, psh : share, p : val, q : val, 
         n : Z, r : int, ls: list byte
   PRE [ tptr tvoid, tptr tvoid, size_t ]
       PROP (readable_share qsh; readable_share psh;
             0 <= n <= Ptrofs.max_unsigned;
             n < Zlength ls)
       PARAMS (p; q; Vptrofs (Ptrofs.repr n))
       GLOBALS()
       SEP (data_at qsh (tarray tuchar n) (map Vbyte ls) q;
            data_at psh (tarray tuchar n) (map Vbyte ls) p)
    POST [ tint ]
       PROP() LOCAL(temp ret_temp (Vint r))
       SEP(data_at qsh (tarray tuchar n) (map Vbyte ls) q;
           data_at psh (tarray tuchar n) (map Vbyte ls) p).

(* Definition memchr_spec {cs : compspecs}:=
   WITH sh : share, p: val, n: Z, c: int
   PRE [ tptr tvoid, tint, tuint ]
       PROP (writable_share sh; 0 <= n <= Int.max_unsigned)
       PARAMS (p; Vint c; Vint (Int.repr n))
       GLOBALS()
       SEP (memory_block sh n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint c)) p).

const void * memchr ( const void * ptr, int value, size_t num );
      void * memchr (       void * ptr, int value, size_t num ); *)



