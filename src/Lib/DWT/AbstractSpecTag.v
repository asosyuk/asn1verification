Require Import Core.Core Core.Notations.

Inductive Tag : list byte -> Prop :=
(* 8.1.2.2 *)
(* tag number < 31 *)
| Low_tag t : t @ 7 = false -> Tag [t]
(* 8.1.2.4 *)
(* tag number >= 31 *)
| High_tag t ls : forall n,
    (* 1st octet *)
    (0 <= n <= 5 -> t @ n = true) ->
    (* subsequent octets representing the tag number *)
     ls#0 <> all_zero ->  
    (forall m, m < len ls - 1 -> (ls#m) @ 7 = true) ->
    (ls#(len ls - 1)) @ 7 = false ->    
    Tag (t::ls).
