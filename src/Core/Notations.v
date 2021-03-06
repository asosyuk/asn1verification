Require Import Core.

Notation "x >> y" := (Z.shiftr x y) (at level 70) : Z_scope.
Notation "x << y" := (Z.shiftl x y) (at level 70) : Z_scope.
Infix "&" := Z.land (at level 70) : Z_scope.
Infix "or" := Z.lor (at level 70): Z_scope.

(* Notations for integers and ptrofs *)

Delimit Scope ByteScope with byte.
Infix "==" := Byte.eq (at level 70) : ByteScope.
Notation "x ~= y" := (negb (Byte.eq x y)) (at level 70) : ByteScope.
Notation "x >> y" := (Byte.shru x y) (at level 70) : ByteScope.
Notation "0" := Byte.zero : ByteScope.
Notation "1" := Byte.one : ByteScope.
Infix "+" := Byte.add  : ByteScope.
Infix "-" := Byte.sub : ByteScope.
Infix "*" := Byte.mul : ByteScope.
Infix "<" := Byte.lt : ByteScope.
Infix "<u" := Byte.ltu (at level 70) : ByteScope.
Notation "x <=u y" := (negb (Byte.ltu y x)) (at level 70) : ByteScope.
Notation "x <= y" := (negb (Byte.lt y x)) (at level 70) : ByteScope.
Infix "%" := Byte.mods (at level 70) : ByteScope.
Infix "//" := Byte.divs (at level 70) : ByteScope. 
Infix "&" := Byte.and (at level 70) : ByteScope. 


Delimit Scope IntScope with int.
Infix "==" := Int.eq (at level 70) : IntScope.
Notation "x ~= y" := (negb Int.eq x y) (at level 70) : IntScope.
Notation "x >> y" := (Int.shr x y) (at level 70) : IntScope.
Notation "x >>u y" := (Int.shru x y) (at level 70) : IntScope.
Notation "x << y" := (Int.shl x y) (at level 70) : IntScope.
Notation "0" := Int.zero : IntScope.
Notation "1" := Int.one : IntScope.
Infix "+" := Int.add : IntScope.
Infix "-" := Int.sub : IntScope.
Infix "*" := Int.mul : IntScope.
Infix "<" := Int.lt : IntScope.
Infix "<u" := Int.ltu (at level 70) : IntScope.
Notation "x <=u y" := (negb (Int.ltu y x)) (at level 70) : IntScope.
Notation "x <= y" := (negb (Int.lt y x)) (at level 70) : IntScope.
Infix "%" := Int.mods (at level 70) : IntScope.
Infix "//" := Int.divs (at level 70) : IntScope.
Infix "&" := Int.and (at level 70) : IntScope. 
Infix "or" := Int.or (at level 70) : IntScope. 


Delimit Scope Int64Scope with int64.
Infix "==" := Int64.eq (at level 70) : Int64Scope.
Notation "x ~= y" := (negb Int64.eq x y) (at level 70) : Int64Scope.
Notation "x >> y" := (Int64.shru x y) (at level 70) : Int64Scope.
Notation "0" := Int64.zero : Int64Scope.
Notation "1" := Int64.one : Int64Scope.
Infix "+" := Int64.add : Int64Scope.
Infix "-" := Int64.sub : Int64Scope.
Infix "*" := Int64.mul : Int64Scope.
Infix "<" := Int64.lt : Int64Scope.
Notation "x <= y" := (negb (Int64.lt y x)) (at level 70) : Int64Scope.
Notation "x <=u y" := (negb (Int64.ltu y x)) (at level 70) : Int64Scope.
Infix "%" := Int64.mods (at level 70) : Int64Scope.
Infix "//" := Int64.divs (at level 70) : Int64Scope.
 
Delimit Scope PtrofsScope with ptrofs.
Infix "==" := Ptrofs.eq (at level 70) : PtrofsScope.
Notation "x ~= y" := (negb Ptrofs.eq x y) (at level 70) : PtrofsScope.
Notation "x >> y" := (Ptrofs.shru x y) (at level 70) : PtrofsScope.
Notation "0" := Ptrofs.zero : PtrofsScope.
Notation "1" := Ptrofs.one : PtrofsScope.
Infix "+" := Ptrofs.add : PtrofsScope.
Infix "-" := Ptrofs.sub : PtrofsScope.
Infix "*" := Ptrofs.mul : PtrofsScope.
Infix "<" := Ptrofs.lt : PtrofsScope.
Infix "<u" := Ptrofs.ltu (at level 70) : PtrofsScope.
Notation "x <= y" := (negb (Ptrofs.lt y x)) (at level 70) : PtrofsScope.
Notation "x <=u y" := (negb (Ptrofs.ltu y x)) (at level 70) : PtrofsScope.
Infix "%" := Ptrofs.mods (at level 70) : PtrofsScope.
Infix "//" := Ptrofs.divs (at level 70) : PtrofsScope.

Delimit Scope PTreeScope with ptree.
Notation "a <~ b" := (a, b) (at level 85, only parsing).
Definition s {A : Type} (a : (positive * A)) := PTree.set (fst a) (snd a).
Notation "'in' env 'set' [ x ; .. ; y ]" :=
  ((s x) .. ((s y) env) ..)
    (at level 85, right associativity).


Delimit Scope ByteScope with byte.
Infix "==" := Byte.eq (at level 70) : ByteScope.
Notation "x ~= y" := (negb Byte.eq x y) (at level 70) : ByteScope.
Notation "x >> y" := (Byte.shru x y) (at level 70) : ByteScope.
Notation "0" := Byte.zero : ByteScope.
Notation "1" := Byte.one : ByteScope.
Infix "+" := Byte.add : ByteScope.
Infix "-" := Byte.sub : ByteScope.
Infix "*" := Byte.mul : ByteScope. 
Infix "<" := Byte.lt (at level 70) : ByteScope.
Notation "x <=u y" := (negb (Byte.ltu y x)) (at level 70) : ByteScope.
Notation "x <= y" := (negb (Byte.lt y x)) (at level 70) : ByteScope.
Infix "%" := Byte.mods (at level 70) : ByteScope.
Infix "//" := Byte.divs (at level 70) : ByteScope.

(* Byte list notations *)
Notation all_zero := Byte.zero.
Definition all_one  := Byte.repr (Byte.max_unsigned).
Notation default_byte := all_zero.
Notation "t @ n" := (Byte.testbit t n) (at level 50).
Notation len a := (Zlength a).
Definition flatten {A} l := fold_right (@app _) (@nil A) l.

Class Nth A := 
  { default : A;
    n_th : Z -> list A -> A;
    hd_nth : list A -> A }.

Notation "ls # n" := (n_th n ls) (at level 70).

Instance Nth_Byte : Nth byte :=
  { default := default_byte ;
    n_th := fun n ls => nth (Z.to_nat n) ls default_byte;
    hd_nth := fun ls => List.hd default_byte ls
    }.

Instance Nth_Bool : Nth bool :=
  { default := false ;
    n_th := fun n ls => nth (Z.to_nat n)  ls false;
    hd_nth := fun ls => List.hd false ls
 }.


Instance Nth_List {A} : Nth (list A) :=
  { default := [] ;
    n_th := fun n ls => nth (Z.to_nat n) ls [];
    hd_nth := fun ls => List.hd [] ls
 }.

Require Import ExtLib.Structures.Monad.

Inductive DWT_Error := .

 Delimit Scope monad_scope with monad.

  Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 58, left associativity) : monad_scope.
  Notation "f =<< c" := (@bind _ _ _ _ c f) (at level 61, right associativity) : monad_scope.
  Notation "f >=> g" := (@mcompose _ _ _ _ _ f g) (at level 55, right associativity) : monad_scope. 

  Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity) : monad_scope.

  Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
    (at level 61, right associativity) : monad_scope.

  Notation "' pat <- c1 ;; c2" :=
    (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
    (at level 61, pat pattern, c1 at next level, right associativity) : monad_scope.
