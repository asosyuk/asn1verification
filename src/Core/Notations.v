Require Import Core.
Import ListNotations.

(* Notations for integers and ptrofs *)

 Delimit Scope ByteScope with byte.
Infix "==" := Byte.eq (at level 70) : ByteScope.
Notation "x ~= y" := (negb Byte.eq x y) (at level 70) : ByteScope.
Notation "x >> y" := (Byte.shru x y) (at level 70) : ByteScope.
Notation "0" := Byte.zero : ByteScope.
Notation "1" := Byte.one : ByteScope.
Infix "+" := Byte.add  : ByteScope.
Infix "-" := Byte.sub : ByteScope.
Infix "*" := Byte.mul : ByteScope.
Infix "<" := Byte.lt : ByteScope.
Notation "x <=u y" := (negb (Byte.ltu y x)) (at level 70) : ByteScope.
Notation "x <= y" := (negb (Byte.lt y x)) (at level 70) : ByteScope.
Infix "%" := Byte.mods (at level 70) : ByteScope.
Infix "//" := Byte.divs (at level 70) : ByteScope. 

Delimit Scope IntScope with int.
Infix "==" := Int.eq (at level 70) : IntScope.
Notation "x ~= y" := (negb Int.eq x y) (at level 70) : IntScope.
Notation "x >> y" := (Int.shru x y) (at level 70) : IntScope.
Notation "0" := Int.zero : IntScope.
Notation "1" := Int.one : IntScope.
Infix "+" := Int.add : IntScope.
Infix "-" := Int.sub : IntScope.
Infix "*" := Int.mul : IntScope.
Infix "<" := Int.lt : IntScope.
Notation "x <=u y" := (negb (Int.ltu y x)) (at level 70) : IntScope.
Notation "x <= y" := (negb (Int.lt y x)) (at level 70) : IntScope.
Infix "%" := Int.mods (at level 70) : IntScope.
Infix "//" := Int.divs (at level 70) : IntScope.

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
