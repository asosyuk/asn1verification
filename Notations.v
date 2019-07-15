From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.
Import ListNotations.

(* Notations for integers and ptrofs *)

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
Notation "x <= y" := (negb (Int.ltu y x)) (at level 70) : IntScope.
Infix "%" := Int.mods (at level 70) : IntScope.
Infix "//" := Int.divs (at level 70) : IntScope.

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
Notation "x <= y" := (negb (Ptrofs.ltu y x)) (at level 70) : PtrofsScope.
Infix "%" := Ptrofs.mods (at level 70) : PtrofsScope.
Infix "//" := Ptrofs.divs (at level 70) : PtrofsScope.