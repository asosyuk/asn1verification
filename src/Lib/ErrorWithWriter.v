From ExtLib.Structures Require Import Monad MonadWriter MonadExc Monoid.
Require Import ExtLib.Data.Monads.WriterMonad.

Import MonadNotation.

Open Scope monad.

Section Error.

(* Error type *)
Context {E : Type}.
(* Log type that must implement monoid typeclass *)
Context {T : Type}.
Context {MT : Monoid T}.

(* Custom monad parametrized by Error type, Log type and return type *)
Definition errW A := T -> E + (T * A).

Global Instance Monad_errW : Monad errW := {
  ret := fun _ x => fun w => inr (w, x) ;
  bind := fun _ _ m f => fun w => match m w with
                            | inl v => inl v
                            | inr (w', x) => f x w'
                            end
}.

Global Instance Exception_errW : MonadExc E errW := {
  raise := fun _ v => fun w => inl v ;
  catch := fun _ c h => fun w => match c w with
                           | inl v => h v w
                           | inr x => inr x
                           end
}.

Global Instance Writer_errW : MonadWriter MT errW := {
  tell := fun w => fun _ => inr (w, tt) ;
  listen := fun _ m => fun w => match m w with 
                          | inl v => inl v 
                          | inr (w', x) => inr (w', (x, w'))
                          end ;
  pass := fun _ m => fun w => match m w with
                        | inl v => inl v
                        | inr (w', (x, f)) => inr (f w', x)
                        end ;
}.

(* Run monad and get inner value *)
Definition evalErrW {A : Type} (e : errW A) (init : T) : option A := 
  match e init with
  | inl _ => None
  | inr (_, v) => Some v
  end.

(* Run monad and get log value *)
Definition execErrW {A : Type} (e : errW A) (init : T) : option T :=
  match e init with
  | inl _ => None
  | inr (w, _) => Some w
  end.

End Error.
