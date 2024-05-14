Require Import Basics.Overture.

(** * Option types *)

(** Option types are a simple way to represent a value that may or may not be present. They are also known as the Maybe monad in functional programming. *)

Definition map {A B} (f : A -> B) (x : option A) : option B :=
  match x with
  | None => None
  | Some a => Some (f a)
  end.

Definition option_path {A} {x y : A} (p : Some x = Some y)
  : x = y.
Proof.
  injection p.
  exact idmap.
Defined.
