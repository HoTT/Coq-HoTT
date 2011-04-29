(* Basic definitions about functions. *)

Definition idmap A := fun x : A => x.

Definition compose {A B C} (g : B -> C) (f : A -> B) (x : A) := g (f x).

(** printing ○ $\circ$ *)

Notation "g ○ f" := (compose g f) (left associativity, at level 37).
(* Notation "g 'o' f" := (compose g f) (left associativity, at level 37). *)
