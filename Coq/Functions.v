(* Basic definitions about functions. *)

Definition idmap A := fun x : A => x.

Definition compose {A B C} (g : B -> C) (f : A -> B) (x : A) := g (f x).

(** printing o $\circ$ *)

Notation "g 'o' f" := (compose g f) (left associativity, at level 37).
