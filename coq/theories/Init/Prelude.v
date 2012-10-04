(** Because we do not use the Coq standard library at all, we have
    to start from scratch. *)

(** In order not to annoy people we follow Coq's reserved notations.
    Thus we copy [Notations.v] from Coq. *)
Require Export Notations.
Require Export Logic.
Require Export Datatypes.

(* A random selection of things from Coq's prelude, thrown in here just
   so that the library compiles. We need to organize this later. *)

(* The identity map and composition. This will probably go elsewhere. *)

Definition idmap A := fun x : A => x.

Definition compose {A B C} (g : B -> C) (f : A -> B) (x : A) := g (f x).

(** printing o $\circ$ *)

Notation "g 'o' f" := (compose g f) (left associativity, at level 37).
