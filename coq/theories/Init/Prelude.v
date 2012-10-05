(** Because we do not use the Coq standard library at all, we have
    to start from scratch. *)

Require Export Notations.
Require Export Logic.
Require Export Datatypes.
Require Export Coq.Init.Tactics.

Add Search Blacklist "_admitted" "_subproof" "Private_".

(* Old things from the HoTT library. It is a bit wrong to have this here. *)
(* The identity map and composition. This will probably go elsewhere. *)

Definition idmap A := fun x : A => x.

Definition compose {A B C} (g : B -> C) (f : A -> B) (x : A) := g (f x).

(** printing o $\circ$ *)

Notation "g 'o' f" := (compose g f) (left associativity, at level 37).

