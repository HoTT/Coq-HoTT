Require Import Basics.
Require Import Classes.interfaces.abstract_algebra.

(* We say that a relation is a congruence if it respects the operation.
  This is technically incorrect since we are not enforcing the relation to be an equivalence relation.
*)

Local Open Scope mc_mult_scope.

Class IsCongruence {G} `{SgOp G} (R : Relation G) := {
  iscong {x x' y y'} : R x x' -> R y y' -> R (x * y) (x' * y');
}.
