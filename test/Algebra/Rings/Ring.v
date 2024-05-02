From HoTT Require Import Basics.Overture Algebra.Rings.Ring Algebra.Rings.CRing.
From HoTT.Algebra Require Import Groups.Group AbGroups.AbelianGroup.
From HoTT Require Import abstract_algebra.

Local Open Scope path_scope.

(** Test that opposite rings are definitionally involutive. *)
Definition test1 (R : Ring) : R = (rng_op (rng_op R)) :> Ring := 1.
  
(** This may look funny, but you will see that Coq discards the [rng_op] during elaboration meaning that we only have [R = R] at the end. The reason this works is that [rng_op] takes in only a [Ring]. Afterwards, Coq is able to see that [rng_op (rng_op R)] should be a [CRing] and the coercion from [Ring] to [CRing] is reversible, therefore Coq tries to unify it with the original commutative ring. This behaviour is a bit surprising but is harmless so we just document it here. *)
Definition test2 (R : CRing) : R = (rng_op (rng_op R)) :> CRing := 1.
