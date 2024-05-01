From HoTT Require Import Basics.Overture Algebra.Rings.Ring Algebra.Rings.CRing.
From HoTT.Algebra Require Import Groups.Group AbGroups.AbelianGroup.
From HoTT Require Import abstract_algebra.

Local Open Scope path_scope.

(** Test that opposite rings are definitionally involutive. *)
Definition test1 (R : Ring) : R = (rng_op (rng_op R)) :> Ring := 1.
Definition test2 (R : CRing) : R = (rng_op (rng_op R)) :> CRing := 1.

Axiom fake_comm : forall (R : CRing) (x y : R), x * y = y * x.
Definition augment (R : CRing) : CRing.
Proof.
  snrapply Build_CRing.
  - exact R.
  - exact (fake_comm R).
Defined.

Fail Definition test3 (R : CRing) : R = augment R :> CRing := 1.
(* !? *)
Definition test4 (R : CRing) : R = (rng_op (rng_op (augment R))) :> CRing := 1.
