From HoTT Require Import Basics.Overture Algebra.Rings.Ring Algebra.Rings.CRing.
From HoTT.Algebra Require Import Groups.Group AbGroups.AbelianGroup.
From HoTT Require Import abstract_algebra.

Local Open Scope path_scope.

(** Test that opposite rings are definitionally involutive. *)
Definition test1 (R : Ring) : R = (rng_op (rng_op R)) :> Ring := 1.
Definition test2 (R : CRing) : R = (rng_op (rng_op R)) :> CRing := 1.
