Require Import Basics Types.
Require Import Algebra.Rings.CRing.
Require Import Algebra.AbGroups.

Local Open Scope mc_scope.

(** In this file we define Ideals *)

(** TODO: In the future it might be useful to define ideals as submodules *)

(** An additive subgroup I of a ring R is an ideal when: *)
Class IsIdeal {R : CRing} (I : Subgroup R) := {
  (** Forall r : R and x : I, there exists an a : I, such that a = r * x inside R *)
  isideal : forall r x, exists a, issubgroup_incl a = r * issubgroup_incl x;
}.

Record Ideal (R : CRing) := {
  ideal_subgroup : Subgroup R;
  ideal_isideal : IsIdeal ideal_subgroup;
}.

Coercion ideal_subgroup : Ideal >-> Subgroup.
Global Existing Instances ideal_isideal.
