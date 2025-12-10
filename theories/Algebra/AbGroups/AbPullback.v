From HoTT Require Import Basics.
Require Import Limits.Pullback Cubical.PathSquare.
Require Export Algebra.Groups.GrpPullback.
Require Import Algebra.AbGroups.AbelianGroup.
Require Import WildCat.Core WildCat.Pullbacks.

Local Open Scope mc_add_scope.

(** * Pullbacks of abelian groups *)

Section AbPullback.
  (* Variables are named to correspond with Limits.Pullback. *)
  Context {A B C : AbGroup} (f : B $-> A) (g : C $-> A).

  #[export] Instance ab_pullback_commutative
    : Commutative (@group_sgop (grp_pullback f g)).
  Proof.
    unfold Commutative.
    intros [b [c p]] [d [e q]].
    apply equiv_path_pullback; simpl.
    refine (commutativity _ _; commutativity _ _; _).
    apply equiv_sq_path.
    apply path_ishprop.
  Defined.

  Definition ab_pullback : AbGroup := Build_AbGroup (grp_pullback f g) _.

  (** The corecursion principle is inherited from [Group]; use [grp_pullback_corec] and friends from Groups/GrpPullback.v. *)

End AbPullback.

Definition haspullbacks_abgroup : HasPullbacks AbGroup.
Proof.
  rapply (haspullbacks_induced abgroup_group).
  intros A B C f g.
  exists (ab_pullback f g).
  reflexivity.
Defined.
