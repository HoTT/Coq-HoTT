From HoTT Require Import Basics Types.Universe.
Require Import Truncations.Core HIT.epi Modalities.ReflectiveSubuniverse.
Require Import Limits.Pullback Cubical.PathSquare.
Require Export Algebra.Groups.GrpPullback.
Require Import AbelianGroup AbHom.
Require Import WildCat.Core WildCat.Pullbacks WildCat.EpiStable.

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

Instance haspullbacks_abgroup : HasPullbacks AbGroup.
Proof.
  rapply (haspullbacks_induced abgroup_group).
  intros A B C f g.
  exists (ab_pullback f g).
  reflexivity.
Defined.

Instance isepistable_abgroup `{Univalence} : IsEpiStable AbGroup.
Proof.
  srapply Build_IsEpiStable.
  1: exact _. (* By the above, [AbGroup] has pullbacks. *)
  (* We have to show that the categorical epimorphisms are stable under pullback. *)
  intros A B C f g ef.
  intros Z k1 k2.
  (* Since surjections are epimorphisms in [Type], it's enough to show that the pulled back map is a surjection. *)
  rapply issurj_isepi_funext.
  (* Since surjections are stable under pullback, it's enough to show that [f] is a surjection. *)
  apply issurj_pullback_pr2.
  (* This follows from the fact the epimorphisms of abelian groups are surjections. *)
  by apply ab_issurj_epi.
Defined.

(** Combining [isepistable_abgroup] with [abenriched_abgroup] from AbHom.v gives: *)
Instance isabepistable_abgroup `{Univalence} : IsAbEpiStable AbGroup := {}.
