(** * Applications of the Duality Principle

    This file demonstrates concrete applications of the duality principle
    to obtain dual theorems and constructions automatically. We show how
    properties of stable categories systematically dualize, providing a
    powerful tool for discovering new results.
    
    Contents:
    - Dual constructions for triangles
    - Dualization of distinguished triangle properties
    - Dual formulations of stability conditions
    - Automatic generation of dual theorems
    - Non-trivial applications
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import AdditiveCategories.
Require Import PreStableCategories.
Require Import ProperStableCategories.
Require Import Triangles.
Require Import TriangleMorphisms.
Require Import TriangleRotation.
Require Import OppositeCategories.
Require Import OppositePreStable.
Require Import DualityPrinciple.
Require Import SemiStableCategories.

(** * Dual Constructions for Triangles *)

Section DualStability.

  (** If a category is left semi-stable, its opposite is right semi-stable. *)
  Theorem left_stable_gives_opposite_right (PS : PreStableCategory)
    : is_left_semi_stable PS -> is_right_semi_stable (opposite_prestable_category PS).
  Proof.
    apply left_right_semi_stable_dual.
  Qed.

  (** The converse: right semi-stable gives opposite left semi-stable. *)
Theorem right_stable_gives_opposite_left (PS : PreStableCategory)
  : is_right_semi_stable PS -> is_left_semi_stable (opposite_prestable_category PS).
Proof.
  intro H.
  unfold is_left_semi_stable.
  intro X.
  simpl.
  (* We need IsIsomorphism of eta in PS^op, which is epsilon in PS *)
  (* But H X gives IsIsomorphism in PS, we need it in opposite_category PS *)
  pose proof (H X) as H_iso.
  destruct H_iso as [g [Hgf Hfg]].
  exists g.
  split.
  - simpl. exact Hfg.
  - simpl. exact Hgf.
Qed.

  (** Proper stability is self-dual. *)
  Theorem proper_stable_self_dual (PS : ProperStableCategory)
    : ProperStableCategory.
  Proof.
    exact (opposite_proper_stable_category PS).
  Defined.

End DualStability.

(** * Automatic Generation of Dual Theorems *)

Section AutomaticDuals.
  Context (PS : PreStableCategory).


Theorem zero_comp_left {X Y Z : object PS} (f : morphism PS X Y)
  : (add_zero_morphism PS Y Z o f)%morphism = add_zero_morphism PS X Z.
Proof.
  apply zero_morphism_left.
Qed.

Theorem zero_comp_right {X Y Z : object PS} (f : morphism PS Y Z)
  : (f o add_zero_morphism PS X Y)%morphism = add_zero_morphism PS X Z.
Proof.
  apply zero_morphism_right.
Qed.
End AutomaticDuals.

(** * Non-trivial Applications *)

Section NonTrivialApplications.

  (** The suspension-loop adjunction dualizes to a loop-suspension adjunction. *)
  Theorem adjunction_duality (PS : PreStableCategory)
    : (* Original adjunction: Σ ⊣ Ω with unit η and counit ε *)
      (* In opposite: Ω ⊣ Σ with unit ε and counit η *)
      components_of (eta (opposite_prestable_category PS)) = 
      components_of (epsilon PS).
  Proof.
    reflexivity.
  Qed.

  (** If we have a theorem about suspension, we get one about loops for free. *)
  Theorem suspension_preserves_zero_dual (PS : PreStableCategory) 
    : object_of (Loop PS) (@zero _ (add_zero PS)) = @zero _ (add_zero PS).
  Proof.
    (* In PS^op, Loop^op = Susp, so this follows from Susp preserving zero *)
    change (object_of (Loop PS) (@zero _ (add_zero PS))) with
           (object_of (Susp (opposite_prestable_category PS)) 
                      (@zero _ (add_zero (opposite_prestable_category PS)))).
    apply (preserves_zero (opposite_prestable_category PS) 
                          (opposite_prestable_category PS) 
                          (Susp (opposite_prestable_category PS))).
  Qed.

End NonTrivialApplications.

(** * Duality for Exact Sequences *)

Section ExactSequenceDuality.
  Context (PS : PreStableCategory).

Definition is_exact_at {C : PreStableCategory} {X Y Z : object C} 
  (f : morphism C X Y) (g : morphism C Y Z) : Type
  := (g o f)%morphism = add_zero_morphism C X Z.

  (** Exactness dualizes. *)
  Theorem exact_sequence_dualizes {X Y Z : object PS}
    (f : morphism PS X Y) (g : morphism PS Y Z)
    : is_exact_at f g ->
      is_exact_at (g : morphism (opposite_prestable_category PS) Z Y)
                  (f : morphism (opposite_prestable_category PS) Y X).
  Proof.
    unfold is_exact_at.
    intro H.
    simpl.
    (* In opposite: (f ∘ g) = g ∘ f in original *)
    exact H.
  Qed.

End ExactSequenceDuality.

(** * The Power of Duality in Practice *)

Section PowerInPractice.

  (** Every property we prove about pre-stable categories automatically 
      gives us a dual property. This effectively doubles our theorems! *)
  
  (** Example: If we prove that left semi-stable categories with triangle 
      identities have property P, then right semi-stable categories with 
      (dual) triangle identities have the dual property. *)
  
Theorem theorem_doubling_principle_correct
  (P : PreStableCategory -> Type)
  (Q : PreStableCategory -> Type)
  (H_dual : forall PS, P PS <-> Q (opposite_prestable_category PS))
  (H_theorem : forall PS, is_left_semi_stable PS -> satisfies_triangle_1 PS -> P PS)
  (H_invol : forall PS, opposite_prestable_category (opposite_prestable_category PS) = PS)
  : forall PS, 
    is_left_semi_stable (opposite_prestable_category PS) -> 
    satisfies_triangle_1 (opposite_prestable_category PS) -> 
    Q PS.
Proof.
  intros PS H_left_op H_tri1_op.
  rewrite <- H_invol.
  destruct (H_dual (opposite_prestable_category PS)) as [H_forward _].
  apply H_forward.
  apply H_theorem; assumption.
Qed.

Theorem theorem_doubling_principle_final
  (P : PreStableCategory -> Type)
  (Q : PreStableCategory -> Type)
  (H_dual : forall PS, P PS <-> Q (opposite_prestable_category PS))
  (H_theorem : forall PS, is_left_semi_stable PS -> satisfies_triangle_1 PS -> P PS)
  (H_invol : forall PS, opposite_prestable_category (opposite_prestable_category PS) = PS)
  : forall PS, is_right_semi_stable PS -> satisfies_triangle_2 PS -> Q PS.
Proof.
  intros PS H_right H_tri2.
  
  apply theorem_doubling_principle_correct with (P := P).
  - exact H_dual.
  - exact H_theorem.
  - exact H_invol.
  - apply right_stable_gives_opposite_left.
    exact H_right.
  - apply triangle_identity_duality.
    exact H_tri2.
Qed.

End PowerInPractice.

(** * Export Hints *)

Hint Resolve
  left_stable_gives_opposite_right
  right_stable_gives_opposite_left
  exact_sequence_dualizes
  : duality_applications.
