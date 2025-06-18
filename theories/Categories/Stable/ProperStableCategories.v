(** * Proper Stable Categories

    A proper stable category is a pre-stable category where the suspension
    and loop functors are inverse equivalences.
    
    Contents:
    - Definition of proper stable categories
    - Triangle identities for the adjunction
    - Basic properties
    - Opposite of proper stable is proper stable
    - Equivalence properties of suspension and loop
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import Biproducts.
Require Import AdditiveCategories.
Require Import PreStableCategories.
Require Import SemiStableCategories.
Require Import OppositeCategories.
Require Import OppositePreStable.

(** * Proper Stable Categories *)

Record ProperStableCategory := {
  pre_stable :> PreStableCategory;
  
  (** η and ε are isomorphisms at each object *)
  eta_is_iso : forall X, IsIsomorphism (components_of (eta pre_stable) X);
  epsilon_is_iso : forall X, IsIsomorphism (components_of (epsilon pre_stable) X);
  
  (** Triangle identities for the adjunction *)
  triangle_1 : forall X, 
    (components_of (epsilon pre_stable) (object_of (Susp pre_stable) X) o 
     morphism_of (Susp pre_stable) (components_of (eta pre_stable) X))%morphism = 1%morphism;
     
  triangle_2 : forall X,
    (morphism_of (Loop pre_stable) (components_of (epsilon pre_stable) X) o
     components_of (eta pre_stable) (object_of (Loop pre_stable) X))%morphism = 1%morphism
}.

(** * Basic Properties *)

Section ProperStableProperties.
  Context (PS : ProperStableCategory).

  (** In a proper stable category, both unit and counit are isomorphisms at
      every object, establishing that suspension and loop are equivalences. *)
  Lemma suspension_is_equivalence (X : object PS)
    : IsIsomorphism (components_of (eta PS) X) /\
      IsIsomorphism (components_of (epsilon PS) (object_of (Susp PS) X)).
  Proof.
    split.
    - (* η is an isomorphism by definition of proper stable *)
      exact (eta_is_iso PS X).
    - (* ε at ΣX is also an isomorphism *)
      exact (epsilon_is_iso PS (object_of (Susp PS) X)).
  Qed.

  (** The suspension and loop functors are inverse equivalences, with explicit
      inverse isomorphisms given by the unit and counit. *)
  Theorem suspension_loop_inverse (X : object PS)
    : (* ΣΩX ≅ X via ε *)
      IsIsomorphism (components_of (epsilon PS) X) /\
      (* ΩΣX ≅ X via η^(-1) *)
      exists (inv_eta : morphism PS (object_of ((Loop PS) o (Susp PS))%functor X) X),
        (inv_eta o components_of (eta PS) X)%morphism = 1%morphism /\
        (components_of (eta PS) X o inv_eta)%morphism = 1%morphism.
  Proof.
    split.
    - exact (epsilon_is_iso PS X).
    - destruct (eta_is_iso PS X) as [inv_eta [H_left H_right]].
      exists inv_eta.
      split; assumption.
  Qed.

  (** Proper stable categories are both left and right semi-stable. *)
  Lemma proper_is_left_semi_stable : is_left_semi_stable PS.
  Proof.
    exact (eta_is_iso PS).
  Qed.

  Lemma proper_is_right_semi_stable : is_right_semi_stable PS.
  Proof.
    exact (epsilon_is_iso PS).
  Qed.

  (** Proper stable categories satisfy both triangle identities. *)
  Lemma proper_satisfies_triangle_identities
    : satisfies_triangle_1 PS * satisfies_triangle_2 PS.
  Proof.
    split.
    - exact (triangle_1 PS).
    - exact (triangle_2 PS).
  Qed.

End ProperStableProperties.

(** * Opposite of Proper Stable Categories *)

Section OppositeProperStable.
  Context (PS : ProperStableCategory).

  (** Helper lemmas for opposite natural transformations. *)
  
  Lemma opposite_preserves_iso {X Y : object PS} (f : morphism PS X Y)
    : IsIsomorphism f -> 
      IsIsomorphism (f : morphism (opposite_category PS) Y X).
  Proof.
    intro H.
    destruct H as [g [Hgf Hfg]].
    exists g.
    split.
    - simpl. exact Hfg.
    - simpl. exact Hgf.
  Qed.

  (** Preservation of isomorphisms under opposite. *)
  
  Lemma eta_iso_opposite
    : forall X, IsIsomorphism (components_of (eta (opposite_prestable_category (pre_stable PS))) X).
  Proof.
    intro X.
    simpl.
    apply opposite_preserves_iso.
    exact (epsilon_is_iso PS X).
  Qed.

  Lemma epsilon_iso_opposite
    : forall X, IsIsomorphism (components_of (epsilon (opposite_prestable_category (pre_stable PS))) X).
  Proof.
    intro X.
    simpl.
    apply opposite_preserves_iso.
    exact (eta_is_iso PS X).
  Qed.

  (** Triangle identities in the opposite. *)
  
  Lemma opposite_triangle_1
    : forall X,
      (components_of (epsilon (opposite_prestable_category (pre_stable PS))) 
        (object_of (Susp (opposite_prestable_category (pre_stable PS))) X) o 
       morphism_of (Susp (opposite_prestable_category (pre_stable PS))) 
        (components_of (eta (opposite_prestable_category (pre_stable PS))) X))%morphism = 
      1%morphism.
  Proof.
    intro X.
    simpl.
    (* In the opposite: Susp^op = Loop, eta^op = epsilon, epsilon^op = eta
       So this becomes: eta(Loop X) ∘ Loop(epsilon X) = 1
       Which is triangle_2 from the original *)
    exact (triangle_2 PS X).
  Qed.

  Lemma opposite_triangle_2
    : forall X,
      (morphism_of (Loop (opposite_prestable_category (pre_stable PS))) 
        (components_of (epsilon (opposite_prestable_category (pre_stable PS))) X) o
       components_of (eta (opposite_prestable_category (pre_stable PS))) 
        (object_of (Loop (opposite_prestable_category (pre_stable PS))) X))%morphism = 
      1%morphism.
  Proof.
    intro X.
    simpl.
    (* In the opposite: Loop^op = Susp, eta^op = epsilon, epsilon^op = eta
       So this becomes: Susp(eta X) ∘ epsilon(Susp X) = 1
       Which is triangle_1 from the original *)
    exact (triangle_1 PS X).
  Qed.

  (** Main theorem: opposite of proper stable is proper stable. *)
  Definition opposite_proper_stable_category : ProperStableCategory.
  Proof.
    exact (Build_ProperStableCategory
      (opposite_prestable_category (pre_stable PS))
      eta_iso_opposite
      epsilon_iso_opposite
      opposite_triangle_1
      opposite_triangle_2).
  Defined.

End OppositeProperStable.

(** * Main Duality Theorems *)

(** The opposite of a proper stable category exists and has the expected form. *)
Theorem proper_stable_duality_principle
  : forall (PS : ProperStableCategory),
    exists (PS_op : ProperStableCategory),
      pre_stable PS_op = opposite_prestable_category (pre_stable PS).
Proof.
  intro PS.
  exists (opposite_proper_stable_category PS).
  reflexivity.
Qed.

(** The beautiful symmetry: Susp and Loop functors perfectly swap roles. *)
Theorem suspension_loop_duality (PS : ProperStableCategory)
  : object_of (Susp (opposite_proper_stable_category PS)) = 
    object_of (opposite_functor (Loop (pre_stable PS))) /\
    object_of (Loop (opposite_proper_stable_category PS)) = 
    object_of (opposite_functor (Susp (pre_stable PS))).
Proof.
  split; reflexivity.
Qed.

(** * Connection to Almost Proper Stable Categories *)

Section ConnectionToSemiStable.
  Context (PS : ProperStableCategory).

  (** Proper stable categories have all the structure of almost proper stable strong. *)
  Theorem proper_is_almost_proper_strong
    : almost_proper_stable_strong (pre_stable PS).
  Proof.
    unfold almost_proper_stable_strong.
    unfold is_left_semi_stable, is_right_semi_stable.
    unfold satisfies_triangle_1, satisfies_triangle_2.
    repeat split.
    - (* is_left_semi_stable: forall X, IsIsomorphism (components_of (eta (pre_stable PS)) X) *)
      exact (eta_is_iso PS).
    - (* is_right_semi_stable: forall X, IsIsomorphism (components_of (epsilon (pre_stable PS)) X) *)
      exact (epsilon_is_iso PS).
    - (* satisfies_triangle_1: forall X, ... = 1 *)
      exact (triangle_1 PS).
    - (* satisfies_triangle_2: forall X, ... = 1 *)
      exact (triangle_2 PS).
  Qed.

  (** Proper stable categories are balanced. *)
  Theorem proper_stable_is_balanced
    : is_balanced (pre_stable PS).
  Proof.
    intros X.
    split.
    - intro H. apply (epsilon_is_iso PS).
    - intro H. apply (eta_is_iso PS).
  Qed.

End ConnectionToSemiStable.

(** * The Fundamental Duality Principle *)

(** This completes our formalization of stable categories and their duality theory.
    The key insights are:
    
    1. Pre-stable categories have suspension and loop functors connected by natural transformations
    2. In the opposite category, these functors swap roles
    3. Proper stable categories (where Σ and Ω are equivalences) are self-dual
    4. Every theorem has a dual obtained by passing to the opposite category
    
    This duality is fundamental in the theory of triangulated and stable categories,
    providing a powerful tool for proving theorems and understanding the structure.
*)

(** * Export Hints *)

Hint Resolve 
  proper_is_left_semi_stable
  proper_is_right_semi_stable
  proper_stable_is_balanced
  : proper_stable.

Hint Resolve
  eta_is_iso
  epsilon_is_iso
  triangle_1
  triangle_2
  : proper_stable_axioms.

(** The next file in the library will be [StableTriangulated.v] which proves
    that proper stable categories with cofibers are triangulated categories. *)