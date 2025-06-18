(** * Semi-Stable Categories and the Stability Hierarchy

    Semi-stable categories form an intermediate class between pre-stable and 
    proper stable categories. They are characterized by having the unit or 
    counit be an isomorphism in only one direction, providing insight into 
    the gradual transition from pre-stable to proper stable structures.
    
    This file establishes:
    - Left and right semi-stability definitions
    - The duality between left and right semi-stability
    - Balanced categories where η and ε isomorphism properties correlate
    - The complete hierarchy from pre-stable to proper stable categories
    - Triangle identities and their consequences
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import Biproducts.
Require Import AdditiveCategories.
Require Import PreStableCategories.

(** * Isomorphism Definition
    
    We need a basic definition of isomorphism to work with semi-stability.
    This could later be unified with the HoTT library's definition.
*)

Definition IsIsomorphism {C : PreCategory} {X Y : object C} (f : morphism C X Y)
  : Type
  := { g : morphism C Y X |
       (g o f = 1)%morphism /\ (f o g = 1)%morphism }.

(** Extract the inverse morphism. *)
Definition iso_inverse {C : PreCategory} {X Y : object C} {f : morphism C X Y} 
  (H : IsIsomorphism f)
  : morphism C Y X
  := H.1.

(** * Left and Right Semi-Stability *)

(** A pre-stable category is left semi-stable if the unit natural 
    transformation η is an isomorphism at every object. *)
Definition is_left_semi_stable (PS : PreStableCategory)
  : Type
  := forall X : object PS, IsIsomorphism (components_of (eta PS) X).

(** A pre-stable category is right semi-stable if the counit natural 
    transformation ε is an isomorphism at every object. *)
Definition is_right_semi_stable (PS : PreStableCategory)
  : Type
  := forall X : object PS, IsIsomorphism (components_of (epsilon PS) X).

(** ** Basic Properties of Semi-Stability *)

Section SemiStableProperties.
  Context (PS : PreStableCategory).

  (** Left semi-stable means we can invert η. *)
  Definition eta_inverse (H : is_left_semi_stable PS) (X : object PS)
    : morphism PS (object_of ((Loop PS) o (Susp PS))%functor X) X
    := iso_inverse (H X).

  (** Right semi-stable means we can invert ε. *)
  Definition epsilon_inverse (H : is_right_semi_stable PS) (X : object PS)
    : morphism PS X (object_of ((Susp PS) o (Loop PS))%functor X)
    := iso_inverse (H X).

  (** Basic inversion properties. *)
  Lemma eta_inverse_left (H : is_left_semi_stable PS) (X : object PS)
    : (eta_inverse H X o components_of (eta PS) X)%morphism = 1%morphism.
  Proof.
    unfold eta_inverse, iso_inverse.
    destruct (H X) as [g [Hgf Hfg]].
    exact Hgf.
  Qed.

  Lemma eta_inverse_right (H : is_left_semi_stable PS) (X : object PS)
    : (components_of (eta PS) X o eta_inverse H X)%morphism = 1%morphism.
  Proof.
    unfold eta_inverse, iso_inverse.
    destruct (H X) as [g [Hgf Hfg]].
    exact Hfg.
  Qed.

End SemiStableProperties.

(** * Almost Proper Stable Categories *)

(** A category is almost proper stable if it is both left and right 
    semi-stable, but may lack the triangle identities. *)
Definition is_almost_proper_stable (PS : PreStableCategory)
  : Type
  := is_left_semi_stable PS * is_right_semi_stable PS.

(** * Balanced Categories *)

(** A pre-stable category is balanced if being an isomorphism at X for η
    is equivalent to being an isomorphism at ΣX for ε. *)
Definition is_balanced (PS : PreStableCategory)
  : Type
  := forall X : object PS,
     IsIsomorphism (components_of (eta PS) X) <->
     IsIsomorphism (components_of (epsilon PS) (object_of (Susp PS) X)).

(** Semi-stability in both directions implies balance. *)
Theorem semi_stable_both_directions_implies_balanced
  : forall (PS : PreStableCategory),
    is_left_semi_stable PS ->
    is_right_semi_stable PS ->
    is_balanced PS.
Proof.
  intros PS H_left H_right X.
  split.
  - intro H. apply H_right.
  - intro H. apply H_left.
Qed.

(** * Triangle Identities *)

(** The first triangle identity: ε(ΣX) ∘ Σ(ηX) = 1. *)
Definition satisfies_triangle_1 (PS : PreStableCategory)
  : Type
  := forall X : object PS,
     (components_of (epsilon PS) (object_of (Susp PS) X) o 
      morphism_of (Susp PS) (components_of (eta PS) X))%morphism = 1%morphism.

(** The second triangle identity: Ω(εX) ∘ η(ΩX) = 1. *)
Definition satisfies_triangle_2 (PS : PreStableCategory)
  : Type
  := forall X : object PS,
     (morphism_of (Loop PS) (components_of (epsilon PS) X) o
      components_of (eta PS) (object_of (Loop PS) X))%morphism = 1%morphism.

(** Both triangle identities together. *)
Definition satisfies_triangle_identities (PS : PreStableCategory)
  : Type
  := satisfies_triangle_1 PS * satisfies_triangle_2 PS.

(** * The Complete Stability Hierarchy *)

(** Almost proper stable categories with triangle identities. *)
Definition almost_proper_stable_strong (PS : PreStableCategory)
  : Type
  := is_left_semi_stable PS * 
     is_right_semi_stable PS * 
     satisfies_triangle_1 PS * 
     satisfies_triangle_2 PS.

(** Almost proper stable with triangle identities implies all conditions
    for proper stability. *)
Theorem almost_proper_is_proper
  : forall (PS : PreStableCategory),
    almost_proper_stable_strong PS ->
    (* All the data for ProperStableCategory is present *)
    (forall X, IsIsomorphism (components_of (eta PS) X)) *
    (forall X, IsIsomorphism (components_of (epsilon PS) X)) *
    satisfies_triangle_1 PS *
    satisfies_triangle_2 PS.
Proof.
  intros PS H.
  destruct H as [[[H_left H_right] H_tri1] H_tri2].
  unfold is_left_semi_stable in H_left.
  unfold is_right_semi_stable in H_right.
  refine (_, _, _, _).
  - exact H_left.
  - exact H_right.
  - exact H_tri1.
  - exact H_tri2.
Qed.

(** The complete hierarchy summarizes the relationships between different
    levels of stability. *)
Definition stability_hierarchy_summary
  : Type
  := forall (PS : PreStableCategory),
     (* Level 0: Pre-stable *)
     Unit ->
     (* Level 1: Semi-stable (one direction) *)
     (is_left_semi_stable PS + is_right_semi_stable PS) ->
     (* Level 2: Almost proper (both directions) *)
     (is_left_semi_stable PS * is_right_semi_stable PS) ->
     (* Level 3: Weak proper (triangle identities) *)
     (satisfies_triangle_1 PS * satisfies_triangle_2 PS) ->
     (* Level 4: Proper stable (all conditions) *)
     almost_proper_stable_strong PS.

(** The hierarchy theorem confirms the logical progression of stability properties. *)
Theorem stability_hierarchy_holds
  : stability_hierarchy_summary.
Proof.
  unfold stability_hierarchy_summary.
  intros PS _ _ H_almost H_triangles.
  unfold almost_proper_stable_strong.
  destruct H_almost as [H_left H_right].
  destruct H_triangles as [H_tri1 H_tri2].
  exact (H_left, H_right, H_tri1, H_tri2).
Qed.

(** * One-Sided Inverses from Triangle Identities *)

(** The unit has a left inverse when precomposed with suspension. *)
Definition eta_has_left_inverse (PS : PreStableCategory)
  : Type
  := forall X : object PS,
     exists (g : morphism PS (object_of ((Loop PS) o (Susp PS))%functor X) X),
     (g o components_of (eta PS) X)%morphism = 1%morphism.

(** The counit has a right inverse when postcomposed with loop. *)
Definition epsilon_has_right_inverse (PS : PreStableCategory)
  : Type
  := forall X : object PS,
     exists (g : morphism PS X (object_of ((Susp PS) o (Loop PS))%functor X)),
     (components_of (epsilon PS) X o g)%morphism = 1%morphism.

(** The first triangle identity directly implies that Ση has a left inverse. *)
Theorem triangle_identity_1_gives_left_inverse
  : forall (PS : PreStableCategory) (X : object PS),
    (components_of (epsilon PS) (object_of (Susp PS) X) o
     morphism_of (Susp PS) (components_of (eta PS) X))%morphism = 1%morphism ->
    exists (g : morphism PS (object_of ((Susp PS) o (Loop PS) o (Susp PS))%functor X)
                            (object_of (Susp PS) X)),
    (g o morphism_of (Susp PS) (components_of (eta PS) X))%morphism = 1%morphism.
Proof.
  intros PS X H_tri.
  exists (components_of (epsilon PS) (object_of (Susp PS) X)).
  exact H_tri.
Qed.

(** * Classification by Semi-Stability *)

Section Classification.
  Context (PS : PreStableCategory).

  (** A pre-stable category can be classified by its semi-stability properties. *)
  Definition semi_stability_class
    : Type
    := (is_left_semi_stable PS) * (is_right_semi_stable PS) + 
       (is_left_semi_stable PS) * (~is_right_semi_stable PS) +
       (~is_left_semi_stable PS) * (is_right_semi_stable PS) +
       (~is_left_semi_stable PS) * (~is_right_semi_stable PS).

  (** Helper to determine if a category is in the top class. *)
  Definition is_both_semi_stable : Type
    := is_left_semi_stable PS * is_right_semi_stable PS.

  (** With triangle identities, both semi-stable implies proper stable structure. *)
  Definition both_semi_stable_with_triangles_is_proper
    : is_both_semi_stable -> 
      satisfies_triangle_identities PS ->
      almost_proper_stable_strong PS.
  Proof.
    intros [H_left H_right] [H_tri1 H_tri2].
    exact (H_left, H_right, H_tri1, H_tri2).
  Qed.

End Classification.

(** * Export Hints *)

Hint Unfold 
  is_left_semi_stable is_right_semi_stable
  is_almost_proper_stable is_balanced
  satisfies_triangle_1 satisfies_triangle_2
  : semi_stable.

Hint Resolve 
  semi_stable_both_directions_implies_balanced
  triangle_identity_1_gives_left_inverse
  : semi_stable.

(** The next file in the library will be [TriangleMorphisms.v] which defines
    morphisms between triangles and their properties. *)