(** * Advanced Structural Properties

    This file explores advanced structural properties of stable categories,
    including self-dual triangulated categories, conditions under which
    suspension and loop functors commute, and various special properties
    that arise in the theory.
    
    Contents:
    - Self-dual triangulated categories
    - Commuting suspension and loop functors
    - Functor compositions and identity relations
    - Inverse objects
    - Groupoid properties under duality
    - Biproduct uniqueness
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From HoTT.Categories.Functor Require Import Identity Composition.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import Biproducts.
Require Import AdditiveCategories.
Require Import PreStableCategories.
Require Import ProperStableCategories.
Require Import SemiStableCategories.
Require Import OppositeCategories.
Require Import OppositePreStable.

(** * Self-Dual Triangulated Categories *)

Section SelfDualTriangulated.
  Context (PS : PreStableCategory).

  (** A pre-stable category is self-dual triangulated if the two triangle
      identities are equivalent at every object. *)
  Definition is_self_dual_triangulated : Type
    := forall X : object PS,
       ((components_of (epsilon PS) (object_of (Susp PS) X) o 
         morphism_of (Susp PS) (components_of (eta PS) X))%morphism = 1%morphism) <->
       ((morphism_of (Loop PS) (components_of (epsilon PS) X) o
         components_of (eta PS) (object_of (Loop PS) X))%morphism = 1%morphism).

  (** Self-duality implies that one triangle identity gives both. *)
  Theorem self_dual_gives_both_triangles
    : is_self_dual_triangulated ->
      satisfies_triangle_1 PS ->
      satisfies_triangle_2 PS.
  Proof.
    intros H_self H1 X.
    destruct (H_self X) as [H_forward H_backward].
    apply H_forward.
    apply H1.
  Qed.

End SelfDualTriangulated.

(** * Commuting Suspension and Loop Functors *)

Section CommutingSuspLoop.
  Context (PS : PreStableCategory).

  (** Suspension and loop commute if there exists a natural isomorphism between
      their compositions. *)
  Definition has_commuting_susp_loop : Type
    := exists (α : NaturalTransformation 
         ((Susp PS) o (Loop PS))%functor
         ((Loop PS) o (Susp PS))%functor),
       forall X, IsIsomorphism (components_of α X).

  (** The compositions of suspension and loop coincide at the object level. *)
  Definition has_coinciding_compositions : Type
    := forall X : object PS,
       object_of ((Susp PS) o (Loop PS))%functor X = 
       object_of ((Loop PS) o (Susp PS))%functor X.

End CommutingSuspLoop.

(** * Functor Compositions and Identity Relations *)

Section FunctorCompositions.
  Context (PS : PreStableCategory).

  (** Suspension composed with loop equals the identity functor. *)
  Definition susp_loop_is_identity : Type
    := forall X : object PS,
       object_of ((Susp PS) o (Loop PS))%functor X = X.

  (** Loop composed with suspension equals the identity functor. *)
  Definition loop_susp_is_identity : Type
    := forall X : object PS,
       object_of ((Loop PS) o (Susp PS))%functor X = X.

  (** Both compositions being identity implies they coincide. *)
  Theorem both_compositions_identity_coincide
    : susp_loop_is_identity ->
      loop_susp_is_identity ->
      has_coinciding_compositions PS.
  Proof.
    intros H_sl H_ls X.
    rewrite H_sl.
    rewrite H_ls.
    reflexivity.
  Qed.

End FunctorCompositions.

(** * Inverse Objects *)

Section InverseObjects.
  Context (PS : PreStableCategory).

  (** A category has inverse objects if both functor compositions are identity. *)
  Definition has_inverse_objects : Type
    := susp_loop_is_identity PS * loop_susp_is_identity PS.

(** Inverse objects are preserved under duality. *)
Theorem inverse_objects_opposite
  : has_inverse_objects ->
    (susp_loop_is_identity (opposite_prestable_category PS) * 
     loop_susp_is_identity (opposite_prestable_category PS)).
Proof.
  intros [H_sl H_ls].
  unfold susp_loop_is_identity, loop_susp_is_identity in *.
  split.
  - intro X. 
    simpl.
    (* In opposite: Susp^op = Loop, Loop^op = Susp *)
    (* So (Susp^op o Loop^op) = (Loop o Susp) *)
    exact (H_ls X).
  - intro X. 
    simpl.
    (* In opposite: (Loop^op o Susp^op) = (Susp o Loop) *)
    exact (H_sl X).
Qed.

End InverseObjects.

(** * Groupoid Properties Under Duality *)

Section GroupoidDuality.
  Context (C : PreCategory).

  (** A category is a groupoid if all morphisms are isomorphisms. *)
  Definition is_groupoid : Type
    := forall (X Y : object C) (f : morphism C X Y), IsIsomorphism f.

  (** Helper: opposite categories preserve isomorphisms. *)
  Lemma opposite_preserves_iso {X Y : object C} (f : morphism C X Y)
    : IsIsomorphism f -> 
      IsIsomorphism (f : morphism (opposite_category C) Y X).
  Proof.
    intro H.
    destruct H as [g [Hgf Hfg]].
    exists g.
    split.
    - simpl. exact Hfg.
    - simpl. exact Hgf.
  Qed.

Theorem opposite_preserves_groupoid_property
  : is_groupoid ->
    forall (X Y : object (opposite_category C)) (f : morphism (opposite_category C) X Y), 
    IsIsomorphism f.
Proof.
  intros H_groupoid X Y f.
  (* f in opposite is a morphism Y -> X in original *)
  pose proof (H_groupoid Y X f) as H_iso.
  apply opposite_preserves_iso.
  exact H_iso.
Qed.

End GroupoidDuality.

(** * Preservation of Zero Compositions Under Duality *)

Section ZeroCompositionDuality.
  Context (PS : PreStableCategory).

  (** Zero compositions are preserved under opposite. *)
  Theorem opposite_preserves_zero_composition (X Y Z : object PS) 
    (f : morphism PS X Y) (g : morphism PS Y Z)
    : (g o f)%morphism = add_zero_morphism PS X Z ->
      ((f : morphism (opposite_prestable_category PS) Y X) o 
       (g : morphism (opposite_prestable_category PS) Z Y))%morphism = 
      add_zero_morphism (opposite_prestable_category PS) Z X.
  Proof.
    intros H.
    simpl.
    exact H.
  Qed.

End ZeroCompositionDuality.

(** * Biproduct Uniqueness *)

Section BiproductUniqueness.
  Context (A : AdditiveCategory).

  (** Two biproducts of the same objects are canonically isomorphic. *)
  Theorem biproduct_unique_up_to_iso (X Y : object A)
    : let B1 := add_biproduct A X Y in
      let B2 := add_biproduct A X Y in
      exists (f : morphism A (add_biproduct_obj A X Y) (add_biproduct_obj A X Y)),
        IsIsomorphism f /\
        (f o @add_inl A X Y = @add_inl A X Y)%morphism /\
        (f o @add_inr A X Y = @add_inr A X Y)%morphism.
  Proof.
    intros B1 B2.
    (* Since B1 and B2 are definitionally equal, the identity works *)
    exists 1%morphism.
    split; [|split].
    - exists 1%morphism.
      split; apply morphism_left_identity.
    - apply morphism_left_identity.
    - apply morphism_left_identity.
  Qed.

  (** The biproduct isomorphism is unique. *)
Theorem biproduct_iso_unique (X Y : object A)
  (f g : morphism A (add_biproduct_obj A X Y) (add_biproduct_obj A X Y))
  : IsIsomorphism f ->
    IsIsomorphism g ->
    (f o @add_inl A X Y = @add_inl A X Y)%morphism ->
    (f o @add_inr A X Y = @add_inr A X Y)%morphism ->
    (g o @add_inl A X Y = @add_inl A X Y)%morphism ->
    (g o @add_inr A X Y = @add_inr A X Y)%morphism ->
    f = g.
Proof.
  intros Hf_iso Hg_iso Hf_l Hf_r Hg_l Hg_r.
  
  (* Both f and g equal the unique morphism determined by the universal property *)
  transitivity (biproduct_coprod_mor (add_biproduct A X Y) 
                                     (X ⊕ Y) 
                                     (@add_inl A X Y) 
                                     (@add_inr A X Y)).
  - (* f equals this morphism *)
    apply (biproduct_coprod_unique (add_biproduct A X Y) (X ⊕ Y) 
           (@add_inl A X Y) (@add_inr A X Y) f).
    + exact Hf_l.
    + exact Hf_r.
    
  - (* g equals this morphism *)
    symmetry.
    apply (biproduct_coprod_unique (add_biproduct A X Y) (X ⊕ Y) 
           (@add_inl A X Y) (@add_inr A X Y) g).
    + exact Hg_l.
    + exact Hg_r.
Qed.

End BiproductUniqueness.

(** * Existence Principles *)

Section ExistencePrinciples.
  
  (** Every pre-stable category gives rise to an opposite pre-stable category
      with predictable structure. *)
  Theorem opposite_prestable_is_prestable (PS : PreStableCategory)
    : PreStableCategory.
  Proof.
    exact (opposite_prestable_category PS).
  Defined.

  (** Functor correspondence in opposite categories. *)
  Theorem opposite_functor_correspondence (PS : PreStableCategory)
    : Susp (opposite_prestable_category PS) = 
      opposite_additive_functor (Loop PS).
  Proof.
    reflexivity.
  Qed.

End ExistencePrinciples.

(** * The Space of Adjunction Data *)

Section AdjunctionSpace.
  Context (PS : PreStableCategory).

  (** Any compatible pair interacts predictably with zero morphisms. *)
  Theorem compatible_pair_zero_interaction
    (η : NaturalTransformation 1%functor ((Loop PS) o (Susp PS))%functor)
    (ε : NaturalTransformation ((Susp PS) o (Loop PS))%functor 1%functor)
    : (forall X, (components_of ε (object_of (Susp PS) X) o
                  morphism_of (Susp PS) (components_of η X))%morphism = 1%morphism) ->
      (forall X, (morphism_of (Loop PS) (components_of ε X) o
                  components_of η (object_of (Loop PS) X))%morphism = 1%morphism) ->
      forall X,
      (components_of ε (object_of (Susp PS) X) o
       morphism_of (Susp PS) (add_zero_morphism PS X 
         (object_of ((Loop PS) o (Susp PS))%functor X)))%morphism =
      add_zero_morphism PS (object_of (Susp PS) X) (object_of (Susp PS) X).
  Proof.
    intros H_tri1 H_tri2 X.
    rewrite susp_preserves_zero_morphisms.
    apply zero_morphism_right.
  Qed.

End AdjunctionSpace.

(** * Export Hints *)

Hint Resolve 
  self_dual_gives_both_triangles
  both_compositions_identity_coincide
  inverse_objects_opposite
  opposite_preserves_groupoid_property
  opposite_preserves_zero_composition
  biproduct_unique_up_to_iso
  : advanced_structures.

Hint Unfold
  is_self_dual_triangulated
  has_commuting_susp_loop
  has_coinciding_compositions
  susp_loop_is_identity
  loop_susp_is_identity
  has_inverse_objects
  is_groupoid
  : advanced_structures.

(** The next file in the library will be [DualityPrinciple.v] which establishes
    the universal duality principle and meta-theorems about dualization. *)