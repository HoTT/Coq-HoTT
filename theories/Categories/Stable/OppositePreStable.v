(** * Opposite Pre-Stable Categories

    This file shows how pre-stable structures behave under the opposite
    construction. The key insight: in the opposite category, suspension 
    and loop functors swap roles.
    
    Contents:
    - Opposite functors
    - Opposite additive functors
    - Opposite natural transformations
    - Opposite pre-stable categories
    - Suspension and loop duality
    - Basic properties
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From HoTT.Categories.Functor Require Import Identity Composition.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import Biproducts.
Require Import AdditiveCategories.
Require Import PreStableCategories.
Require Import OppositeCategories.

(** * Opposite Functors *)

Definition opposite_functor {C D : PreCategory} (F : Functor C D)
  : Functor (opposite_category C) (opposite_category D).
Proof.
  exact (Build_Functor
    (opposite_category C) (opposite_category D)
    (object_of F)
    (fun X Y f => morphism_of F f)
    (fun X Y Z f g => composition_of F Z Y X g f)
    (fun X => identity_of F X)).
Defined.

(** * Opposite Additive Functors *)

Section OppositeAdditiveFunctor.
  Context {A B : AdditiveCategory} (F : AdditiveFunctor A B).

  Definition opposite_additive_functor
    : AdditiveFunctor (opposite_additive_category A) (opposite_additive_category B).
  Proof.
    exact (Build_AdditiveFunctor
      (opposite_additive_category A) (opposite_additive_category B)
      (opposite_functor F)
      (preserves_zero A B F)
      (fun X Y => preserves_biproduct A B F Y X)).
  Defined.

End OppositeAdditiveFunctor.

(** * Opposite Natural Transformations *)

Definition opposite_natural_transformation {C D : PreCategory} 
  {F G : Functor C D} (η : NaturalTransformation F G)
  : NaturalTransformation (opposite_functor G) (opposite_functor F).
Proof.
  exact (Build_NaturalTransformation
    (opposite_functor G) (opposite_functor F)
    (fun X => components_of η X)
    (fun X Y f => (commutes η Y X f)^)).
Defined.

(** * Opposite Pre-Stable Categories *)

(** The key insight: in the opposite category, suspension and loop functors swap roles. *)
Definition opposite_prestable_category (PS : PreStableCategory)
  : PreStableCategory.
Proof.
  exact (Build_PreStableCategory
    (opposite_additive_category PS)
    (opposite_additive_functor (Loop PS))  (* Loop becomes Susp *)
    (opposite_additive_functor (Susp PS))  (* Susp becomes Loop *)
    (opposite_natural_transformation (epsilon PS))  (* epsilon becomes eta *)
    (opposite_natural_transformation (eta PS))).     (* eta becomes epsilon *)
Defined.

(** * Basic Properties *)

Section OppositePreStableProperties.
  Context (PS : PreStableCategory).

  (** Opposite pre-stable exists. *)
  Theorem opposite_prestable_exists
    : exists (PS_op : PreStableCategory),
      A PS_op = opposite_additive_category PS.
  Proof.
    exists (opposite_prestable_category PS).
    reflexivity.
  Qed.

  (** Morphisms flip in the opposite. *)
  Theorem opposite_morphisms_flip (X Y : object PS)
    : morphism (opposite_prestable_category PS) X Y = morphism PS Y X.
  Proof.
    reflexivity.
  Qed.

  (** The fundamental duality: suspension and loop functors swap. *)
  Theorem suspension_loop_swap (X : object PS)
    : (object_of (Susp (opposite_prestable_category PS)) X = 
       object_of (Loop PS) X) /\
      (object_of (Loop (opposite_prestable_category PS)) X = 
       object_of (Susp PS) X).
  Proof.
    split; simpl; reflexivity.
  Qed.

  (** Zero morphisms dualize correctly. *)
  Theorem zero_morphism_dualizes (X Y : object PS)
    : add_zero_morphism (opposite_prestable_category PS) Y X = 
      add_zero_morphism PS X Y.
  Proof.
    unfold add_zero_morphism.
    apply zero_morphism_opposite.
  Qed.

  (** Composition reverses in the opposite category. *)
  Lemma opposite_composition_demo 
    (X Y Z : object PS)
    (f : morphism PS X Y) (g : morphism PS Y Z)
    : let original_composition := (g o f)%morphism in
      let f_op : morphism (opposite_prestable_category PS) Y X := f in
      let g_op : morphism (opposite_prestable_category PS) Z Y := g in
      let opposite_composition := (f_op o g_op)%morphism in
      opposite_composition = original_composition.
  Proof.
    simpl.
    reflexivity.
  Qed.

End OppositePreStableProperties.

(** * Opposite Natural Transformation Components *)

Section OppositeNaturalTransformationComponents.
  Context (PS : PreStableCategory).

  (** Components of opposite natural transformations. *)
  Lemma opposite_nat_trans_components
    {F G : Functor PS PS}
    (η : NaturalTransformation F G) (X : object PS)
    : components_of (opposite_natural_transformation η) X = components_of η X.
  Proof.
    reflexivity.
  Qed.

  (** The eta component in the opposite. *)
  Lemma opposite_eta_component (X : object PS)
    : components_of (eta (opposite_prestable_category PS)) X =
      components_of (epsilon PS) X.
  Proof.
    reflexivity.
  Qed.

  (** The epsilon component in the opposite. *)
  Lemma opposite_epsilon_component (X : object PS)
    : components_of (epsilon (opposite_prestable_category PS)) X =
      components_of (eta PS) X.
  Proof.
    reflexivity.
  Qed.

End OppositeNaturalTransformationComponents.

(** * Functor Actions on Morphisms *)

Section FunctorActions.
  Context (PS : PreStableCategory).

  (** How suspension acts on morphisms in the opposite. *)
  Lemma opposite_susp_morphism {X Y : object PS} (f : morphism PS X Y)
    : morphism_of (Susp (opposite_prestable_category PS)) f =
      morphism_of (Loop PS) f.
  Proof.
    reflexivity.
  Qed.

  (** How loop acts on morphisms in the opposite. *)
  Lemma opposite_loop_morphism {X Y : object PS} (f : morphism PS X Y)
    : morphism_of (Loop (opposite_prestable_category PS)) f =
      morphism_of (Susp PS) f.
  Proof.
    reflexivity.
  Qed.

End FunctorActions.

(** * Double Opposite Properties *)

Section DoubleOppositePreStable.
  Context (PS : PreStableCategory).

  (** Double opposite recovers the original functor structure. *)
  Theorem double_opposite_susp_commutes
    : object_of (Susp PS) = 
      object_of (Susp (opposite_prestable_category 
                       (opposite_prestable_category PS))).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Theorem double_opposite_loop_commutes
    : object_of (Loop PS) = 
      object_of (Loop (opposite_prestable_category 
                       (opposite_prestable_category PS))).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Theorem double_opposite_eta_components (X : object PS)
    : components_of (eta PS) X =
      components_of (eta (opposite_prestable_category 
                         (opposite_prestable_category PS))) X.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Theorem double_opposite_epsilon_components (X : object PS)
    : components_of (epsilon PS) X =
      components_of (epsilon (opposite_prestable_category 
                             (opposite_prestable_category PS))) X.
  Proof.
    simpl.
    reflexivity.
  Qed.

End DoubleOppositePreStable.

(** * Natural Transformation Preservation *)

Section NaturalTransformationPreservation.
  Context (PS : PreStableCategory).

  (** Naturality is built into the definition of opposite_natural_transformation.
      The naturality square for epsilon in the original category automatically
      gives the naturality square for eta in the opposite category. 
      
      The key is that opposite_natural_transformation includes (commutes η Y X f)^
      which provides exactly the reversal needed for naturality in the opposite category. *)
  
  (** To see how naturality works, we can verify it's built into eta of the opposite. *)
  Lemma opposite_eta_naturality
    {X Y : object PS} (f : morphism PS Y X)  (* Note: reversed *)
    : (* This is the naturality square for eta in the opposite category *)
      (components_of (eta (opposite_prestable_category PS)) Y o f)%morphism =
      (morphism_of ((Loop (opposite_prestable_category PS)) o 
                    (Susp (opposite_prestable_category PS)))%functor f o
       components_of (eta (opposite_prestable_category PS)) X)%morphism.
  Proof.
    (* eta in opposite is epsilon, and the functors are swapped *)
    change (components_of (eta (opposite_prestable_category PS))) with
           (fun X => components_of (epsilon PS) X).
    change (Loop (opposite_prestable_category PS)) with
           (opposite_additive_functor (Susp PS)).
    change (Susp (opposite_prestable_category PS)) with
           (opposite_additive_functor (Loop PS)).
    simpl.
    (* Now we have: epsilon Y ∘ f = f ∘ epsilon X, which is exactly
       the inverse of the naturality square for epsilon *)
    exact (commutes (opposite_natural_transformation (epsilon PS)) X Y f).
  Qed.

End NaturalTransformationPreservation.

(** * Summary Theorem *)

(** The complete duality theorem for pre-stable categories. *)
Theorem prestable_duality_theorem (PS : PreStableCategory)
  : (* 1. Underlying category dualizes *)
    (A (opposite_prestable_category PS) = opposite_additive_category PS) /\
    (* 2. Functors swap *)
    (forall X, object_of (Susp (opposite_prestable_category PS)) X = 
               object_of (Loop PS) X) /\
    (forall X, object_of (Loop (opposite_prestable_category PS)) X = 
               object_of (Susp PS) X) /\
    (* 3. Natural transformations swap *)
    (forall X, components_of (eta (opposite_prestable_category PS)) X =
               components_of (epsilon PS) X) /\
    (forall X, components_of (epsilon (opposite_prestable_category PS)) X =
               components_of (eta PS) X).
Proof.
  split; [|split; [|split; [|split]]].
  - reflexivity.
  - intro X. reflexivity.
  - intro X. reflexivity.
  - intro X. reflexivity.
  - intro X. reflexivity.
Qed.

(** * Export Hints *)

Hint Resolve 
  suspension_loop_swap
  zero_morphism_dualizes
  : opposite_prestable.

Hint Rewrite
  @opposite_eta_component
  @opposite_epsilon_component
  @opposite_susp_morphism
  @opposite_loop_morphism
  : opposite_simplify.

(** The next file in the library will be [ProperStableCategories.v] which defines
    proper stable categories where the suspension and loop functors are 
    inverse equivalences. *)