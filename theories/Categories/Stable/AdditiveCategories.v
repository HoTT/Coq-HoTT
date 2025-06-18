(** * Additive Categories

    An additive category is a category enriched over abelian groups,
    with a zero object and biproducts for all pairs of objects.
    
    In this file, we focus on the structural aspects:
    - Categories with zero objects and biproducts
    - Additive functors that preserve this structure
    - Basic properties of additive functors
    
    Note: We don't yet define the abelian group structure on hom-sets,
    which would require additional machinery. We focus on the categorical
    structure that makes a category "additive-like".
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import Biproducts.

(** * Additive Categories *)

(** ** Definition
    
    An additive category has a zero object and biproducts for all pairs
    of objects. This is a key step toward abelian categories.
*)

Record AdditiveCategory := {
  cat :> PreCategory;
  
  add_zero : ZeroObject cat;
  
  add_biproduct : forall (X Y : object cat), Biproduct X Y add_zero
}.

(** ** Helper Functions *)

(** Access the zero object. *)
Definition zero_obj (A : AdditiveCategory) : object A
  := zero (add_zero A).

(** Zero morphism in an additive category. *)
Definition add_zero_morphism (A : AdditiveCategory) (X Y : object A)
  : morphism A X Y
  := zero_morphism (add_zero A) X Y.

(** Helper functions to access biproduct components. *)
Definition add_biproduct_data (A : AdditiveCategory) (X Y : object A)
  : BiproductData X Y
  := biproduct_data (add_biproduct A X Y).

Definition add_biproduct_obj (A : AdditiveCategory) (X Y : object A)
  : object A
  := biproduct_obj (add_biproduct_data A X Y).

(** Notation for biproduct object. *)
Notation "X ⊕ Y" := (add_biproduct_obj _ X Y) (at level 40, left associativity).

(** Biproduct injections. *)
Definition add_inl {A : AdditiveCategory} {X Y : object A}
  : morphism A X (X ⊕ Y)
  := inl (add_biproduct_data A X Y).

Definition add_inr {A : AdditiveCategory} {X Y : object A}
  : morphism A Y (X ⊕ Y)
  := inr (add_biproduct_data A X Y).

(** Biproduct projections. *)
Definition add_outl {A : AdditiveCategory} {X Y : object A}
  : morphism A (X ⊕ Y) X
  := outl (add_biproduct_data A X Y).

Definition add_outr {A : AdditiveCategory} {X Y : object A}
  : morphism A (X ⊕ Y) Y
  := outr (add_biproduct_data A X Y).

(** ** Basic Properties *)

Section AdditiveProperties.
  Context (A : AdditiveCategory).

(** The biproduct axioms hold. *)
  Lemma add_beta_l {X Y : object A}
    : (@add_outl A X Y o @add_inl A X Y)%morphism = 1%morphism.
  Proof.
    apply (beta_l (biproduct_is (add_biproduct A X Y))).
  Qed.

  Lemma add_beta_r {X Y : object A}
    : (@add_outr A X Y o @add_inr A X Y)%morphism = 1%morphism.
  Proof.
    apply (beta_r (biproduct_is (add_biproduct A X Y))).
  Qed.

  Lemma add_mixed_l {X Y : object A}
    : (@add_outl A X Y o @add_inr A X Y)%morphism = add_zero_morphism A Y X.
  Proof.
    apply (mixed_l (biproduct_is (add_biproduct A X Y))).
  Qed.

  Lemma add_mixed_r {X Y : object A}
    : (@add_outr A X Y o @add_inl A X Y)%morphism = add_zero_morphism A X Y.
  Proof.
    apply (mixed_r (biproduct_is (add_biproduct A X Y))).
  Qed.

  (** Universal property of biproducts. *)
  Definition add_coprod_mor {X Y Z : object A}
    (f : morphism A X Z) (g : morphism A Y Z)
    : morphism A (X ⊕ Y) Z
    := biproduct_coprod_mor (add_biproduct A X Y) Z f g.

  Lemma add_coprod_beta_l {X Y Z : object A}
    (f : morphism A X Z) (g : morphism A Y Z)
    : (add_coprod_mor f g o add_inl = f)%morphism.
  Proof.
    apply biproduct_coprod_beta_l.
  Qed.

  Lemma add_coprod_beta_r {X Y Z : object A}
    (f : morphism A X Z) (g : morphism A Y Z)
    : (add_coprod_mor f g o add_inr = g)%morphism.
  Proof.
    apply biproduct_coprod_beta_r.
  Qed.

  Definition add_prod_mor {X Y Z : object A}
    (f : morphism A Z X) (g : morphism A Z Y)
    : morphism A Z (X ⊕ Y)
    := biproduct_prod_mor (add_biproduct A X Y) Z f g.

  Lemma add_prod_beta_l {X Y Z : object A}
    (f : morphism A Z X) (g : morphism A Z Y)
    : (add_outl o add_prod_mor f g = f)%morphism.
  Proof.
    apply biproduct_prod_beta_l.
  Qed.

  Lemma add_prod_beta_r {X Y Z : object A}
    (f : morphism A Z X) (g : morphism A Z Y)
    : (add_outr o add_prod_mor f g = g)%morphism.
  Proof.
    apply biproduct_prod_beta_r.
  Qed.

End AdditiveProperties.

(** * Additive Functors *)

(** ** Definition
    
    An additive functor preserves the additive structure: zero objects
    and biproducts.
*)

Record AdditiveFunctor (A B : AdditiveCategory) := {
  add_functor :> Functor A B;
  
  preserves_zero : 
    object_of add_functor (zero_obj A) = zero_obj B;
  
  preserves_biproduct : forall (X Y : object A),
    object_of add_functor (X ⊕ Y) =
    (object_of add_functor X ⊕ object_of add_functor Y)
}.

(** ** Properties of Additive Functors *)

Section AdditiveFunctorProperties.
  Context {A B : AdditiveCategory} (F : AdditiveFunctor A B).

  (** Helper lemmas for preservation properties. *)
  
  (** Additive functors preserve initial morphisms. *)
  Lemma functor_preserves_initial_morphism (Y : object A)
    : transport (fun Z => morphism B Z (object_of F Y)) 
                (preserves_zero A B F)
                (morphism_of F (@center _ (is_initial (add_zero A) Y))) =
      @center _ (is_initial (add_zero B) (object_of F Y)).
  Proof.
    apply (@path_contr _ (is_initial (add_zero B) (object_of F Y))).
  Qed.

  (** Additive functors preserve terminal morphisms. *)
  Lemma functor_preserves_terminal_morphism (X : object A)
    : transport (fun Z => morphism B (object_of F X) Z) 
                (preserves_zero A B F)
                (morphism_of F (@center _ (is_terminal (add_zero A) X))) =
      @center _ (is_terminal (add_zero B) (object_of F X)).
  Proof.
    apply (@path_contr _ (is_terminal (add_zero B) (object_of F X))).
  Qed.

  (** ** Main Theorem: Additive Functors Preserve Zero Morphisms *)

  Theorem additive_functor_preserves_zero_morphisms (X Y : object A)
    : morphism_of F (add_zero_morphism A X Y) = 
      add_zero_morphism B (object_of F X) (object_of F Y).
  Proof.
    unfold add_zero_morphism, zero_morphism.
    rewrite composition_of.
    
    set (p := preserves_zero A B F).
    
    assert (H1: morphism_of F (@center _ (is_terminal (add_zero A) X)) =
                transport (fun Z => morphism B (object_of F X) Z) p^
                         (@center _ (is_terminal (add_zero B) (object_of F X)))).
    {
      apply transport_inverse_eq.
      apply functor_preserves_terminal_morphism.
    }
    
    assert (H2: morphism_of F (@center _ (is_initial (add_zero A) Y)) =
                transport (fun Z => morphism B Z (object_of F Y)) p^
                         (@center _ (is_initial (add_zero B) (object_of F Y)))).
    {
      apply morphism_eq_transport_inverse.
      apply functor_preserves_initial_morphism.
    }
    
    rewrite H1, H2.
    rewrite <- (transport_compose_both_inverse p^).
    reflexivity.
  Qed.

End AdditiveFunctorProperties.

(** * Examples and Constructions *)

(** The identity functor is additive. *)
Definition id_additive_functor (A : AdditiveCategory) 
  : AdditiveFunctor A A.
Proof.
  refine {|
    add_functor := 1%functor;
    preserves_zero := idpath;
    preserves_biproduct := fun X Y => idpath
  |}.
Defined.

(** Composition of additive functors is additive. *)
Definition compose_additive_functors {A B C : AdditiveCategory}
  (G : AdditiveFunctor B C) (F : AdditiveFunctor A B)
  : AdditiveFunctor A C.
Proof.
  refine {|
    add_functor := (G o F)%functor;
    preserves_zero := _;
    preserves_biproduct := _
  |}.
  - simpl. rewrite preserves_zero. apply preserves_zero.
  - intros X Y. simpl. 
    rewrite preserves_biproduct.
    rewrite preserves_biproduct.
    reflexivity.
Defined.

(** * Export Hints *)

Hint Resolve 
  add_beta_l add_beta_r
  add_coprod_beta_l add_coprod_beta_r
  add_prod_beta_l add_prod_beta_r
  : additive.

Hint Rewrite 
  @add_mixed_l @add_mixed_r
  @additive_functor_preserves_zero_morphisms
  : additive_simplify.

(** The next file in the library will be [PreStableCategories.v] which introduces
    suspension and loop functors. *)