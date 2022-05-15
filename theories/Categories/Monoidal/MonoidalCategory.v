Require Import Basics Basics.Utf8 Basics.Tactics.
Require Import implementations.list.
Require Import Category.Core Category.Prod Category.Morphisms.
Require Import NatCategory.
Require Import Functor.Core Functor.Identity Functor.Composition.Core Functor.Prod.Core
        Functor.Utf8.
Require Import NaturalTransformation.Core NaturalTransformation.Isomorphisms NaturalTransformation.Identity NaturalTransformation.Prod.
Require Import NaturalTransformation.Composition.Core.
Require Import FunctorCategory.Core FunctorCategory.Morphisms.
Require Import ProductLaws.
Require Import Cat.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Section MonoidalStructure.
Local Notation id := Functor.Identity.identity.
Local Notation "x --> y" := (morphism _ x y).
Local Open Scope category_scope.
Local Open Scope morphism_scope.
Local Notation "g ∘ f" := (Functor.Composition.Core.compose g f).
Context `{Funext}.
Section MonoidalCategoryConcepts.
  Variable C : PreCategory.
  Variable tensor : ((C * C) -> C)%category.
  Variable I : C.
  Local Notation "A ⊗ B" := (tensor (Datatypes.pair A B)) (at level 45, left associativity).
  Definition right_assoc := tensor ∘ (Functor.Prod.pair (id C) tensor).
  Definition left_assoc :=  tensor ∘
                                   (Functor.Prod.pair tensor (id C)) ∘
                                   (Associativity.functor _ _ _).
  Definition associator := NaturalIsomorphism right_assoc left_assoc.
  (* Orientation  (A ⊗ B) ⊗ C -> A ⊗ (B ⊗ C) *)
  Definition pretensor (A : C) := Core.induced_snd tensor A.
  Definition I_pretensor := pretensor I.
  Definition posttensor (A : C) := Core.induced_fst tensor A.
  Definition I_posttensor := posttensor I.
  Definition left_unitor := NaturalIsomorphism I_pretensor (id C).
  Definition right_unitor := NaturalIsomorphism I_posttensor (id C).

  Variable alpha : associator.
  Variable lambda : left_unitor.
  Variable rho : right_unitor.
  Notation alpha_nat_trans := ((@morphism_isomorphic
                                  (C * (C * C) -> C)%category right_assoc left_assoc) alpha).
  Notation lambda_nat_trans := ((@morphism_isomorphic _ _ _) lambda).
  Notation rho_nat_trans := ((@morphism_isomorphic _ _ _) rho).

  Section coherence_laws.
    Variable a b c d : C.
  Local Definition P1 : (a ⊗ (b ⊗ (c ⊗ d))) --> (a ⊗ ((b ⊗ c) ⊗ d)).
  Proof.
    apply (morphism_of tensor); split; simpl.
    - exact (Core.identity a).
    - exact (alpha_nat_trans (b, (c, d))).
  Defined.

  Local Definition P2 : a ⊗ ((b ⊗ c) ⊗ d) --> (a ⊗ (b ⊗ c)) ⊗ d
    := alpha_nat_trans (a, (b ⊗ c, d)).
  Local Definition P3 : (a ⊗ (b ⊗ c)) ⊗ d --> ((a ⊗ b) ⊗ c ) ⊗ d.
  Proof.
    apply (morphism_of tensor); split; simpl.
    - exact (alpha_nat_trans (a,_)).
    - exact (Core.identity d).
  Defined.
  Local Definition P4 : a ⊗ (b ⊗ (c ⊗ d)) --> (a ⊗ b) ⊗ (c ⊗ d)
    := alpha_nat_trans (a, (b, (c ⊗ d))).
  Local Definition P5 : (a ⊗ b) ⊗ (c ⊗ d) --> ((a ⊗ b) ⊗ c ) ⊗ d
    := alpha_nat_trans (a ⊗ b,(c, d)).

  Definition pentagon_eq := P3 o P2 o P1 = P5 o P4.

  Local Definition Q1 : (a ⊗ (I ⊗ b)) --> a ⊗ b.
  Proof.
    apply (morphism_of tensor); split; simpl.
    - exact (Core.identity a).
    - exact (lambda_nat_trans _).
  Defined.

  Local Definition Q2 : (a ⊗ (I ⊗ b)) --> a ⊗ b.
  Proof.
    refine (@Category.Core.compose _ _ ((a ⊗ I) ⊗ b) _ _ _).
    - apply (morphism_of tensor); split; simpl.
      + exact (rho_nat_trans a).
      + exact (Core.identity b).
    - exact (alpha_nat_trans (a,(I,b))).
  Defined.
  Definition triangle_eq := Q1 = Q2.
  End coherence_laws.
End MonoidalCategoryConcepts.

Class MonoidalStructure (C : PreCategory) :=
  Build_MonoidalStructure {
    tensor : (C * C -> C)%category;
    I : C;
    alpha : associator tensor;
    lambda : left_unitor tensor I;
    rho : right_unitor tensor I;
    pentagon_eq_holds : forall a b c d : C, pentagon_eq alpha a b c d;
    triangle_eq_holds : forall a b : C, triangle_eq alpha lambda rho a b;
  }.

End MonoidalStructure.
