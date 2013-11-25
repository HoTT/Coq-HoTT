Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import FunctorCategory.Core NaturalTransformation.Paths Functor.Composition.Core NaturalTransformation.Composition.Core.
Require Import Functor.Pointwise.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope category_scope.
Local Open Scope functor_scope.
Local Open Scope natural_transformation_scope.

Section pointwise.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable C' : PreCategory.
  Variable D' : PreCategory.

  Local Ltac t :=
    path_natural_transformation; simpl;
    rewrite <- ?composition_of;
    try apply ap;
    first [ apply commutes
          | apply symmetry; apply commutes ].

  Definition pointwise_l
             (F G : Functor C D)
             (T : NaturalTransformation F G)
             (F' : Functor C' D')
  : NaturalTransformation (pointwise F F') (pointwise G F').
  Proof.
    refine (Build_NaturalTransformation
              (pointwise F F') (pointwise G F')
              (fun f : object (D -> C') => (F' o f) oL T)%natural_transformation
              _).
    abstract t.
  Defined.

  Definition pointwise_r
             (F : Functor C D)
             (F' G' : Functor C' D')
             (T' : NaturalTransformation F' G')
  : NaturalTransformation (pointwise F F') (pointwise F G').
  Proof.
    refine (Build_NaturalTransformation
              (pointwise F F') (pointwise F G')
              (fun f : object (D -> C') => T' oR f oR F)%natural_transformation
              _).
    abstract t.
  Defined.
End pointwise.
