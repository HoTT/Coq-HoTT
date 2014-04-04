Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core NaturalTransformation.Composition.Core.
Require Import Category.Prod FunctorCategory.Core NaturalTransformation.Composition.Functorial NaturalTransformation.Composition.Laws ExponentialLaws.Law4.Functors.
Require Import NaturalTransformation.Paths.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Section functorial_composition.
  Context `{fs : Funext, fs' : Funext, fs'' : Funext, fs''' : Funext, fs'''' : Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Local Open Scope natural_transformation_scope.

  Definition compose_functor_morphism_of
             s d (m : morphism (@functor_category fs C D) s d)
  : morphism (@functor_category fs''' (@functor_category fs' D E) (@functor_category fs'' C E))
             (whiskerR_functor _ s)
             (whiskerR_functor _ d)
    := Build_NaturalTransformation
         (whiskerR_functor E s)
         (whiskerR_functor E d)
         (fun x => x oL m)
         (fun _ _ _ => exchange_whisker _ _).

  Definition compose_functor
  : object (@functor_category fs''''
                              (@functor_category fs C D)
                              (@functor_category fs''' (@functor_category fs' D E) (@functor_category fs'' C E))).
  Proof.
    refine (Build_Functor
              (C -> D) ((D -> E) -> (C -> E))
              (@whiskerR_functor _ _ _ _ _ _ _)
              compose_functor_morphism_of
              _
              _);
    abstract (
        path_natural_transformation;
        rewrite ?composition_of, ?identity_of;
        reflexivity
      ).
  Defined.

  Definition compose_functor_uncurried
  : object ((@functor_category fs C D) * (@functor_category fs' D E)
            -> (@functor_category fs'' C E))
    := ExponentialLaws.Law4.Functors.functor _ _ _ compose_functor.
End functorial_composition.
