Require Import Category.Core Category.Strict Functor.Core NaturalTransformation.Core Functor.Paths.
(** These must come last, so that [identity], [compose], etc., refer to natural transformations. *)
Require Import NaturalTransformation.Composition NaturalTransformation.Identity NaturalTransformation.CompositionLaws.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section functor_category.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.

  (** There is a category Fun(C, D) of functors from [C] to [D]. *)

  Definition functor_category : PreCategory
    := @Build_PreCategory (Functor C D)
                          (@NaturalTransformation C D)
                          (@identity C D)
                          (@compose C D)
                          (@associativity _ C D)
                          (@left_identity _ C D)
                          (@right_identity _ C D)
                          _.
End functor_category.

Local Notation "C -> D" := (functor_category C D) : category_scope.

Lemma isstrict_functor_category `{Funext} C `{IsStrictCategory D}
: IsStrictCategory (C -> D).
Proof.
  typeclasses eauto.
Defined.

Module Export FunctorCategoryCoreNotations.
  (*Notation "C ^ D" := (functor_category D C) : category_scope.
  Notation "[ C , D ]" := (functor_category C D) : category_scope.*)
  Notation "C -> D" := (functor_category C D) : category_scope.
End FunctorCategoryCoreNotations.
