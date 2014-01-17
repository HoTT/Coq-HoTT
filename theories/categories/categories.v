(** To get all of the category theory library in scope with the proper qualified names, you should [Require Import categories.] or [Require Import HoTT.categories.] *)

(** First we give modules to all of the kinds of category theory constructions (corresponding to directories), so that we can refer to them as [Category.foo] or [Functor.foo] after [Require Import categories.] *)
Require Category.
Require Functor.
Require NaturalTransformation.
Require FunctorCategory.
Require GroupoidCategory.
Require DiscreteCategory.
Require IndiscreteCategory.
Require NatCategory.
Require InitialTerminalCategory.
Require SetCategory.
Require HomFunctor.
Require Profunctor.
Require Cat.
Require ExponentialLaws.
Require ProductLaws.
Require Comma.
Require UniversalProperties.
Require KanExtensions.
Require Adjoint.
Require Limits.
Require Pseudofunctor.
Require DualFunctor.
Require Grothendieck.
Require CategoryOfSections.
Require DependentProduct.
Require Yoneda.

(* We bind the record structures for [PreCategory], [IsCategory], [IsStrictCategory], [Functor], and eventually [NaturalTransformation] at top level. *)
Include Category.Core.
Include Category.Strict.
Include Category.Univalent.
Include Functor.Core.
Include NaturalTransformation.Core.
Include FunctorCategory.Core.
Include GroupoidCategory.Core.
Include DiscreteCategory.Core.
Include IndiscreteCategory.Core.
Include NatCategory.Core.
Include InitialTerminalCategory.Core.
Include SetCategory.Core.
Include HomFunctor.
Include Profunctor.Core.
Include Cat.Core.
Include Comma.Core.
Include UniversalProperties.
Include KanExtensions.Core.
Include Adjoint.Core.
Include Limits.Core.
Include Pseudofunctor.Core.
Include DualFunctor.
Include CategoryOfSections.Core.
Include DependentProduct.
Include Yoneda.

Require Export categories.Notations.

(** Some checks that should pass, if all of the importing went correctly. *)
(*Check PreCategory.
Check IsStrictCategory _.
Check Category.compose.
Check Category.sum.
Check Category.Sum.sum_compose.
Check Functor.sum.
Check Functor.Prod.unique.
Check (_ o _)%morphism.
Check (_ o _)%functor.*)
