(** * Category Theory *)
(** To get all of the category theory library in scope with the proper qualified names, you should [Require Import Categories.] or [Require Import HoTT.Categories.] *)

(** First we give modules to all of the kinds of category theory constructions (corresponding to directories), so that we can refer to them as [Category.foo] or [Functor.foo] after [Require Import Categories.] *)
(** ** Categories *)
Require Category.
(** ** Functors *)
Require Functor.
(** ** Natural Transformations *)
Require NaturalTransformation.
(** ** Functor Categories *)
Require FunctorCategory.
(** ** Groupoids *)
Require GroupoidCategory.
(** ** Precategory of Groupoids *)
Require CategoryOfGroupoids.
(** ** Discrete Categories *)
Require DiscreteCategory.
(** ** Indiscrete Categories *)
Require IndiscreteCategory.
(** ** Finite Discrete Categories (natural numbers as categories) *)
Require NatCategory.
(** ** Chain Categories [[n]] *)
Require ChainCategory.
(** ** Initial and Terminal Categories *)
Require InitialTerminalCategory.
(** ** The Category of Sets *)
Require SetCategory.
(** ** The Category of Simplicial Sets *)
Require SimplicialSets.
(** ** The Category of Semi-Simplicial Sets *)
Require SemiSimplicialSets.
(** ** The Hom Functor *)
Require HomFunctor.
(** ** Profunctors *)
Require Profunctor.
(** ** The Category of Categories *)
Require Cat.
(** ** Laws about Functor Categories *)
Require ExponentialLaws.
(** ** Laws about Product Categories *)
Require ProductLaws.
(** ** Comma Categories *)
Require Comma.
(** ** Universal Properties and Universal Morphisms *)
Require UniversalProperties.
(** ** Kan Extensions *)
Require KanExtensions.
(** ** Adjunctions *)
Require Adjoint.
(** ** Limits *)
Require Limits.
(** ** Pseudofunctors *)
Require Pseudofunctor.
(** ** Pseudonatural Transformations *)
Require PseudonaturalTransformation.
(** ** Lax Comma Categories *)
Require LaxComma.
(** ** Duality as a Functor *)
Require DualFunctor.
(** ** The Grothendieck Construction *)
Require Grothendieck.
(** ** The Category of Sections of a Functor *)
Require CategoryOfSections.
(** ** The Dependent Product *)
Require DependentProduct.
(** ** The Yoneda Lemma *)
Require Categories.Yoneda.
(** ** The Structure Identity Principle *)
Require Structure.
(** ** Fundamental Pregroupoids *)
Require FundamentalPreGroupoidCategory.
(** ** Homotopy PreCategory *)
Require HomotopyPreCategory.

(* We bind the record structures for [PreCategory], [IsCategory], [IsStrictCategory], [Functor], and eventually [NaturalTransformation] at top level. *)
Local Set Warnings Append "-notation-overridden".
Include Category.Core.
Include Category.Strict.
Include Category.Univalent.
Include Functor.Core.
Include NaturalTransformation.Core.
Include FunctorCategory.Core.
Include GroupoidCategory.Core.
Include CategoryOfGroupoids.
Include DiscreteCategory.Core.
Include IndiscreteCategory.Core.
Include NatCategory.Core.
Include ChainCategory.Core.
Include InitialTerminalCategory.Core.
Include SetCategory.Core.
Include SimplicialSets.Core.
Include SemiSimplicialSets.Core.
Include HomFunctor.
Include Profunctor.Core.
Include Cat.Core.
Include Comma.Core.
Include UniversalProperties.
Include KanExtensions.Core.
Include Adjoint.Core.
Include Limits.Core.
Include Pseudofunctor.Core.
Include PseudonaturalTransformation.Core.
Include LaxComma.Core.
Include DualFunctor.
Include CategoryOfSections.Core.
Include DependentProduct.
Include Categories.Yoneda.
Include Structure.Core.
Include FundamentalPreGroupoidCategory.
Include HomotopyPreCategory.

Require Export Categories.Notations.

(** Some checks that should pass, if all of the importing went correctly. *)
(*Check PreCategory.
Check IsStrictCategory _.
Check Category.compose.
Check Category.sum.
Check Category.Sum.sum_compose.
Check Functor.sum.
Check Functor.Prod.Core.unique.
Check (_ o _)%morphism.
Check (_ o _)%functor.*)
