(** * Category Theory *)
(** To get all of the category theory library in scope with the proper qualified names, you should [Require Import Categories.] or [Require Import HoTT.Categories.] *)

(** First we give modules to all of the kinds of category theory constructions (corresponding to directories), so that we can refer to them as [Category.foo] or [Functor.foo] after [Require Import Categories.] *)
(** ** Categories *)
Require HoTT.Categories.Category.
(** ** Functors *)
Require HoTT.Categories.Functor.
(** ** Natural Transformations *)
Require HoTT.Categories.NaturalTransformation.
(** ** Functor Categories *)
Require HoTT.Categories.FunctorCategory.
(** ** Groupoids *)
Require HoTT.Categories.GroupoidCategory.
(** ** Precategory of Groupoids *)
Require HoTT.Categories.CategoryOfGroupoids.
(** ** Discrete Categories *)
Require HoTT.Categories.DiscreteCategory.
(** ** Indiscrete Categories *)
Require HoTT.Categories.IndiscreteCategory.
(** ** Finite Discrete Categories (natural numbers as categories) *)
Require HoTT.Categories.NatCategory.
(** ** Chain Categories [[n]] *)
Require HoTT.Categories.ChainCategory.
(** ** Initial and Terminal Categories *)
Require HoTT.Categories.InitialTerminalCategory.
(** ** The Category of Sets *)
Require HoTT.Categories.SetCategory.
(** ** The Category of Simplicial Sets *)
Require HoTT.Categories.SimplicialSets.
(** ** The Category of Semi-Simplicial Sets *)
Require HoTT.Categories.SemiSimplicialSets.
(** ** The Hom Functor *)
Require HoTT.Categories.HomFunctor.
(** ** Profunctors *)
Require HoTT.Categories.Profunctor.
(** ** The Category of Categories *)
Require HoTT.Categories.Cat.
(** ** Laws about Functor Categories *)
Require HoTT.Categories.ExponentialLaws.
(** ** Laws about Product Categories *)
Require HoTT.Categories.ProductLaws.
(** ** Comma Categories *)
Require HoTT.Categories.Comma.
(** ** Universal Properties and Universal Morphisms *)
Require HoTT.Categories.UniversalProperties.
(** ** Kan Extensions *)
Require HoTT.Categories.KanExtensions.
(** ** Adjunctions *)
Require HoTT.Categories.Adjoint.
(** ** Limits *)
Require HoTT.Categories.Limits.
(** ** Pseudofunctors *)
Require HoTT.Categories.Pseudofunctor.
(** ** Pseudonatural Transformations *)
Require HoTT.Categories.PseudonaturalTransformation.
(** ** Lax Comma Categories *)
Require HoTT.Categories.LaxComma.
(** ** Duality as a Functor *)
Require HoTT.Categories.DualFunctor.
(** ** The Grothendieck Construction *)
Require HoTT.Categories.Grothendieck.
(** ** The Category of Sections of a Functor *)
Require HoTT.Categories.CategoryOfSections.
(** ** The Dependent Product *)
Require HoTT.Categories.DependentProduct.
(** ** The Yoneda Lemma *)
Require HoTT.Categories.Yoneda.
(** ** The Structure Identity Principle *)
Require HoTT.Categories.Structure.
(** ** Fundamental Pregroupoids *)
Require HoTT.Categories.FundamentalPreGroupoidCategory.
(** ** Homotopy PreCategory *)
Require HoTT.Categories.HomotopyPreCategory.

(* We bind the record structures for [PreCategory], [IsCategory], [IsStrictCategory], [Functor], and eventually [NaturalTransformation] at top level. *)
Local Set Warnings Append "-notation-overridden".
Include HoTT.Categories.Category.Core.
Include HoTT.Categories.Category.Strict.
Include HoTT.Categories.Category.Univalent.
Include HoTT.Categories.Functor.Core.
Include HoTT.Categories.NaturalTransformation.Core.
Include HoTT.Categories.FunctorCategory.Core.
Include HoTT.Categories.GroupoidCategory.Core.
Include HoTT.Categories.CategoryOfGroupoids.
Include HoTT.Categories.DiscreteCategory.Core.
Include HoTT.Categories.IndiscreteCategory.Core.
Include HoTT.Categories.NatCategory.Core.
Include HoTT.Categories.ChainCategory.Core.
Include HoTT.Categories.InitialTerminalCategory.Core.
Include HoTT.Categories.SetCategory.Core.
Include HoTT.Categories.SimplicialSets.Core.
Include HoTT.Categories.SemiSimplicialSets.Core.
Include HoTT.Categories.HomFunctor.
Include HoTT.Categories.Profunctor.Core.
Include HoTT.Categories.Cat.Core.
Include HoTT.Categories.Comma.Core.
Include HoTT.Categories.UniversalProperties.
Include HoTT.Categories.KanExtensions.Core.
Include HoTT.Categories.Adjoint.Core.
Include HoTT.Categories.Limits.Core.
Include HoTT.Categories.Pseudofunctor.Core.
Include HoTT.Categories.PseudonaturalTransformation.Core.
Include HoTT.Categories.LaxComma.Core.
Include HoTT.Categories.DualFunctor.
Include HoTT.Categories.CategoryOfSections.Core.
Include HoTT.Categories.DependentProduct.
Include HoTT.Categories.Yoneda.
Include HoTT.Categories.Structure.Core.
Include HoTT.Categories.FundamentalPreGroupoidCategory.
Include HoTT.Categories.HomotopyPreCategory.

Require Export HoTT.Categories.Notations.

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
