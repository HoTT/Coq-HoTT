(** To get all of the category theory library in scope with the proper qualified names, you should [Require Import categories.] or [Require Import HoTT.categories.] *)

(** First we give modules to all of the kinds of category theory constructions (corresponding to directories), so that we can refer to them as [Category.foo] or [Functor.foo] after [Require Import categories.] *)
Require Category.
Require Functor.
Require NaturalTransformation.

(* We bind the record structures for [PreCategory], [IsCategory], [IsStrictCategory], [Functor], and eventually [NaturalTransformation] at top level. *)
Include Category.Core.
Include Category.Strict.
Include Category.Univalent.
Include Functor.Core.
Include NaturalTransformation.Core.

Require Export Category.Notations.
Require Export Functor.Notations.
Require Export NaturalTransformation.Notations.


(** Some checks that should pass, if all of the importing went correctly. *)
(*Check PreCategory.
Check IsStrictCategory _.
Check Category.compose.
Check Category.sum.
Check Category.Sum.sum_compose.
Check (_ o _)%morphism.
Check (_ o _)%functor.*)
