(** To get all of the category theory library in scope with the proper qualified names, you should [Require Import categories.] or [Require Import HoTT.categories.] *)

(** First we give modules to all of the kinds of category theory constructions (corresponding to directories), so that we can refer to them as [Category.foo] or [Functor.foo] after [Require Import categories.] *)
Require Category.
Require Functor.
Require Export Category.Notations Functor.Notations.
