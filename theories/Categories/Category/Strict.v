(** * Definition of a strict category *)
Require Export Category.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

(** Quoting the HoTT Book: *)
(** Definition. A _strict category_ is a precategory whose type of
    objects is a set. *)

Notation IsStrictCategory C := (IsHSet (object C)).

Record StrictCategory :=
  {
    category_strict :> Category;
    isstrict_StrictCategory :> IsStrictCategory category_strict
  }.

Global Existing Instance isstrict_StrictCategory.
