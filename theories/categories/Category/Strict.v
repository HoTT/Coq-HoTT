Require Export Category.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Notation IsStrictCategory C := (IsHSet (object C)).

Record StrictCategory :=
  {
    precategory_strict :> PreCategory;
    isstrict_StrictCategory :> IsStrictCategory precategory_strict
  }.

Existing Instance isstrict_StrictCategory.
