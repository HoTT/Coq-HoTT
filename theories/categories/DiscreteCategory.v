Require Import Category.Core GroupoidCategory.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Module Export Core.
  Definition discrete_category X `{IsHSet X} := groupoid_category X.

  Arguments discrete_category X {_} / .
End Core.
