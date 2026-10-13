From HoTT Require Import Basics.
From HoTT.Analysis Require Import IntervalObject.

(** Being a convex body, having an iteration operator and being an interval object are propositions, and typeclass search finds this. *)
Section Props.
  Context `{Funext}.

  Definition test_ishprop_isconvexbody (A : Type) {Am : Midpoint A}
    : IsHProp (IsConvexBody A)
    := _.

  Definition test_ishprop_iterationoperator (A : Type) {Am : Midpoint A} `{IsHSet A}
    : IsHProp (IterationOperator A)
    := _.

  Definition test_ishprop_isintervalobject (A : BipointedConvexBody)
    : IsHProp (IsIntervalObject A)
    := _.
End Props.
