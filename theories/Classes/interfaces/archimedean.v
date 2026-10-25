From HoTT.Classes Require Import
     interfaces.abstract_algebra
     interfaces.rationals
     interfaces.orders
     theory.rings
     orders.semirings.

Section property.
  Context (Q : Type).
  Context `{Qrats : Rationals Q}.
  Context (F : Type).
  Context `{Aorderedfield : OrderedField F}.

  Definition qinc : Cast Q F := rationals_to_field Q F.
  Existing Instance qinc.

  Class ArchimedeanProperty := archimedean_property
    : forall x y, x < y -> hexists (fun q => x < ' q < y).

End property.
