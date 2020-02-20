Require Import
        HoTT.Classes.interfaces.abstract_algebra
        HoTT.Classes.interfaces.orders
        HoTT.Classes.interfaces.naturals
        HoTT.Classes.implementations.peano_naturals.

Section round_up.

  Class RoundUpStrict A `{IsSemiRing A} `{StrictSemiRingOrder A}
    := round_up_strict : forall a : A, {n : nat & a < naturals_to_semiring nat A n}.
  Global Arguments round_up_strict A {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} _.

End round_up.
