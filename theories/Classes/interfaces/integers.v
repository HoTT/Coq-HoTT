Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.orders
  HoTT.Classes.interfaces.naturals
  HoTT.Classes.theory.rings (* for Ring -> SemiRing *).

Class IntegersToRing@{i j} (A:Type@{i})
  := integers_to_ring: forall (R:Type@{j}) `{IsRing R}, A -> R.
Arguments integers_to_ring A {_} R {_ _ _ _ _ _} _.

Class Integers A {Aap:Apart A} {Aplus Amult Azero Aone Anegate Ale Alt}
  `{U : IntegersToRing A} :=
  { integers_ring :> @IsRing A Aplus Amult Azero Aone Anegate
  ; integers_order :> FullPseudoSemiRingOrder Ale Alt
  ; integers_to_ring_mor:> forall {B} `{IsRing B}, IsSemiRingPreserving (integers_to_ring A B)
  ; integers_initial: forall {B} `{IsRing B} {h : A -> B} `{!IsSemiRingPreserving h} x,
      integers_to_ring A B x = h x}.

Section specializable.
  Context (Z N : Type) `{Integers Z} `{Naturals N}.

  Class IntAbs := int_abs_sig : forall x,
    { n : N | naturals_to_semiring N Z n = x } |_|
    { n : N | naturals_to_semiring N Z n = -x }.

  Definition int_abs `{ia : IntAbs} (x : Z) : N :=
    match int_abs_sig x with
    | inl (n;_) => n
    | inr (n;_) => n
    end.

  Definition int_to_nat `{Zero N} `{ia : IntAbs} (x : Z) : N :=
    match int_abs_sig x with
    | inl (n;_) => n
    | inr (n;_) => 0
    end.
End specializable.
