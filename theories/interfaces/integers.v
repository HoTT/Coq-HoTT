Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.naturals.

Section initial_maps.
  Variable A: Type.

  Class IntegersToRing :=
    integers_to_ring: ∀ R
      `{Ring R}, A → R.

End initial_maps.

Class Integers A {plus mult zero one negate} `{U : IntegersToRing A} :=
  { integers_ring:> @Ring A plus mult zero one negate
  ; integers_to_ring_mor:> ∀ `{Ring B}, SemiRingPreserving (integers_to_ring A B)
  ; integers_initial: forall `{Ring B} {h : A -> B} `{!SemiRingPreserving h} x,
      integers_to_ring A B x = h x}.

Section specializable.
  Context (Z N : Type) `{Integers Z} `{Naturals N}.

  Class IntAbs := int_abs_sig : ∀ x,
    { n : N | naturals_to_semiring N Z n = x } +
    { n : N | naturals_to_semiring N Z n = -x }.

  Definition int_abs `{ia : IntAbs} (x : Z) : N :=
    match int_abs_sig x with
    | inl (n↾_) => n
    | inr (n↾_) => n
    end.

  Definition int_to_nat `{Zero N} `{ia : IntAbs} (x : Z) : N :=
    match int_abs_sig x with
    | inl (n↾_) => n
    | inr (n↾_) => 0
    end.
End specializable.
