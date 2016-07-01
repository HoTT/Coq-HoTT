Require Import
 HoTTClasses.interfaces.abstract_algebra
 HoTTClasses.interfaces.orders.

Class NaturalsToSemiRing@{i j} (A : Type@{i}) :=
  naturals_to_semiring: ∀ (B : Type@{j}) `{SemiRing B}, A → B.

Arguments naturals_to_semiring A {_} B {_ _ _ _ _} _.

Class Naturals A {Aap:Apart A} {Aplus Amult Azero Aone Ale Alt}
  `{U: NaturalsToSemiRing A} :=
  { naturals_ring :> @SemiRing A Aplus Amult Azero Aone
  ; naturals_order :> FullPseudoSemiRingOrder Ale Alt
  ; naturals_to_semiring_mor:> ∀ `{SemiRing B},
    SemiRingPreserving (naturals_to_semiring A B)
  ; naturals_initial: forall `{SemiRing B} {h : A -> B} `{!SemiRingPreserving h} x,
    naturals_to_semiring A B x = h x }.

(* Specializable operations: *)
Class NatDistance N `{Plus N}
  := nat_distance_sig : ∀ x y : N, { z : N | x + z = y } + { z : N | y + z = x }.
Definition nat_distance `{nd : NatDistance N} (x y : N) :=
  match nat_distance_sig x y with
  | inl (n↾_) => n
  | inr (n↾_) => n
  end.
