Require Import
 HoTTClasses.interfaces.abstract_algebra.

Section initial_maps.
  Variable A: Type.

  Class NaturalsToSemiRing :=
    naturals_to_semiring: ∀ B `{Mult B} `{Plus B} `{One B} `{Zero B}, A → B.

End initial_maps.

Class Naturals A {plus mult zero one} `{U: NaturalsToSemiRing A} :=
  { naturals_ring:> @SemiRing A plus mult zero one
  ; naturals_to_semiring_mor:> ∀ `{SemiRing B}, SemiRing_Morphism (naturals_to_semiring A B)
  ; naturals_initial: forall `{SemiRing B} {h : A -> B} `{!SemiRing_Morphism h},
    naturals_to_semiring A B = h }.

(* Specializable operations: *)
Class NatDistance N `{Plus N}
  := nat_distance_sig : ∀ x y : N, { z : N | x + z = y } + { z : N | y + z = x }.
Definition nat_distance `{nd : NatDistance N} (x y : N) :=
  match nat_distance_sig x y with
  | inl (n↾_) => n
  | inr (n↾_) => n
  end.
