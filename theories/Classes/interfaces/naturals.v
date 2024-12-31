Require Import
 HoTT.Classes.interfaces.abstract_algebra
 HoTT.Classes.interfaces.orders.

Class NaturalsToSemiRing@{i j} (A : Type@{i}) :=
  naturals_to_semiring: forall (B : Type@{j}) `{IsSemiCRing B}, A -> B.

Arguments naturals_to_semiring A {_} B {_ _ _ _ _} _.

Class Naturals A {Aap:Apart A} {Aplus Amult Azero Aone Ale Alt}
  `{U: NaturalsToSemiRing A} :=
  { naturals_ring : @IsSemiCRing A Aplus Amult Azero Aone
  ; naturals_order : FullPseudoSemiRingOrder Ale Alt
  ; naturals_to_semiring_mor : forall {B} `{IsSemiCRing B},
    IsSemiRingPreserving (naturals_to_semiring A B)
  ; naturals_initial: forall {B} `{IsSemiCRing B} {h : A -> B} `{!IsSemiRingPreserving h} x,
    naturals_to_semiring A B x = h x }.
#[export] Existing Instances naturals_ring naturals_order naturals_to_semiring_mor.

(* Specializable operations: *)
Class NatDistance N `{Plus N}
  := nat_distance_sig : forall x y : N, { z : N | x + z = y } |_|
                                   { z : N | y + z = x }.
Definition nat_distance {N} `{nd : NatDistance N} (x y : N) :=
  match nat_distance_sig x y with
  | inl (n;_) => n
  | inr (n;_) => n
  end.
