(* General results about arbitrary integer implementations. *)
Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable.
Require
 HoTTClasses.theory.nat_distance.
Require Import
 HoTTClasses.interfaces.naturals
 HoTTClasses.interfaces.abstract_algebra
 HoTTClasses.implementations.natpair_integers
 HoTTClasses.isomorphisms.rings.
Require Export
 HoTTClasses.interfaces.integers.


Lemma to_ring_unique `{Integers Z} `{Ring R} (f: Z → R)
  {h: SemiRing_Morphism f} x
  : f x = integers_to_ring Z R x.
Proof.
symmetry. apply integers_initial.
Qed.

Lemma to_ring_unique_alt `{Integers Z} `{Ring R} (f g: Z → R)
  `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} x :
  f x = g x.
Proof.
rewrite (to_ring_unique f), (to_ring_unique g);reflexivity.
Qed.

Lemma to_ring_involutive Z `{Integers Z} Z2 `{Integers Z2} x :
  integers_to_ring Z2 Z (integers_to_ring Z Z2 x) = x.
Proof.
change (compose (integers_to_ring Z2 Z) (integers_to_ring Z Z2) x = id x).
apply to_ring_unique_alt;apply _.
Qed.

Lemma morphisms_involutive `{Integers Z} `{Ring R} (f: R → Z) (g: Z → R)
  `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} x : f (g x) = x.
Proof (to_ring_unique_alt (f ∘ g) id _).

Lemma to_ring_twice `{Integers Z} `{Ring R1} `{Ring R2}
  (f : R1 → R2) (g : Z → R1) (h : Z → R2)
  `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} `{!SemiRing_Morphism h} x
  : f (g x) = h x.
Proof (to_ring_unique_alt (f ∘ g) h _).

Lemma to_ring_self `{Integers Z} (f : Z → Z) `{!SemiRing_Morphism f} x : f x = x.
Proof (to_ring_unique_alt f id _).

(* A ring morphism from integers to another ring is injective
   if there's an injection in the other direction: *)
Lemma to_ring_injective `{Integers Z} `{Ring R} (f: R → Z) (g: Z → R)
  `{!SemiRing_Morphism f} `{!SemiRing_Morphism g}
  : Injective g.
Proof.
split.
intros x y E.
change (id x = id y).
rewrite <-(to_ring_twice f g id x), <-(to_ring_twice f g id y).
apply ap,E.
Qed.

Instance integers_to_integers_injective `{Integers Z} `{Integers Z2}
  (f: Z → Z2) `{!SemiRing_Morphism f}
  : Injective f.
Proof (to_ring_injective (integers_to_ring Z2 Z) _).

Instance naturals_to_integers_injective `{Funext} `{Univalence}
  `{Integers Z} `{Naturals N}
  (f: N → Z) `{!SemiRing_Morphism f}
  : Injective f.
Proof.
split; try apply _. intros x y E.
apply (injective (cast N (NatPair.Z N))).
rewrite <-2!(naturals.to_semiring_twice (integers_to_ring Z (NatPair.Z N))
  f (cast N (NatPair.Z N))).
apply ap,E.
Qed.

Section retract_is_int.
  Context `{Funext} `{Univalence}.
  Context `{Integers Z} `{Ring Z2}.
  Context (f : Z → Z2) `{!Inverse f} `{!Surjective f} `{!SemiRing_Morphism f}
    `{!SemiRing_Morphism (f⁻¹)}.

  (* If we make this an instance, then instance resolution will often loop *)
  Definition retract_is_int_to_ring : IntegersToRing Z2 := λ Z2 _ _ _ _ _ _,
    integers_to_ring Z Z2 ∘ f⁻¹.

  Section for_another_ring.
    Context `{Ring R}.

    Instance: SemiRing_Morphism (integers_to_ring Z R ∘ f⁻¹) := {}.
    Context (h :  Z2 → R) `{!SemiRing_Morphism h}.

    Lemma same_morphism x : (integers_to_ring Z R ∘ f⁻¹) x = h x.
    Proof.
    transitivity ((h ∘ (f ∘ f⁻¹)) x).
    - symmetry. apply (to_ring_unique (h ∘ f)).
    - unfold compose. rewrite jections.surjective_applied;trivial.
    Qed.
  End for_another_ring.

  (* If we make this an instance, then instance resolution will often loop *)
  Lemma retract_is_int: Integers Z2 (U:=retract_is_int_to_ring).
  Proof.
  split;try apply _.
  - unfold integers_to_ring, retract_is_int_to_ring. apply _.
  - intros;apply same_morphism;apply _.
  Qed.
End retract_is_int.

Section int_to_int_iso.

Context `{Integers Z1} `{Integers Z2}.

Global Instance int_to_int_equiv : IsEquiv (integers_to_ring Z1 Z2).
Proof.
apply Equivalences.isequiv_adjointify with (integers_to_ring Z2 Z1);
red;apply (to_ring_involutive _ _).
Defined.

End int_to_int_iso.


Section contents.
Universe U.

Context `{Funext} `{Univalence}.
Context (Z : Type@{U}) `{Integers@{U U} Z}.

Lemma from_int_stmt  Z' `{Integers@{U U} Z'}
  : forall (P : Rings.Operations -> Type),
  P (Rings.BuildOperations Z') -> P (Rings.BuildOperations Z).
Proof.
apply Rings.iso_leibnitz with (integers_to_ring Z' Z);apply _.
Qed.

Global Instance int_dec : DecidablePaths Z | 10.
Proof.
apply decidablepaths_equiv with (NatPair.Z nat)
  (integers_to_ring (NatPair.Z nat) Z);apply _.
Qed.

Global Instance slow_int_abs `{Naturals N} : IntAbs Z N | 10.
Proof.
intros x.
destruct (int_abs_sig (NatPair.Z N) N (integers_to_ring Z (NatPair.Z N) x))
as [[n E]|[n E]];[left|right];exists n.
- apply (injective (integers_to_ring Z (NatPair.Z N))).
  rewrite <-E. apply (naturals.to_semiring_twice _ _ _).
- apply (injective (integers_to_ring Z (NatPair.Z N))).
  rewrite rings.preserves_negate, <-E.
  apply (naturals.to_semiring_twice _ _ _).
Qed.

Instance int_nontrivial : PropHolds ((1:Z) ≠0).
Proof.
intros E.
apply (rings.is_ne_0 (1:nat)).
apply (injective (naturals_to_semiring nat Z)).
exact E. (* because [naturals_to_semiring nat] plays nice with 1 *)
Qed.

Global Instance int_zero_product : ZeroProduct Z.
Proof.
intros x y E.
destruct (zero_product (integers_to_ring Z (NatPair.Z nat) x)
  (integers_to_ring Z (NatPair.Z nat) y)).
- rewrite <-(rings.preserves_mult (A:=Z)), E, (rings.preserves_0 (A:=Z)).
  trivial.
- left. apply (injective (integers_to_ring Z (NatPair.Z nat))).
  rewrite rings.preserves_0. trivial.
- right. apply (injective (integers_to_ring Z (NatPair.Z nat))).
  rewrite rings.preserves_0. trivial.
Qed.

Global Instance int_integral_domain : IntegralDomain Z := {}.

End contents.
