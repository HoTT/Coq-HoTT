(* General results about arbitrary integer implementations. *)
Require Import
  HoTT.Basics.Decidable.
Require Import
 HoTT.Classes.theory.nat_distance
 HoTT.Classes.implementations.peano_naturals
 HoTT.Classes.interfaces.naturals
 HoTT.Classes.interfaces.orders
 HoTT.Classes.implementations.natpair_integers
 HoTT.Classes.theory.rings
 HoTT.Classes.isomorphisms.rings.
Require Export
 HoTT.Classes.interfaces.integers.

Import NatPair.Instances.
Generalizable Variables N Z R f.

Lemma to_ring_unique `{Integers Z} `{IsCRing R} (f: Z -> R)
  {h: IsSemiRingPreserving f} x
  : f x = integers_to_ring Z R x.
Proof.
symmetry. apply integers_initial.
Qed.

Lemma to_ring_unique_alt `{Integers Z} `{IsCRing R} (f g: Z -> R)
  `{!IsSemiRingPreserving f} `{!IsSemiRingPreserving g} x :
  f x = g x.
Proof.
rewrite (to_ring_unique f), (to_ring_unique g);reflexivity.
Qed.

Lemma to_ring_involutive Z `{Integers Z} Z2 `{Integers Z2} x :
  integers_to_ring Z2 Z (integers_to_ring Z Z2 x) = x.
Proof.
change (Compose (integers_to_ring Z2 Z) (integers_to_ring Z Z2) x = id x).
apply to_ring_unique_alt;apply _.
Qed.

Lemma morphisms_involutive `{Integers Z} `{IsCRing R} (f: R -> Z) (g: Z -> R)
  `{!IsSemiRingPreserving f} `{!IsSemiRingPreserving g} x : f (g x) = x.
Proof. exact (to_ring_unique_alt (f ∘ g) id _). Qed.

Lemma to_ring_twice `{Integers Z} `{IsCRing R1} `{IsCRing R2}
  (f : R1 -> R2) (g : Z -> R1) (h : Z -> R2)
  `{!IsSemiRingPreserving f} `{!IsSemiRingPreserving g} `{!IsSemiRingPreserving h} x
  : f (g x) = h x.
Proof. exact (to_ring_unique_alt (f ∘ g) h _). Qed.

Lemma to_ring_self `{Integers Z} (f : Z -> Z) `{!IsSemiRingPreserving f} x : f x = x.
Proof. exact (to_ring_unique_alt f id _). Qed.

(* A ring morphism from integers to another ring is injective
   if there's an injection in the other direction: *)
Lemma to_ring_injective `{Integers Z} `{IsCRing R} (f: R -> Z) (g: Z -> R)
  `{!IsSemiRingPreserving f} `{!IsSemiRingPreserving g}
  : IsInjective g.
Proof.
intros x y E.
change (id x = id y).
rewrite <-(to_ring_twice f g id x), <-(to_ring_twice f g id y).
apply ap,E.
Qed.

Global Instance integers_to_integers_injective `{Integers Z} `{Integers Z2}
  (f: Z -> Z2) `{!IsSemiRingPreserving f}
  : IsInjective f.
Proof. exact (to_ring_injective (integers_to_ring Z2 Z) _). Qed.

Global Instance naturals_to_integers_injective `{Funext} `{Univalence}
  `{Integers@{i i i i i i i i} Z} `{Naturals@{i i i i i i i i} N}
  (f: N -> Z) `{!IsSemiRingPreserving f}
  : IsInjective f.
Proof.
intros x y E.
apply (injective (cast N (NatPair.Z N))).
rewrite <-2!(naturals.to_semiring_twice (integers_to_ring Z (NatPair.Z N))
  f (cast N (NatPair.Z N))).
apply ap,E.
Qed.

Section retract_is_int.
  Context `{Funext}.
  Context `{Integers Z} `{IsCRing Z2}
    {Z2ap : Apart Z2} {Z2le Z2lt} `{!FullPseudoSemiRingOrder (A:=Z2) Z2le Z2lt}.
  Context (f : Z -> Z2) `{!IsEquiv f} `{!IsSemiRingPreserving f}
    `{!IsSemiRingPreserving (f^-1)}.

  (* If we make this an instance, then instance resolution will often loop *)
  Definition retract_is_int_to_ring : IntegersToRing Z2 := fun Z2 _ _ _ _ _ _ =>
    integers_to_ring Z Z2 ∘ f^-1.

  Section for_another_ring.
    Context `{IsCRing R}.

    Instance: IsSemiRingPreserving (integers_to_ring Z R ∘ f^-1) := {}.
    Context (h :  Z2 -> R) `{!IsSemiRingPreserving h}.

    Lemma same_morphism x : (integers_to_ring Z R ∘ f^-1) x = h x.
    Proof.
    transitivity ((h ∘ (f ∘ f^-1)) x).
    - symmetry. apply (to_ring_unique (h ∘ f)).
    - unfold Compose. apply ap.
      apply eisretr.
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
Context (Z : Type@{U}) `{Integers@{U U U U U U U U} Z}.

Lemma from_int_stmt  (Z':Type@{U}) `{Integers@{U U U U U U U U} Z'}
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
  rewrite preserves_negate, <-E.
  apply (naturals.to_semiring_twice _ _ _).
Qed.

Instance int_nontrivial : PropHolds ((1:Z) <>0).
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

Global Instance int_integral_domain : IsIntegralDomain Z := {}.

End contents.
