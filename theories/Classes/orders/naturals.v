Require Import
  HoTT.Types.Universe
  HoTT.Types.Sigma.
Require
  HoTT.Classes.theory.naturals.
Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.naturals
  HoTT.Classes.interfaces.orders
  HoTT.Classes.theory.rings
  HoTT.Classes.orders.rings
  HoTT.Classes.implementations.peano_naturals
  HoTT.Classes.tactics.ring_tac.
Require Export
  HoTT.Classes.orders.nat_int.

Section naturals_order.
Context `{Funext} `{Univalence}.
Context `{Naturals N} `{!TrivialApart N}.

Instance nat_nonneg x : PropHolds (0 ≤ x).
Proof. apply (to_semiring_nonneg (f:=id)). Qed.

Lemma nat_le_plus {x y: N}: x ≤ y <-> exists z, y = x + z.
Proof.
split; intros E.
- destruct (decompose_le E) as [z [Ez1 Ez2]]. exists z. trivial.
- destruct E as [z Ez].
  apply compose_le with z; [solve_propholds | trivial].
Qed.

Lemma nat_not_neg x : ~x < 0.
Proof. apply le_not_lt_flip, nat_nonneg. Qed.

Lemma nat_0_or_pos x : x = 0 |_| 0 < x.
Proof.
destruct (trichotomy (<) 0 x) as [?|[?|?]]; auto.
- left;symmetry;trivial.
- destruct (nat_not_neg x). trivial.
Qed.

Lemma nat_0_or_ge_1 x : x = 0 |_| 1 ≤ x.
Proof.
destruct (nat_0_or_pos x);auto.
right;apply pos_ge_1. trivial.
Qed.

Lemma nat_ne_0_pos x : x <> 0 <-> 0 < x.
Proof.
split.
- destruct (nat_0_or_pos x); auto.
  intros E;destruct E;trivial.
- intros E1 E2. rewrite E2 in E1. destruct (irreflexivity (<) 0). trivial.
Qed.

Lemma nat_ne_0_ge_1 x : x <> 0 <-> 1 ≤ x.
Proof.
etransitivity.
- apply nat_ne_0_pos.
- apply pos_ge_1.
Qed.

Global Instance: forall (z : N), PropHolds (z <> 0) -> OrderReflecting (z *.).
Proof.
intros z ?. red. apply (order_reflecting_pos (.*.) z).
apply nat_ne_0_pos. trivial.
Qed.

Global Instance slow_nat_le_dec: forall x y: N, Decidable (x ≤ y) | 10.
Proof.
intros x y.
destruct (nat_le_dec (naturals_to_semiring _ nat x) (naturals_to_semiring _ nat y))
as [E | E].
- left.
  apply (order_reflecting (naturals_to_semiring N nat)). exact E.
- right. intros E'. apply E.
  apply order_preserving;trivial. apply _.
Qed.

Section another_ring.
  Context `{Ring R} `{Apart R} `{!FullPseudoSemiRingOrder (A:=R) Rle Rlt}
    `{!SemiRingPreserving (f : N -> R)}.

  Lemma negate_to_ring_nonpos n : -f n ≤ 0.
  Proof. apply flip_nonneg_negate. apply to_semiring_nonneg. Qed.

  Lemma between_to_ring n : -f n ≤ f n.
  Proof. apply between_nonneg. apply to_semiring_nonneg. Qed.
End another_ring.
End naturals_order.

Hint Extern 20 (PropHolds (_ ≤ _)) => eapply @nat_nonneg : typeclass_instances.
