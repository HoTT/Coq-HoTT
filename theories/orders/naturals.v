Require Import
  HoTT.Types.Universe
  HoTT.Types.Sigma.
Require
  HoTTClasses.theory.naturals.
Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.naturals
  HoTTClasses.interfaces.orders
  HoTTClasses.theory.rings
  HoTTClasses.orders.rings
  HoTTClasses.implementations.peano_naturals
  HoTTClasses.tactics.ring_tac.
Require Export
  HoTTClasses.orders.nat_int.

Section naturals_order.
Context `{Funext} `{Univalence}.
Context `{Naturals N} `{Apart N} `{!TrivialApart N}
  `{!FullPseudoSemiRingOrder Nle Nlt}.

Instance nat_nonneg x : PropHolds (0 ≤ x).
Proof. apply (to_semiring_nonneg (f:=id)). Qed.

Lemma nat_le_plus {x y: N}: x ≤ y ↔ ∃ z, y = x + z.
Proof.
split; intros E.
- destruct (decompose_le E) as [z [Ez1 Ez2]]. exists z. trivial.
- destruct E as [z Ez].
  apply compose_le with z; [solve_propholds | trivial].
Qed.

Lemma nat_not_neg x : ¬x < 0.
Proof. apply le_not_lt_flip, nat_nonneg. Qed.

Lemma nat_0_or_pos x : x = 0 ∨ 0 < x.
Proof.
destruct (trichotomy (<) 0 x) as [?|[?|?]]; auto.
- left;symmetry;trivial.
- destruct (nat_not_neg x). trivial.
Qed.

Lemma nat_0_or_ge_1 x : x = 0 ∨ 1 ≤ x.
Proof.
destruct (nat_0_or_pos x);auto.
right;apply pos_ge_1. trivial.
Qed.

Lemma nat_ne_0_pos x : x ≠ 0 ↔ 0 < x.
Proof.
split.
- destruct (nat_0_or_pos x); auto.
  intros E;destruct E;trivial.
- intros E1 E2. rewrite E2 in E1. destruct (irreflexivity (<) 0). trivial.
Qed.

Lemma nat_ne_0_ge_1 x : x ≠ 0 ↔ 1 ≤ x.
Proof.
etransitivity.
- apply nat_ne_0_pos.
- apply pos_ge_1.
Qed.

Global Instance: ∀ (z : N), PropHolds (z ≠ 0) → OrderReflecting (z *.).
Proof.
intros z ?. red. apply (order_reflecting_pos (.*.) z).
apply nat_ne_0_pos. trivial.
Qed.

Global Instance slow_nat_le_dec: ∀ x y: N, Decision (x ≤ y) | 10.
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
    `{!SemiRingPreserving (f : N → R)}.

  Lemma negate_to_ring_nonpos n : -f n ≤ 0.
  Proof. apply flip_nonneg_negate. apply to_semiring_nonneg. Qed.

  Lemma between_to_ring n : -f n ≤ f n.
  Proof. apply between_nonneg. apply to_semiring_nonneg. Qed.
End another_ring.
End naturals_order.

Hint Extern 20 (PropHolds (_ ≤ _)) => eapply @nat_nonneg : typeclass_instances.

(* A default order on the naturals *)
Instance nat_le `{Naturals N} : Le N | 10 :=  λ x y, ∃ z, x + z = y.
Instance nat_lt `{Naturals N} : Lt N | 10 := dec_lt.

Section default_order.
Context `{Funext} `{Univalence} `{Naturals N} `{Apart N} `{!TrivialApart N}.
(* Add Ring N2 : (rings.stdlib_semiring_theory N). *)

Global Instance : is_mere_relation N nat_le.
Proof.
unfold nat_le.
intros a b.
apply ishprop_sigma_disjoint.
intros x y E1 E2.
apply (left_cancellation plus a).
path_via b.
Qed.

Instance: PartialOrder nat_le.
Proof.
repeat split.
- apply _.
- exists 0. apply rings.plus_0_r.
- hnf. intros a b c [d Ed] [e Ee].
  rewrite <-Ee, <-Ed.
  exists (d+e).
  ring_with_nat.
- hnf. intros a b [c Ec] [d Ed].
  rewrite <-(rings.plus_0_r a),<-Ec,<-rings.plus_assoc in Ed.
  apply (left_cancellation _ _) in Ed.
  apply naturals.zero_sum in Ed.
  destruct Ed as [E1 _];rewrite E1,rings.plus_0_r in Ec;trivial.
Qed.

Instance: SemiRingOrder nat_le.
Proof.
repeat (split; try apply _).
- intros a b [c E];exists c. apply symmetry;trivial.
- intros a b [c E];exists c.
  rewrite <-E;ring_with_nat.
- intros a b [c E];exists c.
  rewrite <-plus_assoc in E. apply (left_cancellation _ _) in E.
  trivial.
- intros a b _ _.
  exists (a*b). apply plus_0_l.
Qed.

Notation n_to_sr := (naturals_to_semiring N nat).

Instance: TotalRelation nat_le.
Proof.
assert (∀ x y, n_to_sr x ≤ n_to_sr y → x ≤ y) as P.
- intros x y E.
  destruct (decompose_le E) as [a [_ A]].
  exists (naturals_to_semiring nat N a).
  apply (injective n_to_sr).
  rewrite rings.preserves_plus. rewrite (naturals.to_semiring_involutive _ _).
  symmetry;trivial.
- intros x y.
  destruct (total (≤) (n_to_sr x) (n_to_sr y)); [left | right]; apply P;trivial.
Qed.

Global Instance: FullPseudoSemiRingOrder nat_le nat_lt.
Proof.
apply dec_full_pseudo_srorder.
reflexivity.
Qed.
End default_order.
