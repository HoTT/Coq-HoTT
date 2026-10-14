Require Import
  HoTT.Types.Sigma
  HoTT.Spaces.Nat.Core.
Require Import
  HoTT.Classes.theory.naturals.
Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.orders
  HoTT.Classes.theory.rings
  HoTT.Classes.orders.rings
  HoTT.Classes.implementations.peano_naturals.
Require Export
  HoTT.Classes.orders.nat_int.

Generalizable Variables N R Rle Rlt f.

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

Lemma nat_not_neg x : ~(x < 0).
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

#[export] Instance orderreflecting_left_mult : forall (z : N), PropHolds (z <> 0) -> OrderReflecting (z *.).
Proof.
intros z ?. red. apply (order_reflecting_pos (.*.) z).
apply nat_ne_0_pos. trivial.
Qed.

#[export] Instance slow_nat_le_dec: forall x y: N, Decidable (x ≤ y) | 10.
Proof.
intros x y.
destruct (nat_le_dec (naturals_to_semiring _ nat x) (naturals_to_semiring _ nat y))
as [E | E].
- left.
  apply (order_reflecting (naturals_to_semiring N nat)). exact E.
- right. intros E'. apply E.
  apply order_preserving;trivial. exact _.
Qed.

Section another_ring.
  Context `{IsCRing R} `{Apart R} `{!FullPseudoSemiRingOrder (A:=R) Rle Rlt}
    `{!IsSemiRingPreserving (f : N -> R)}.

  Lemma negate_to_ring_nonpos n : -f n ≤ 0.
  Proof. apply flip_nonneg_negate. apply to_semiring_nonneg. Qed.

  Lemma between_to_ring n : -f n ≤ f n.
  Proof. apply between_nonneg. apply to_semiring_nonneg. Qed.
End another_ring.
End naturals_order.

#[export]
Hint Extern 20 (PropHolds (_ ≤ _)) => eapply @nat_nonneg : typeclass_instances.

(** ** The map from [nat] into an ordered semiring *)

(** Unlike [to_semiring_nonneg], the following facts about [naturals_to_semiring nat] do not need univalence. *)
Section nat_to_semiring.
  Context `{FullPseudoSemiRingOrder R} `{!IsSemiCRing R}.

  Local Notation nR := (naturals_to_semiring nat R).

  Lemma nat_to_semiring_succ (n : nat) : nR (S n) = 1 + nR n.
  Proof.
    exact (preserves_plus (f:=nR) 1%nat n).
  Qed.

  Lemma nat_to_semiring_nonneg (n : nat) : 0 ≤ nR n.
  Proof.
    induction n as [|n IH].
    - reflexivity.
    - rewrite nat_to_semiring_succ; exact (nonneg_plus_compat _ _ le_0_1 IH).
  Qed.

  Lemma nat_to_semiring_le (m n : nat) : (m <= n)%nat -> nR m ≤ nR n.
  Proof.
    intro lemn; induction lemn as [|n lemn IH].
    - reflexivity.
    - refine (transitivity IH _).
      rewrite nat_to_semiring_succ.
      exact (fst (nonneg_plus_le_compat_l _ _) le_0_1).
  Qed.

  Context `{!PropHolds ((1 : R) ≶ 0)}.

  Lemma nat_to_semiring_succ_pos (n : nat) : 0 < nR (S n).
  Proof.
    rewrite nat_to_semiring_succ.
    exact (pos_plus_le_lt_compat_l _ _ _ lt_0_1 (nat_to_semiring_nonneg n)).
  Qed.

  Lemma nat_to_semiring_pos (n : nat) : (0 < n)%nat -> 0 < nR n.
  Proof.
    destruct n as [|n]; intro lt.
    - destruct (not_lt_zero_r _ lt).
    - apply nat_to_semiring_succ_pos.
  Qed.
End nat_to_semiring.
