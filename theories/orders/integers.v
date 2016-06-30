Require Import HoTT.Types.Universe HoTT.Basics.Decidable.
Require
  HoTTClasses.theory.integers
  HoTTClasses.theory.int_abs.
Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.integers
  HoTTClasses.interfaces.naturals
  HoTTClasses.theory.additional_operations
  HoTTClasses.interfaces.orders
  HoTTClasses.implementations.natpair_integers
  HoTTClasses.orders.rings
  HoTTClasses.theory.rings.
Require Export
  HoTTClasses.orders.nat_int.

Section integers.
Context `{Funext} `{Univalence}.
Context `{Integers Z} `{Apart Z} `{!TrivialApart Z}
  `{!FullPseudoSemiRingOrder Zle Zlt}.

(* Add Ring Z : (rings.stdlib_ring_theory Z). *)
(* Add Ring nat : (rings.stdlib_semiring_theory nat). *)

Lemma induction
  (P: Z → Type):
  P 0 → (∀ n, 0 ≤ n → P n → P (1 + n)) → (∀ n, n ≤ 0 → P n → P (n - 1)) →
  ∀ n, P n.
Proof.
intros P0 Psuc1 Psuc2 n.
destruct (int_abs_sig Z nat n) as [[a A]|[a A]].
- rewrite <-A. clear A. revert a.
  apply naturals.induction.
  + rewrite rings.preserves_0. trivial.
  + intros m E.
    rewrite rings.preserves_plus, rings.preserves_1.
    apply Psuc1.
    * apply to_semiring_nonneg.
    * trivial.
- rewrite <-(groups.negate_involutive n), <-A.
  clear A. revert a. apply naturals.induction.
  + rewrite rings.preserves_0, rings.negate_0. trivial.
  + intros m E.
    rewrite rings.preserves_plus, rings.preserves_1.
    rewrite rings.negate_plus_distr, commutativity.
    apply Psuc2.
    * apply naturals.negate_to_ring_nonpos.
    * trivial.
Qed.

Lemma induction_nonneg
  (P: Z → Type):
  P 0 → (∀ n, 0 ≤ n → P n → P (1 + n)) → ∀ n, 0 ≤ n → P n.
Proof.
intros P0 PS. refine (induction _ _ _ _); auto.
intros n E1 ? E2.
destruct (rings.is_ne_0 1).
apply (antisymmetry (≤)).
- apply (order_reflecting ((n - 1) +)).
  rewrite <-plus_assoc,plus_negate_l,2!plus_0_r.
  transitivity 0;trivial.
- transitivity (n - 1);trivial.
  apply (order_reflecting (1 +)).
  rewrite plus_comm,<-plus_assoc,plus_negate_l,plus_0_r.
  transitivity 0. trivial.
  apply le_0_2.
Qed.

Global Instance: Biinduction Z.
Proof.
intros P P0 Psuc. apply induction; trivial.
- intros ??;apply Psuc.
- intros;apply Psuc.
  rewrite plus_comm,<-plus_assoc,plus_negate_l,plus_0_r.
  trivial.
Qed.

Global Instance slow_int_le_dec : ∀ x y: Z, Decision (x ≤ y) | 10.
Proof.
intros x y.
(* otherwise Z_le gets defined using peano.nat_ring
   but we only know order_reflecting when using naturals.nat_ring *)
pose (naturals_ring) as E0.
destruct (decide (integers_to_ring _ (NatPair.Z nat) x ≤
    integers_to_ring _ (NatPair.Z nat) y)) as [E|E].
- left. apply (order_reflecting _) in E. trivial.
- right. intro;apply E;apply (order_preserving _);trivial.
Qed.
End integers.

(* A default order on the integers *)
Instance int_le `{Integers Z} : Le Z | 10
  := λ x y, ∃ z, y = x + naturals_to_semiring nat Z z.
Instance int_lt  `{Integers Z} : Lt Z | 10 := dec_lt.

Section default_order.
Context `{Funext} `{Univalence}.
Context `{Integers Z} `{Apart Z} `{!TrivialApart Z}.
(* Add Ring Int2 : (rings.stdlib_ring_theory Int). *)

Global Instance : is_mere_relation Z int_le.
Proof.
intros;unfold int_le.
apply Sigma.ishprop_sigma_disjoint.
intros a b E1 E2.
pose proof (integers.naturals_to_integers_injective (naturals_to_semiring nat Z)).
rewrite E1 in E2.
apply (left_cancellation _ _) in E2.
apply (injective (naturals_to_semiring nat Z)) in E2.
destruct E2;split. (* <- path_lift *)
Qed.

Instance: PartialOrder int_le.
Proof.
repeat split.
- apply _.
- intros x;hnf.
  exists 0. rewrite preserves_0,plus_0_r;trivial.
- intros x y z [k E1] [k' E2].
  exists (k + k').
  rewrite E2,E1.
  rewrite (preserves_plus (f:=naturals_to_semiring nat Z)).
  Symmetry;apply associativity.
- intros x y [k E1] [k' E2].
  rewrite E1.
  assert (k = 0).
  + apply (naturals.zero_sum k k').
    apply (injective (naturals_to_semiring nat Z)).
    rewrite preserves_0,preserves_plus.
    apply (left_cancellation plus x).
    rewrite plus_assoc,plus_0_r.
    rewrite <-E1,<-E2. trivial.
  + rewrite X,preserves_0,plus_0_r;trivial.
Qed.

Instance: SemiRingOrder int_le.
Proof.
apply from_ring_order.
- intros z x y [a A]. exists a. rewrite A.
  apply associativity.
- intros x y [a A] [b B]. exists (a * b).
  rewrite A, B, (preserves_mult (f:=naturals_to_semiring nat Z)), !plus_0_l.
  trivial.
Qed.

Notation i_to_r := (integers_to_ring Z (NatPair.Z nat)).

Instance: TotalRelation int_le.
Proof.
(* same as for slow_int_le_dec *)
pose (naturals_ring) as E0.
assert (∀ x y, i_to_r x ≤ i_to_r y → x ≤ y) as P.
- intros x y E.
  destruct (decompose_le E) as [a [A B]].
  revert a A B.
  apply (NatPair.Z_ind _ (fun a => _ -> _ -> _)).
  intros [pa na] A B.
  exists (pa ∸ na).
  apply (injective i_to_r).
  rewrite rings.preserves_plus, B. clear B.
  apply ap.
  path_via (' (pa ∸ na)).
  + apply NatPair.Z_eq. red;simpl.
    rewrite plus_0_r,cut_minus_le;trivial.
    change (0 + na <= pa + 0) in A.
    rewrite plus_0_l,plus_0_r in A;trivial.
  + clear E A x y.
    change (' (pa ∸ na) ≡ (compose i_to_r (naturals_to_semiring nat Z)) (pa ∸ na)).
    generalize (pa ∸ na);intros n.
    apply naturals.to_semiring_unique_alt;apply _.
- intros x y.
  destruct (total (≤) (i_to_r x) (i_to_r y)); [left|right]; eapply P;trivial.
Qed.

Global Instance: FullPseudoSemiRingOrder int_le int_lt.
Proof.
apply dec_full_pseudo_srorder.
reflexivity.
Qed.
End default_order.
