Require
  HoTT.Classes.theory.int_abs.
Require Import
  HoTT.Classes.implementations.peano_naturals
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.naturals
  HoTT.Classes.interfaces.orders
  HoTT.Classes.implementations.natpair_integers
  HoTT.Classes.theory.rings
  HoTT.Classes.theory.integers.
Require Export
  HoTT.Classes.orders.nat_int.

Import NatPair.Instances.
Generalizable Variables N Z R f.

Section integers.
Context `{Funext} `{Univalence}.
Context `{Integers Z} `{!TrivialApart Z}.

(* Add Ring Z : (rings.stdlib_ring_theory Z). *)
(* Add Ring nat : (rings.stdlib_semiring_theory nat). *)

Lemma induction
  (P: Z -> Type):
  P 0 -> (forall n, 0 ≤ n -> P n -> P (1 + n)) -> (forall n, n ≤ 0 -> P n -> P (n - 1)) ->
  forall n, P n.
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
- rewrite <-(negate_involutive n), <-A.
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
  (P: Z -> Type):
  P 0 -> (forall n, 0 ≤ n -> P n -> P (1 + n)) -> forall n, 0 ≤ n -> P n.
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
  transitivity 0.
  + trivial.
  + apply le_0_2.
Qed.

Global Instance: Biinduction Z.
Proof.
intros P P0 Psuc. apply induction; trivial.
- intros ??;apply Psuc.
- intros;apply Psuc.
  rewrite plus_comm,<-plus_assoc,plus_negate_l,plus_0_r.
  trivial.
Qed.

Global Instance slow_int_le_dec : forall x y: Z, Decidable (x ≤ y) | 10.
Proof.
intros x y.
(* otherwise Z_le gets defined using peano.nat_ring
   but we only know order_reflecting when using naturals.nat_ring *)
pose (naturals_ring) as E0.
destruct (dec (integers_to_ring _ (NatPair.Z nat) x ≤
    integers_to_ring _ (NatPair.Z nat) y)) as [E|E].
- left. apply (order_reflecting _) in E. trivial.
- right. intro;apply E;apply (order_preserving _);trivial.
Qed.
End integers.
