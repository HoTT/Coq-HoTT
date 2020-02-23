Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.orders
  HoTT.Classes.theory.groups
  HoTT.Classes.theory.rings.
Require Export
  HoTT.Classes.orders.semirings.

Generalizable Variables R Rle Rlt R1le R1lt.

Section from_ring_order.
  Context `{IsRing R} `{!PartialOrder Rle}
    (plus_spec : forall z, OrderPreserving (z +))
    (mult_spec : forall x y, PropHolds (0 ≤ x) -> PropHolds (0 ≤ y) ->
      PropHolds (0 ≤ x * y)).

  Lemma from_ring_order: SemiRingOrder (≤).
  Proof.
  repeat (split; try apply _).
  - intros x y E. exists (- x + y).
    rewrite simple_associativity, plus_negate_r, plus_0_l.
    reflexivity.
  - intros x y E.
    rewrite <-(plus_0_l x), <-(plus_0_l y), <-!(plus_negate_l z),
      <-!simple_associativity.
    apply (order_preserving _). trivial.
  Qed.
End from_ring_order.

Section from_strict_ring_order.
  Context `{IsRing R} `{!StrictOrder Rlt}
    (plus_spec : forall z, StrictlyOrderPreserving (z +))
    (mult_spec : forall x y, PropHolds (0 < x) -> PropHolds (0 < y) ->
      PropHolds (0 < x * y)).

  Lemma from_strict_ring_order: StrictSemiRingOrder (<).
  Proof.
  repeat (split; try apply _).
  - intros x y E. exists (- x + y).
    rewrite simple_associativity, plus_negate_r, plus_0_l.
    reflexivity.
  - intros x y E.
    rewrite <-(plus_0_l x), <-(plus_0_l y), <-!(plus_negate_l z),
      <-!simple_associativity.
    apply (strictly_order_preserving _). trivial.
  Qed.
End from_strict_ring_order.

Section from_pseudo_ring_order.
  Context `{IsRing R} `{Apart R} `{!PseudoOrder Rlt}
    (plus_spec : forall z, StrictlyOrderPreserving (z +))
    (mult_ext : StrongBinaryExtensionality (.*.))
    (mult_spec : forall x y, PropHolds (0 < x) -> PropHolds (0 < y) ->
      PropHolds (0 < x * y)).

  Lemma from_pseudo_ring_order: PseudoSemiRingOrder (<).
  Proof.
  repeat (split; try apply _).
  - intros x y E. exists (- x + y).
    rewrite simple_associativity, plus_negate_r, plus_0_l.
    reflexivity.
  - intros x y E.
    rewrite <-(plus_0_l x), <-(plus_0_l y), <-!(plus_negate_l z),
      <-!simple_associativity.
    apply (strictly_order_preserving _).
    trivial.
  Qed.
End from_pseudo_ring_order.

Section from_full_pseudo_ring_order.
  Context `{IsRing R} `{Apart R} `{!FullPseudoOrder Rle Rlt}
    (plus_spec : forall z, StrictlyOrderPreserving (z +))
    (mult_ext : StrongBinaryExtensionality (.*.))
    (mult_spec : forall x y, PropHolds (0 < x) -> PropHolds (0 < y) ->
      PropHolds (0 < x * y)).

  Lemma from_full_pseudo_ring_order: FullPseudoSemiRingOrder (≤) (<).
  Proof.
  split.
  - apply _.
  - apply from_pseudo_ring_order;trivial.
  - apply le_iff_not_lt_flip;trivial.
  Qed.
End from_full_pseudo_ring_order.

Section ring_order.
  Context `{IsRing R} `{!SemiRingOrder Rle}.
(*   Add Ring R : (stdlib_ring_theory R). *)

  Lemma flip_le_negate x y : -y ≤ -x <-> x ≤ y.
  Proof.
  assert (forall a b, a ≤ b -> -b ≤ -a).
  - intros a b E.
    transitivity (-a + -b + a);[apply eq_le|
    transitivity (-a + -b + b);[|apply eq_le]].
    + rewrite plus_comm, plus_assoc, plus_negate_r, plus_0_l.
      reflexivity.
    + apply (order_preserving _). trivial.
    + rewrite <-plus_assoc, plus_negate_l. apply plus_0_r.
  - split; intros; auto.
    rewrite <-(negate_involutive x), <-(negate_involutive y); auto.
  Qed.

  Lemma flip_nonneg_negate x : 0 ≤ x <-> -x ≤ 0.
  Proof.
  split; intros E.
  - rewrite <-negate_0. apply flip_le_negate.
    rewrite !involutive. trivial.
  - apply flip_le_negate. rewrite negate_0. trivial.
  Qed.

  Lemma flip_nonpos_negate x : x ≤ 0 <-> 0 ≤ -x.
  Proof.
  pattern x at 1;apply (transport _ (negate_involutive x)).
  split; intros; apply flip_nonneg_negate;trivial.
  Qed.

  Lemma flip_le_minus_r (x y z : R) : z ≤ y - x <-> z + x ≤ y.
  Proof.
  split; intros E.
  - rewrite plus_comm.
    rewrite (plus_conjugate_alt y x).
    apply (order_preserving _). trivial.
  - rewrite plus_comm.
    rewrite (plus_conjugate_alt z (- x)), involutive.
    apply (order_preserving _). trivial.
  Qed.

  Lemma flip_le_minus_l (x y z : R) : y - x ≤ z <-> y ≤ z + x.
  Proof.
  pattern x at 2;apply (transport _ (negate_involutive x)).
  split; apply flip_le_minus_r.
  Qed.

  Lemma flip_nonneg_minus (x y : R) : 0 ≤ y - x <-> x ≤ y.
  Proof.
  pattern x at 2;apply (transport _ (plus_0_l x)).
  apply flip_le_minus_r.
  Qed.

  Lemma flip_nonpos_minus (x y : R) : y - x ≤ 0 <-> y ≤ x.
  Proof.
  pattern x at 2;apply (transport _ (plus_0_l x)).
  apply flip_le_minus_l.
  Qed.

  Lemma nonneg_minus_compat (x y z : R) : 0 ≤ z -> x ≤ y -> x - z ≤ y.
  Proof.
  intros E1 E2.
  rewrite plus_comm, (plus_conjugate_alt y (- z)), involutive.
  apply (order_preserving (-(z) +)).
  transitivity y; trivial.
  pattern y at 1;apply (transport _ (plus_0_r y)).
  apply (order_preserving (y +)). trivial.
  Qed.

  Lemma nonneg_minus_compat_back (x y z : R) : 0 ≤ z -> x ≤ y - z -> x ≤ y.
  Proof.
  intros E1 E2.
  transitivity (y - z); trivial.
  apply nonneg_minus_compat;trivial. apply reflexivity.
  Qed.

  Lemma between_nonneg (x : R) : 0 ≤ x -> -x ≤ x.
  Proof.
  intros.
  transitivity 0; trivial.
  apply flip_nonneg_negate. trivial.
  Qed.
End ring_order.

Section strict_ring_order.
  Context `{IsRing R} `{!StrictSemiRingOrder Rlt}.
(*   Add Ring Rs : (stdlib_ring_theory R). *)

  Lemma flip_lt_negate x y : -y < -x <-> x < y.
  Proof.
  assert (forall a b, a < b -> -b < -a).
  - intros a b E.
    rewrite (plus_conjugate (-b) (-a)), involutive.
    apply lt_eq_trans with (-a + -b + b).
    + apply (strictly_order_preserving _). trivial.
    + rewrite <-plus_assoc,plus_negate_l, plus_0_r. reflexivity.
  - split; intros; auto.
    rewrite <-(negate_involutive x), <-(negate_involutive y); auto.
  Qed.

  Lemma flip_pos_negate x : 0 < x <-> -x < 0.
  Proof.
  split; intros E.
  - rewrite <- negate_0. apply flip_lt_negate. rewrite !involutive;trivial.
  - apply flip_lt_negate. rewrite negate_0. trivial.
  Qed.

  Lemma flip_neg_negate x : x < 0 <-> 0 < -x.
  Proof.
  pattern x at 1;apply (transport _ (negate_involutive x)).
  split; intros; apply flip_pos_negate;trivial.
  Qed.

  Lemma flip_lt_minus_r (x y z : R) : z < y - x <-> z + x < y.
  Proof.
  split; intros E.
  - rewrite plus_comm, (plus_conjugate_alt y x).
    apply (strictly_order_preserving _). trivial.
  - rewrite plus_comm, (plus_conjugate_alt z (-x)), involutive.
    apply (strictly_order_preserving _). trivial.
  Qed.

  Lemma flip_lt_minus_l (x y z : R) : y - x < z <-> y < z + x.
  Proof.
  pattern x at 2;apply (transport _ (negate_involutive x)).
  split; apply flip_lt_minus_r.
  Qed.

  Lemma flip_pos_minus (x y : R) : 0 < y - x <-> x < y.
  Proof.
  pattern x at 2;apply (transport _ (plus_0_l x)).
  apply flip_lt_minus_r.
  Qed.

  Lemma flip_neg_minus (x y : R) : y - x < 0 <-> y < x.
  Proof.
  pattern x at 2;apply (transport _ (plus_0_l x)).
  apply flip_lt_minus_l.
  Qed.

  Lemma pos_minus_compat (x y z : R) : 0 < z -> x < y -> x - z < y.
  Proof.
  intros E1 E2.
  rewrite plus_comm, (plus_conjugate_alt y (-z)), involutive.
  apply (strictly_order_preserving (-(z) +)).
  transitivity y; trivial.
  pattern y at 1;apply (transport _ (plus_0_r y)).
  apply (strictly_order_preserving (y +)).
  trivial.
  Qed.

  Lemma pos_minus_lt_compat_r x z : 0 < z <-> x - z < x.
  Proof.
    pattern x at 2;apply (transport _ (plus_0_r x)).
    split; intros.
    - apply (strictly_order_preserving _), flip_pos_negate; assumption.
    - apply flip_pos_negate, (strictly_order_reflecting (x+)); assumption.
  Qed.

  Lemma pos_minus_lt_compat_l x z : 0 < z <-> - z + x < x.
  Proof.
    split; intros ltz.
    - rewrite (commutativity (-z) x); apply pos_minus_lt_compat_r; assumption.
    - rewrite (commutativity (-z) x) in ltz.
      apply (snd (pos_minus_lt_compat_r x z)); assumption.
  Qed.

  Lemma between_pos (x : R) : 0 < x -> -x < x.
  Proof.
  intros E.
  transitivity 0; trivial.
  apply flip_pos_negate. trivial.
  Qed.

End strict_ring_order.

Section strict_ring_apart.
  Context `{FullPseudoSemiRingOrder R}.

  Definition positive_apart_zero (z : R) (Pz : 0 < z) : z ≶ 0
    := pseudo_order_lt_apart_flip 0 z Pz.
  Definition negative_apart_zero (z : R) (Nz : z < 0) : z ≶ 0
    := pseudo_order_lt_apart z 0 Nz.

End strict_ring_apart.

Section another_ring_order.
  Context `{IsRing R1} `{!SemiRingOrder R1le} `{IsRing R2} `{R2le : Le R2}
    `{is_mere_relation R2 R2le}.

  Lemma projected_ring_order (f : R2 -> R1) `{!IsSemiRingPreserving f} `{!IsInjective f}
    : (forall x y, x ≤ y <-> f x ≤ f y) -> SemiRingOrder R2le.
  Proof.
  intros P. apply (projected_srorder f P).
  intros x y E. exists (-x + y).
  rewrite plus_assoc, plus_negate_r, plus_0_l. reflexivity.
  Qed.

  Context `{!SemiRingOrder R2le} {f : R1 -> R2} `{!IsSemiRingPreserving f}.

  Lemma reflecting_preserves_nonneg : (forall x, 0 ≤ f x -> 0 ≤ x) -> OrderReflecting f.
  Proof.
  intros E. repeat (split; try apply _). intros x y F.
  apply flip_nonneg_minus, E.
  rewrite preserves_plus, preserves_negate.
  apply (flip_nonneg_minus (f x)), F.
  Qed.

  Lemma preserves_ge_negate1 `{!OrderPreserving f} x : - 1 ≤ x -> - 1 ≤ f x.
  Proof.
  intros. rewrite <-(preserves_1 (f:=f)), <-preserves_negate.
  apply (order_preserving f). trivial.
  Qed.

  Lemma preserves_le_negate1 `{!OrderPreserving f} x : x ≤ - 1 -> f x ≤ - 1.
  Proof.
  intros. rewrite <-(preserves_1 (f:=f)), <-preserves_negate.
  apply (order_preserving f). trivial.
  Qed.
End another_ring_order.

Section another_strict_ring_order.
  Context `{IsRing R1} `{!StrictSemiRingOrder R1lt} `{IsRing R2} `{R2lt : Lt R2}
    `{is_mere_relation R2 lt}.

  Lemma projected_strict_ring_order (f : R2 -> R1) `{!IsSemiRingPreserving f} :
    (forall x y, x < y <-> f x < f y) -> StrictSemiRingOrder R2lt.
  Proof.
  intros P. pose proof (projected_strict_order f P).
  apply from_strict_ring_order.
  - intros z x y E.
    apply P. rewrite 2!(preserves_plus (f:=f)).
    apply (strictly_order_preserving _), P. trivial.
  - intros x y E1 E2.
    apply P. rewrite preserves_mult, preserves_0.
    apply pos_mult_compat; rewrite <-(preserves_0 (f:=f)); apply P; trivial.
  Qed.
End another_strict_ring_order.

Section another_pseudo_ring_order.
  Context `{IsRing R1} `{Apart R1} `{!PseudoSemiRingOrder R1lt}
    `{IsRing R2} `{IsApart R2} `{R2lt : Lt R2}
    `{is_mere_relation R2 lt}.

  Lemma projected_pseudo_ring_order (f : R2 -> R1) `{!IsSemiRingPreserving f}
    `{!IsStrongInjective f}
    : (forall x y, x < y <-> f x < f y) -> PseudoSemiRingOrder R2lt.
  Proof.
  intros P.
  pose proof (projected_pseudo_order f P).
  pose proof (projected_strict_ring_order f P).
  apply from_pseudo_ring_order; try apply _.
  pose proof (pseudo_order_apart : IsApart R1).
  pose proof (pseudo_order_apart : IsApart R2).
  pose proof (strong_injective_mor f).
  repeat (split; try apply _).
  intros x₁ y₁ x₂ y₂ E.
  apply (strong_injective f) in E. rewrite 2!(preserves_mult (f:=f)) in E.
  apply (merely_destruct (strong_binary_extensionality (.*.) _ _ _ _ E));
  intros [?|?];apply tr; [left | right];
  apply (strong_extensionality f); trivial.
  Qed.
End another_pseudo_ring_order.

Section another_full_pseudo_ring_order.
  Context `{IsRing R1} `{Apart R1} `{!FullPseudoSemiRingOrder R1le R1lt}
    `{IsRing R2} `{IsApart R2} `{R2le : Le R2} `{R2lt : Lt R2}
    `{is_mere_relation R2 le} `{is_mere_relation R2 lt}.

  Lemma projected_full_pseudo_ring_order (f : R2 -> R1) `{!IsSemiRingPreserving f}
    `{!IsStrongInjective f}
    : (forall x y, x ≤ y <-> f x ≤ f y) -> (forall x y, x < y <-> f x < f y) ->
    FullPseudoSemiRingOrder R2le R2lt.
  Proof.
  intros P1 P2. pose proof (projected_full_pseudo_order f P1 P2).
  pose proof (projected_pseudo_ring_order f P2).
  split; try apply _. apply le_iff_not_lt_flip.
  Qed.
End another_full_pseudo_ring_order.
