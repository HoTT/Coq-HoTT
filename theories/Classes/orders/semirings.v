Require Import HoTT.Basics.Decidable.
Require Import
  HoTT.Classes.theory.apartness
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.orders
  HoTT.Classes.theory.rings.
Require Export
  HoTT.Classes.orders.orders
  HoTT.Classes.orders.maps.

Generalizable Variables R Rlt f.

Section semiring_order.
  Context `{SemiRingOrder R} `{!IsSemiRing R}.
(*   Add Ring R : (stdlib_semiring_theory R). *)

  Global Instance plus_le_embed_l : forall (z : R), OrderEmbedding (+z).
  Proof.
  intro. split.
  - apply order_preserving_flip.
  - apply order_reflecting_flip.
  Qed.

  Global Instance plus_ordered_cancel_l : forall z, LeftCancellation (+) z.
  Proof.
  intros z x y E.
  apply (antisymmetry (≤)); apply (order_reflecting (z+)); apply eq_le;trivial.
  apply symmetry;trivial.
  Qed.

  Global Instance plus_ordered_cancel_r : forall z, RightCancellation (+) z.
  Proof.
  intros. apply (right_cancel_from_left (+)).
  Qed.

  Lemma nonneg_plus_le_compat_r x z : 0 ≤ z <-> x ≤ x + z.
  Proof.
  pattern x at 1. apply (transport _ (plus_0_r x)).
  split; intros.
  - apply (order_preserving _). trivial.
  - apply (order_reflecting (x+)). trivial.
  Qed.

  Lemma nonneg_plus_le_compat_l x z : 0 ≤ z <-> x ≤ z + x.
  Proof.
  rewrite (commutativity (f:=plus)).
  apply nonneg_plus_le_compat_r.
  Qed.

  Lemma plus_le_compat x₁ y₁ x₂ y₂ : x₁ ≤ y₁ -> x₂ ≤ y₂ -> x₁ + x₂ ≤ y₁ + y₂.
  Proof.
  intros E1 E2.
  transitivity (y₁ + x₂).
  - apply (order_preserving (+ x₂));trivial.
  - apply (order_preserving (y₁ +));trivial.
  Qed.

  Lemma plus_le_compat_r x y z : 0 ≤ z -> x ≤ y -> x ≤ y + z.
  Proof.
  intros. rewrite <-(plus_0_r x).
  apply plus_le_compat;trivial.
  Qed.

  Lemma plus_le_compat_l x y z : 0 ≤ z -> x ≤ y -> x ≤ z + y.
  Proof.
  rewrite (commutativity (f:=plus)).
  apply plus_le_compat_r.
  Qed.

  Lemma nonpos_plus_compat x y : x ≤ 0 -> y ≤ 0 -> x + y ≤ 0.
  Proof.
  intros. rewrite <-(plus_0_r 0).
  apply plus_le_compat;trivial.
  Qed.

  Instance nonneg_plus_compat (x y : R)
    : PropHolds (0 ≤ x) -> PropHolds (0 ≤ y) -> PropHolds (0 ≤ x + y).
  Proof.
  intros.
  apply plus_le_compat_l;trivial.
  Qed.

  Lemma decompose_le {x y} : x ≤ y -> exists z, 0 ≤ z /\ y = x + z.
  Proof.
  intros E.
  destruct (srorder_partial_minus x y E) as [z Ez].
  exists z. split; [| trivial].
  apply (order_reflecting (x+)).
  rewrite plus_0_r, <-Ez.
  trivial.
  Qed.

  Lemma compose_le x y z : 0 ≤ z -> y = x + z -> x ≤ y.
  Proof.
  intros E1 E2.
  rewrite E2.
  apply nonneg_plus_le_compat_r.
  trivial.
  Qed.

  Global Instance nonneg_mult_le_l : forall (z : R), PropHolds (0 ≤ z) ->
    OrderPreserving (z *.).
  Proof.
  intros z E.
  repeat (split; try apply _).
  intros x y F.
  destruct (decompose_le F) as [a [Ea1 Ea2]].
  rewrite Ea2, plus_mult_distr_l.
  apply nonneg_plus_le_compat_r.
  apply nonneg_mult_compat;trivial.
  Qed.

  Global Instance nonneg_mult_le_r : forall (z : R), PropHolds (0 ≤ z) ->
    OrderPreserving (.* z).
  Proof.
  intros. apply order_preserving_flip.
  Qed.

  Lemma mult_le_compat x₁ y₁ x₂ y₂ :
    0 ≤ x₁ -> 0 ≤ x₂ -> x₁ ≤ y₁ -> x₂ ≤ y₂ -> x₁ * x₂ ≤ y₁ * y₂.
  Proof.
  intros Ex₁ Ey₁ E1 E2.
  transitivity (y₁ * x₂).
  - apply (order_preserving_flip_nonneg (.*.) x₂);trivial.
  - apply (order_preserving_nonneg (.*.) y₁); [| trivial].
    transitivity x₁;trivial.
  Qed.

  Lemma ge_1_mult_le_compat_r x y z : 1 ≤ z -> 0 ≤ y -> x ≤ y -> x ≤ y * z.
  Proof.
  intros.
  transitivity y; [trivial |].
  pattern y at 1;apply (transport _ (mult_1_r y)).
  apply (order_preserving_nonneg (.*.) y);trivial.
  Qed.

  Lemma ge_1_mult_le_compat_l x y z : 1 ≤ z -> 0 ≤ y -> x ≤ y -> x ≤ z * y.
  Proof.
  rewrite (commutativity (f:=mult)).
  apply ge_1_mult_le_compat_r.
  Qed.

  Lemma flip_nonpos_mult_l x y z : z ≤ 0 -> x ≤ y -> z * y ≤ z * x.
  Proof.
  intros Ez Exy.
  destruct (decompose_le Ez) as [a [Ea1 Ea2]], (decompose_le Exy) as [b [Eb1 Eb2]].
  rewrite Eb2.
  apply compose_le with (a * b).
  - apply nonneg_mult_compat;trivial.
  - transitivity (z * x + (z + a) * b).
    + rewrite <-Ea2. rewrite mult_0_l,plus_0_r. reflexivity.
    + rewrite plus_mult_distr_r,plus_mult_distr_l.
      apply associativity.
  Qed.

  Lemma flip_nonpos_mult_r x y z : z ≤ 0 -> x ≤ y -> y * z ≤ x * z.
  Proof.
  rewrite 2!(commutativity _ z).
  apply flip_nonpos_mult_l.
  Qed.

  Lemma nonpos_mult x y : x ≤ 0 -> y ≤ 0 -> 0 ≤ x * y.
  Proof.
  intros.
  rewrite <-(mult_0_r x).
  apply flip_nonpos_mult_l;trivial.
  Qed.

  Lemma nonpos_nonneg_mult x y : x ≤ 0 -> 0 ≤ y -> x * y ≤ 0.
  Proof.
  intros.
  rewrite <-(mult_0_r x).
  apply flip_nonpos_mult_l;trivial.
  Qed.

  Lemma nonneg_nonpos_mult x y : 0 ≤ x -> y ≤ 0 -> x * y ≤ 0.
  Proof.
  intros.
  rewrite (commutativity (f:=mult)).
  apply nonpos_nonneg_mult;trivial.
  Qed.
End semiring_order.

(* Due to bug #2528 *)
Hint Extern 7 (PropHolds (0 ≤ _ + _)) =>
  eapply @nonneg_plus_compat : typeclass_instances.

Section strict_semiring_order.
  Context `{IsSemiRing R} `{!StrictSemiRingOrder Rlt}.
(*   Add Ring Rs : (stdlib_semiring_theory R). *)

  Global Instance plus_lt_embed : forall (z : R), StrictOrderEmbedding (+z).
  Proof.
  intro. split.
  - apply strictly_order_preserving_flip.
  - apply strictly_order_reflecting_flip.
  Qed.

  Lemma pos_plus_lt_compat_r x z : 0 < z <-> x < x + z.
  Proof.
  pattern x at 1;apply (transport _ (plus_0_r x)).
  split; intros.
  - apply (strictly_order_preserving _);trivial.
  - apply (strictly_order_reflecting (x+));trivial.
  Qed.

  Lemma pos_plus_lt_compat_l x z : 0 < z -> x < z + x.
  Proof.
  rewrite (commutativity (f:=plus)).
  apply pos_plus_lt_compat_r.
  Qed.

  Lemma plus_lt_compat x₁ y₁ x₂ y₂ : x₁ < y₁ -> x₂ < y₂ -> x₁ + x₂ < y₁ + y₂.
  Proof.
  intros E1 E2.
  transitivity (y₁ + x₂).
  - apply (strictly_order_preserving (+ x₂));trivial.
  - apply (strictly_order_preserving (y₁ +));trivial.
  Qed.

  Lemma plus_lt_compat_r x y z : 0 < z -> x < y -> x < y + z.
  Proof.
  intros. rewrite <-(plus_0_r x). apply plus_lt_compat;trivial.
  Qed.

  Lemma plus_lt_compat_l x y z : 0 < z -> x < y -> x < z + y.
  Proof.
  rewrite (commutativity (f:=plus)).
  apply plus_lt_compat_r.
  Qed.

  Lemma neg_plus_compat x y : x < 0 -> y < 0 -> x + y < 0.
  Proof.
  intros. rewrite <-(plus_0_r 0).
  apply plus_lt_compat;trivial.
  Qed.

  Instance pos_plus_compat (x y : R)
    : PropHolds (0 < x) -> PropHolds (0 < y) -> PropHolds (0 < x + y).
  Proof.
  intros. apply plus_lt_compat_l;trivial.
  Qed.

  Lemma compose_lt x y z : 0 < z -> y = x + z -> x < y.
  Proof.
  intros E1 E2.
  rewrite E2.
  apply pos_plus_lt_compat_r;trivial.
  Qed.

  Lemma decompose_lt {x y} : x < y -> exists z, 0 < z /\ y = x + z.
  Proof.
  intros E.
  destruct (strict_srorder_partial_minus x y E) as [z Ez].
  exists z. split; [| trivial].
  apply (strictly_order_reflecting (x+)).
  rewrite <-Ez, rings.plus_0_r. trivial.
  Qed.

  Global Instance pos_mult_lt_l : forall (z : R), PropHolds (0 < z) ->
    StrictlyOrderPreserving (z *.).
  Proof.
  intros z E x y F.
  destruct (decompose_lt F) as [a [Ea1 Ea2]].
  rewrite Ea2, plus_mult_distr_l.
  apply pos_plus_lt_compat_r.
  apply pos_mult_compat;trivial.
  Qed.

  Global Instance pos_mult_lt_r : forall (z : R), PropHolds (0 < z) ->
    StrictlyOrderPreserving (.* z).
  Proof.
  intros. apply strictly_order_preserving_flip.
  Qed.

  Lemma mult_lt_compat x₁ y₁ x₂ y₂ :
    0 < x₁ -> 0 < x₂ -> x₁ < y₁ -> x₂ < y₂ -> x₁ * x₂ < y₁ * y₂.
  Proof.
  intros Ex₁ Ey₁ E1 E2.
  transitivity (y₁ * x₂).
  - apply (strictly_order_preserving_flip_pos (.*.) x₂);trivial.
  - apply (strictly_order_preserving_pos (.*.) y₁); [| trivial ].
    transitivity x₁;trivial.
  Qed.

  Lemma gt_1_mult_lt_compat_r x y z : 1 < z -> 0 < y -> x < y -> x < y * z.
  Proof.
  intros.
  transitivity y; [ trivial |].
  pattern y at 1;apply (transport _ (mult_1_r y)).
  apply (strictly_order_preserving_pos (.*.) y);trivial.
  Qed.

  Lemma gt_1_mult_lt_compat_l x y z : 1 < z -> 0 < y -> x < y -> x < z * y.
  Proof.
  rewrite (commutativity (f:=mult)).
  apply gt_1_mult_lt_compat_r.
  Qed.

  Lemma flip_neg_mult_l x y z : z < 0 -> x < y -> z * y < z * x.
  Proof.
  intros Ez Exy.
  destruct (decompose_lt Ez) as [a [Ea1 Ea2]], (decompose_lt Exy) as [b [Eb1 Eb2]].
  rewrite Eb2.
  apply compose_lt with (a * b).
  - apply pos_mult_compat;trivial.
  - transitivity (z * x + (z + a) * b).
    + rewrite <-Ea2. rewrite mult_0_l,plus_0_r;reflexivity.
    + rewrite plus_mult_distr_r,plus_mult_distr_l.
      apply associativity.
  Qed.

  Lemma flip_neg_mult_r x y z : z < 0 -> x < y -> y * z < x * z.
  Proof.
  rewrite 2!(commutativity _ z).
  apply flip_neg_mult_l.
  Qed.

  Lemma neg_mult x y : x < 0 -> y < 0 -> 0 < x * y.
  Proof.
  intros.
  rewrite <-(mult_0_r x).
  apply flip_neg_mult_l;trivial.
  Qed.

  Lemma pos_mult x y : 0 < x -> 0 < y -> 0 < x * y.
  Proof.
    intros xpos ypos.
    rewrite <-(mult_0_r x).
    apply (pos_mult_lt_l); assumption.
  Qed.

  Lemma neg_pos_mult x y : x < 0 -> 0 < y -> x * y < 0.
  Proof.
  intros.
  rewrite <-(mult_0_r x).
  apply flip_neg_mult_l;trivial.
  Qed.

  Lemma pos_neg_mult x y : 0 < x -> y < 0 -> x * y < 0.
  Proof.
  intros. rewrite (commutativity (f:=mult)).
  apply neg_pos_mult;trivial.
  Qed.
End strict_semiring_order.

(* Due to bug #2528 *)
Hint Extern 7 (PropHolds (0 < _ + _)) =>
  eapply @pos_plus_compat : typeclass_instances.

Section pseudo_semiring_order.
  Context `{PseudoSemiRingOrder R} `{!IsSemiRing R}.
(*   Add Ring Rp : (stdlib_semiring_theory R). *)

  Local Existing Instance pseudo_order_apart.

  Global Instance pseudosrorder_strictsrorder : StrictSemiRingOrder (_ : Lt R).
  Proof.
  split; try apply _.
  - intros. apply pseudo_srorder_partial_minus, lt_flip. trivial.
  - apply pseudo_srorder_pos_mult_compat.
  Qed.

  Global Instance plus_strong_ext : StrongBinaryExtensionality (+).
  Proof.
  assert (forall z, StrongExtensionality (z +)).
  - intros. apply pseudo_order_embedding_ext.
  - apply apartness.strong_binary_setoid_morphism_commutative.
  Qed.

  Global Instance plus_strong_cancel_l
    : forall z, StrongLeftCancellation (+) z.
  Proof.
  intros z x y E.
  apply apart_iff_total_lt in E;apply apart_iff_total_lt.
  destruct E; [left | right]; apply (strictly_order_preserving (z +));trivial.
  Qed.

  Global Instance plus_strong_cancel_r
    : forall z, StrongRightCancellation (+) z.
  Proof.
  intros. apply (strong_right_cancel_from_left (+)).
  Qed.

  Lemma neg_mult_decompose x y : x * y < 0 -> (x < 0 /\ 0 < y) |_| (0 < x /\ y < 0).
  Proof.
  intros.
  assert (0 ≶ x) as Ex;[|assert (apart 0 y) as Ey].
  - apply (strong_extensionality (.* y)).
    rewrite mult_0_l. apply pseudo_order_lt_apart_flip;trivial.
  - apply (strong_extensionality (x *.)).
    rewrite mult_0_r. apply pseudo_order_lt_apart_flip;trivial.
  - apply apart_iff_total_lt in Ex;apply apart_iff_total_lt in Ey.
    destruct Ex as [Ex|Ex], Ey as [Ey|Ey]; try auto.
    + destruct (irreflexivity (<) 0).
      transitivity (x * y); [| trivial].
      apply pos_mult_compat;trivial.
    + destruct (irreflexivity (<) 0).
      transitivity (x * y); [| trivial].
      apply neg_mult;trivial.
  Qed.

  Lemma pos_mult_decompose x y : 0 < x * y -> (0 < x /\ 0 < y) |_| (x < 0 /\ y < 0).
  Proof.
  intros.
  assert (0 ≶ x /\ apart 0 y) as [Ex Ey];[split|].
  - apply (strong_extensionality (.* y)).
    rewrite mult_0_l. apply pseudo_order_lt_apart;trivial.
  - apply (strong_extensionality (x *.)).
    rewrite mult_0_r. apply pseudo_order_lt_apart;trivial.
  - apply apart_iff_total_lt in Ex;apply apart_iff_total_lt in Ey.
    destruct Ex as [Ex|Ex], Ey as [Ey|Ey]; try auto.
    + destruct (irreflexivity (<) 0).
      transitivity (x * y); [trivial |].
      apply pos_neg_mult;trivial.
    + destruct (irreflexivity (<) 0).
      transitivity (x * y); [trivial |].
      apply neg_pos_mult;trivial.
  Qed.

  Global Instance pos_mult_reflect_l
    : forall (z : R), PropHolds (0 < z) -> StrictlyOrderReflecting (z *.).
  Proof.
  intros z Ez x y E1.
  apply not_lt_apart_lt_flip.
  + intros E2. apply (lt_flip _ _ E1).
    apply (strictly_order_preserving (z *.));trivial.
  + apply (strong_extensionality (z *.)).
    apply pseudo_order_lt_apart_flip;trivial.
  Qed.

  Global Instance pos_mult_reflect_r
    : forall (z : R), PropHolds (0 < z) -> StrictlyOrderReflecting (.* z).
  Proof.
  intros.
  apply strictly_order_reflecting_flip.
  Qed.

  Global  Instance apartzero_mult_strong_cancel_l
    : forall z, PropHolds (z ≶ 0) -> StrongLeftCancellation (.*.) z.
  Proof.
  intros z Ez x y E. red in Ez.
  apply apart_iff_total_lt in E;apply apart_iff_total_lt in Ez;
  apply apart_iff_total_lt.
  destruct E as [E|E], Ez as [Ez|Ez].
  - right. apply flip_neg_mult_l;trivial.
  - left. apply (strictly_order_preserving_pos (.*.) z);trivial.
  - left. apply flip_neg_mult_l;trivial.
  - right. apply (strictly_order_preserving_pos (.*.) z);trivial.
  Qed.

  Global Instance apartzero_mult_strong_cancel_r
    : forall z, PropHolds (z ≶ 0) -> StrongRightCancellation (.*.) z.
  Proof.
  intros.
  apply (strong_right_cancel_from_left (.*.)).
  Qed.

  Global Instance apartzero_mult_cancel_l
    : forall z, PropHolds (z ≶ 0) -> LeftCancellation (.*.) z.
  Proof.
  intros. apply _.
  Qed.

  Global Instance apartzero_mult_cancel_r
    : forall z, PropHolds (z ≶ 0) -> RightCancellation (.*.) z.
  Proof.
  intros. apply _.
  Qed.

  Lemma square_pos x : x ≶ 0 -> 0 < x * x.
  Proof.
  intros E. apply apart_iff_total_lt in E.
  destruct E as [E|E].
  - destruct (decompose_lt E) as [z [Ez1 Ez2]].
    apply compose_lt with (z * z).
    + apply pos_mult_compat;trivial.
    + rewrite plus_0_l.
      apply (left_cancellation (+) (x * z)).
      rewrite <-plus_mult_distr_r, <-plus_mult_distr_l.
      rewrite (commutativity (f:=plus) z x), <-!Ez2.
      rewrite mult_0_l,mult_0_r. reflexivity.
  - apply pos_mult_compat;trivial.
  Qed.

  Lemma pos_mult_rev_l x y : 0 < x * y -> 0 < y -> 0 < x.
  Proof.
  intros. apply (strictly_order_reflecting (.* y)).
  rewrite rings.mult_0_l;trivial.
  Qed.

  Lemma pos_mult_rev_r x y : 0 < x * y -> 0 < x -> 0 < y.
  Proof.
  intros. apply pos_mult_rev_l with x.
  - rewrite (commutativity (f:=mult));trivial.
  - trivial.
  Qed.

  Context `{PropHolds (1 ≶ 0)}.

  Instance lt_0_1 : PropHolds (0 < 1).
  Proof.
  red.
  rewrite <-(mult_1_l 1).
  apply square_pos;trivial.
  Qed.

  Instance lt_0_2 : PropHolds (0 < 2).
  Proof.
  apply _.
  Qed.

  Instance lt_0_3 : PropHolds (0 < 3).
  Proof.
  apply _.
  Qed.

  Instance lt_0_4 : PropHolds (0 < 4).
  Proof.
  apply _.
  Qed.

  Lemma lt_1_2 : 1 < 2.
  Proof.
  apply pos_plus_lt_compat_r, lt_0_1.
  Qed.

  Lemma lt_1_3 : 1 < 3.
  Proof.
  apply pos_plus_lt_compat_r, lt_0_2.
  Qed.

  Lemma lt_1_4 : 1 < 4.
  Proof.
  apply pos_plus_lt_compat_r, lt_0_3.
  Qed.

  Lemma lt_2_3 : 2 < 3.
  Proof.
  apply (strictly_order_preserving (1+)), lt_1_2.
  Qed.

  Lemma lt_2_4 : 2 < 4.
  Proof.
  apply (strictly_order_preserving (1+)), lt_1_3.
  Qed.

  Lemma lt_3_4 : 3 < 4.
  Proof.
  apply (strictly_order_preserving (1+)), lt_2_3.
  Qed.

  Instance apart_0_2 : PropHolds (2 ≶ 0).
  Proof.
  red. apply symmetry.
  apply pseudo_order_lt_apart, lt_0_2.
  Qed.
End pseudo_semiring_order.

Hint Extern 7 (PropHolds (0 < 1)) => eapply @lt_0_1 : typeclass_instances.
Hint Extern 7 (PropHolds (0 < 2)) => eapply @lt_0_2 : typeclass_instances.
Hint Extern 7 (PropHolds (0 < 3)) => eapply @lt_0_3 : typeclass_instances.
Hint Extern 7 (PropHolds (0 < 4)) => eapply @lt_0_4 : typeclass_instances.
Hint Extern 7 (PropHolds (2 ≶ 0)) => eapply @apart_0_2 : typeclass_instances.

Section full_pseudo_semiring_order.
  Context `{FullPseudoSemiRingOrder R} `{!IsSemiRing R}.

(*   Add Ring Rf : (stdlib_semiring_theory R). *)

  Global Instance fullpseudosrorder_fullpseudoorder
    : FullPseudoOrder (_ : Le R) (_ : Lt R).
  Proof.
  split.
  - apply _.
  - apply _.
  - apply full_pseudo_srorder_le_iff_not_lt_flip.
  Qed.

  Global Instance fullpseudosrorder_srorder : SemiRingOrder (_ : Le R).
  Proof.
  split; try apply _.
  - intros x y E. apply le_iff_not_lt_flip in E.
    apply pseudo_srorder_partial_minus;trivial.
  - intros z. repeat (split; try apply _).
    + intros x y E1. apply le_iff_not_lt_flip in E1;apply le_iff_not_lt_flip.
      intros E2. apply E1.
      apply (strictly_order_reflecting (z+)). trivial.
    + intros x y E1.  apply le_iff_not_lt_flip in E1;apply le_iff_not_lt_flip.
      intros E2. apply E1.
      apply (strictly_order_preserving _);trivial.
  - intros x y Ex Ey.
    apply le_iff_not_lt_flip in Ex;apply le_iff_not_lt_flip in Ey;
    apply le_iff_not_lt_flip.
    intros E.
    destruct (neg_mult_decompose x y E) as [[? ?]|[? ?]];auto.
  Qed.

  Global Instance : forall (z : R), PropHolds (0 < z) -> OrderReflecting (z *.).
  Proof.
  intros z E. apply full_pseudo_order_reflecting.
  Qed.

  Global Instance: forall (z : R), PropHolds (0 < z) -> OrderReflecting (.* z).
  Proof.
  intros. apply order_reflecting_flip.
  Qed.

  Lemma plus_lt_le_compat x₁ y₁ x₂ y₂ : x₁ < y₁ -> x₂ ≤ y₂ -> x₁ + x₂ < y₁ + y₂.
  Proof.
  intros E1 E2.
  apply lt_le_trans with (y₁ + x₂).
  - apply (strictly_order_preserving (+ x₂));trivial.
  - apply (order_preserving (y₁ +));trivial.
  Qed.

  Lemma plus_le_lt_compat x₁ y₁ x₂ y₂ : x₁ ≤ y₁ -> x₂ < y₂ -> x₁ + x₂ < y₁ + y₂.
  Proof.
  intros E1 E2.
  apply le_lt_trans with (y₁ + x₂).
  - apply (order_preserving (+ x₂));trivial.
  - apply (strictly_order_preserving (y₁ +));trivial.
  Qed.

  Lemma nonneg_plus_lt_compat_r x y z : 0 ≤ z -> x < y -> x < y + z.
  Proof.
  intros. rewrite <-(plus_0_r x). apply plus_lt_le_compat;trivial.
  Qed.

  Lemma nonneg_plus_lt_compat_l x y z : 0 ≤ z -> x < y -> x < z + y.
  Proof.
  intros. rewrite (commutativity (f:=plus)).
  apply nonneg_plus_lt_compat_r;trivial.
  Qed.

  Lemma pos_plus_le_lt_compat_r x y z : 0 < z -> x ≤ y -> x < y + z.
  Proof.
  intros. rewrite <-(plus_0_r x). apply plus_le_lt_compat;trivial.
  Qed.

  Lemma pos_plus_le_lt_compat_l x y z : 0 < z -> x ≤ y -> x < z + y.
  Proof.
  intros. rewrite (commutativity (f:=plus)).
  apply pos_plus_le_lt_compat_r;trivial.
  Qed.

  Lemma square_nonneg x : 0 ≤ x * x.
  Proof.
  apply not_lt_le_flip. intros E.
  destruct (lt_antisym (x * x) 0).
  split; [trivial |].
  apply square_pos.
  pose proof pseudo_order_apart.
  apply (strong_extensionality (x *.)).
  rewrite mult_0_r.
  apply lt_apart. trivial.
  Qed.

  Lemma nonneg_mult_rev_l x y : 0 ≤ x * y -> 0 < y -> 0 ≤ x.
  Proof.
  intros. apply (order_reflecting (.* y)).
  rewrite rings.mult_0_l. trivial.
  Qed.

  Lemma nonneg_mult_rev_r x y : 0 ≤ x * y -> 0 < x -> 0 ≤ y.
  Proof.
  intros. apply nonneg_mult_rev_l with x.
  - rewrite (commutativity (f:=mult)). trivial.
  - trivial.
  Qed.

  Instance le_0_1 : PropHolds (0 ≤ 1).
  Proof.
  red. rewrite <-(mult_1_r 1). apply square_nonneg.
  Qed.

  Instance le_0_2 : PropHolds (0 ≤ 2).
  Proof. solve_propholds. Qed.

  Instance le_0_3 : PropHolds (0 ≤ 3).
  Proof. solve_propholds. Qed.

  Instance le_0_4 : PropHolds (0 ≤ 4).
  Proof. solve_propholds. Qed.

  Lemma le_1_2 : 1 ≤ 2.
  Proof.
  apply nonneg_plus_le_compat_r, le_0_1.
  Qed.

  Lemma le_1_3 : 1 ≤ 3.
  Proof.
  apply nonneg_plus_le_compat_r, le_0_2.
  Qed.

  Lemma le_1_4 : 1 ≤ 4.
  Proof.
  apply nonneg_plus_le_compat_r, le_0_3.
  Qed.

  Lemma le_2_3 : 2 ≤ 3.
  Proof.
  apply (order_preserving (1+)), le_1_2.
  Qed.

  Lemma le_2_4 : 2 ≤ 4.
  Proof.
  apply (order_preserving (1+)), le_1_3.
  Qed.

  Lemma le_3_4 : 3 ≤ 4.
  Proof.
  apply (order_preserving (1+)), le_2_3.
  Qed.

  Lemma ge_1_mult_compat x y : 1 ≤ x -> 1 ≤ y -> 1 ≤ x * y.
  Proof.
  intros.
  apply ge_1_mult_le_compat_r; trivial.
  transitivity 1.
  - apply le_0_1.
  - trivial.
  Qed.

  Lemma gt_1_ge_1_mult_compat x y : 1 < x -> 1 ≤ y -> 1 < x * y.
  Proof.
  intros.
  apply lt_le_trans with x; trivial.
  apply ge_1_mult_le_compat_r;[trivial| |apply reflexivity].
  transitivity 1.
  - apply le_0_1.
  - apply lt_le;trivial.
  Qed.

  Lemma ge_1_gt_1_mult_compat x y : 1 ≤ x -> 1 < y -> 1 < x * y.
  Proof.
  intros.
  rewrite (commutativity (f:=mult)).
  apply gt_1_ge_1_mult_compat;trivial.
  Qed.

  Lemma pos_mult_le_lt_compat : forall a b c d, 0 <= a /\ a <= b -> 0 < b ->
    0 <= c /\ c < d ->
    a * c < b * d.
  Proof.
  intros a b c d [E1 E2] E3 [E4 E5] .
  apply le_lt_trans with (b * c).
  - apply mult_le_compat;auto.
  - apply (strictly_order_preserving (b *.)). trivial.
  Qed.

  Context `{PropHolds (1 ≶ 0)}.

  Lemma not_le_1_0 : ~1 ≤ 0.
  Proof.
  apply lt_not_le_flip, lt_0_1.
  Qed.

  Lemma not_le_2_0 : ~2 ≤ 0.
  Proof.
  apply lt_not_le_flip, lt_0_2.
  Qed.

  Lemma repeat_nat_nonneg : forall n, 0 <= Peano.nat_iter n (plus 1) 0.
  Proof.
  induction n;simpl.
  - reflexivity.
  - apply nonneg_plus_compat.
    + apply _.
    + apply IHn.
  Qed.

  Lemma repeat_nat_pos : forall n, 0 < Peano.nat_iter (S n) (plus 1) 0.
  Proof.
  intros n. simpl.
  apply pos_plus_le_lt_compat_l.
  - solve_propholds.
  - apply repeat_nat_nonneg.
  Qed.

  Local Existing Instance pseudo_order_apart.

  Global Instance ordered_characteristic_0 : FieldCharacteristic R 0.
  Proof.
  hnf. intros [|n] _;split.
  - intros E'. destruct (E' O). reflexivity.
  - intros E';apply (irreflexivity _) in E';destruct E'.
  - intros _;apply apart_iff_total_lt;right;apply repeat_nat_pos.
  - intros _ m;simpl. intros E.
    apply (ap (fun n => match n with | S _ => Unit | _ => Empty end)) in E;
    simpl in E. rewrite <-E. trivial.
  Qed.
End full_pseudo_semiring_order.

(* Due to bug #2528 *)
Hint Extern 7 (PropHolds (0 ≤ 1)) => eapply @le_0_1 : typeclass_instances.
Hint Extern 7 (PropHolds (0 ≤ 2)) => eapply @le_0_2 : typeclass_instances.
Hint Extern 7 (PropHolds (0 ≤ 3)) => eapply @le_0_3 : typeclass_instances.
Hint Extern 7 (PropHolds (0 ≤ 4)) => eapply @le_0_4 : typeclass_instances.

Section dec_semiring_order.
  (* Maybe these assumptions can be weakened? *)
  Context `{SemiRingOrder R} `{Apart R} `{!TrivialApart R}
    `{!NoZeroDivisors R} `{!TotalRelation (≤)} `{DecidablePaths R}.

  Context `{Rlt : Lt R} `{is_mere_relation R lt}
    (lt_correct : forall x y, x < y <-> x ≤ y /\ x <> y).

  Instance dec_srorder_fullpseudo
    : FullPseudoOrder _ _ := dec_full_pseudo_order lt_correct.
  Local Existing Instance pseudo_order_apart.

  Instance dec_pseudo_srorder: PseudoSemiRingOrder (<).
  Proof.
  split; try apply _.
  - intros x y E. apply srorder_partial_minus, not_lt_le_flip;trivial.
  - intros z. repeat (split; try apply _).
    intros x y E. apply lt_correct in E;apply lt_correct.
    destruct E as [E2a E2b]. split.
    + apply (order_preserving (z+));trivial.
    + intros E3. apply E2b. apply (left_cancellation (+) z);trivial.
  - apply (apartness.dec_strong_binary_morphism (.*.)).
  - intros x y E1 E2.
    apply lt_correct in E1;apply lt_correct in E2;apply lt_correct.
    destruct E1 as [E1a E1b], E2 as [E2a E2b]. split.
    + apply nonneg_mult_compat;trivial.
    + apply symmetric_neq.
      apply mult_ne_0; apply symmetric_neq;trivial.
  Qed.

  Instance dec_full_pseudo_srorder: FullPseudoSemiRingOrder (≤) (<).
  Proof.
  split; try apply _.
  apply le_iff_not_lt_flip.
  Qed.
End dec_semiring_order.

Section another_semiring.
  Context `{SemiRingOrder R1}.

  Lemma projected_srorder `{IsSemiRing R2} `{R2le : Le R2}
    `{is_mere_relation R2 R2le} (f : R2 -> R1)
    `{!IsSemiRingPreserving f} `{!IsInjective f}
    : (forall x y, x ≤ y <-> f x ≤ f y) -> (forall x y : R2, x ≤ y -> exists z, y = x + z) ->
      SemiRingOrder R2le.
  Proof.
  intros P. pose proof (projected_partial_order f P).
  repeat (split; try apply _).
  - assumption.
  - red;intros. apply P.
    rewrite 2!(preserves_plus (f:=f)). apply (order_preserving _), P. trivial.
  - red;intros. apply P. apply (order_reflecting (f z +)).
    rewrite <-2!preserves_plus. apply P. trivial.
  - intros. apply P. rewrite preserves_mult, preserves_0.
    apply nonneg_mult_compat; rewrite <-(preserves_0 (f:=f)); apply P;trivial.
  Qed.

 Context `{!IsSemiRing R1} `{SemiRingOrder R2} `{!IsSemiRing R2}
   `{!IsSemiRingPreserving (f : R1 -> R2)}.

  (* If a morphism agrees on the positive cone then it is order preserving *)
  Lemma preserving_preserves_nonneg : (forall x, 0 ≤ x -> 0 ≤ f x) -> OrderPreserving f.
  Proof.
  intros E.
  repeat (split; try apply _).
  intros x y F.
  destruct (decompose_le F) as [z [Ez1 Ez2]].
  apply compose_le with (f z).
  - apply E;trivial.
  - rewrite Ez2, (preserves_plus (f:=f)). trivial.
  Qed.

  Instance preserves_nonneg `{!OrderPreserving f} x
    : PropHolds (0 ≤ x) -> PropHolds (0 ≤ f x).
  Proof.
  intros. rewrite <-(preserves_0 (f:=f)). apply (order_preserving f);trivial.
  Qed.

  Lemma preserves_nonpos `{!OrderPreserving f} x : x ≤ 0 -> f x ≤ 0.
  Proof.
  intros. rewrite <-(preserves_0 (f:=f)). apply (order_preserving f);trivial.
  Qed.

  Lemma preserves_ge_1 `{!OrderPreserving f} x : 1 ≤ x -> 1 ≤ f x.
  Proof.
  intros. rewrite <-(preserves_1 (f:=f)). apply (order_preserving f);trivial.
  Qed.

  Lemma preserves_le_1 `{!OrderPreserving f} x : x ≤ 1 -> f x ≤ 1.
  Proof.
  intros. rewrite <-(preserves_1 (f:=f)). apply (order_preserving f);trivial.
  Qed.
End another_semiring.

Section another_semiring_strict.
  Context `{StrictSemiRingOrder R1} `{StrictSemiRingOrder R2}
    `{!IsSemiRing R1} `{!IsSemiRing R2}
    `{!IsSemiRingPreserving (f : R1 -> R2)}.

  Lemma strictly_preserving_preserves_pos
    : (forall x, 0 < x -> 0 < f x) -> StrictlyOrderPreserving f.
  Proof.
  intros E.
  repeat (split; try apply _).
  intros x y F.
  destruct (decompose_lt F) as [z [Ez1 Ez2]].
  apply compose_lt with (f z).
  - apply E. trivial.
  - rewrite Ez2, (preserves_plus (f:=f)). trivial.
  Qed.

  Instance preserves_pos `{!StrictlyOrderPreserving f} x
   : PropHolds (0 < x) -> PropHolds (0 < f x).
  Proof.
  intros. rewrite <-(preserves_0 (f:=f)).
  apply (strictly_order_preserving f);trivial.
  Qed.

  Lemma preserves_neg `{!StrictlyOrderPreserving f} x
    : x < 0 -> f x < 0.
  Proof.
  intros. rewrite <-(preserves_0 (f:=f)).
  apply (strictly_order_preserving f);trivial.
  Qed.

  Lemma preserves_gt_1 `{!StrictlyOrderPreserving f} x
    : 1 < x -> 1 < f x.
  Proof.
  intros. rewrite <-(preserves_1 (f:=f)).
  apply (strictly_order_preserving f);trivial.
  Qed.

  Lemma preserves_lt_1 `{!StrictlyOrderPreserving f} x
    : x < 1 -> f x < 1.
  Proof.
  intros. rewrite <-(preserves_1 (f:=f)).
  apply (strictly_order_preserving f);trivial.
  Qed.
End another_semiring_strict.

(* Due to bug #2528 *)
Hint Extern 15 (PropHolds (_ ≤ _ _)) =>
  eapply @preserves_nonneg : typeclass_instances.
Hint Extern 15 (PropHolds (_ < _ _)) =>
  eapply @preserves_pos : typeclass_instances.

(* Oddly enough, the above hints do not work for goals of the following shape? *)
Hint Extern 15 (PropHolds (_ ≤ '_)) =>
  eapply @preserves_nonneg : typeclass_instances.
Hint Extern 15 (PropHolds (_ < '_)) =>
  eapply @preserves_pos : typeclass_instances.
