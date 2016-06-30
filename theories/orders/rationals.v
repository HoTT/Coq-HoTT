Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.orders
  HoTTClasses.interfaces.naturals
  HoTTClasses.interfaces.rationals
  HoTTClasses.interfaces.integers
  HoTTClasses.implementations.natpair_integers
  HoTTClasses.theory.rationals
  HoTTClasses.theory.dec_fields
  HoTTClasses.theory.rings
  HoTTClasses.orders.integers
  HoTTClasses.orders.dec_fields.

Section rationals_and_integers.
  Context `{Rationals Q} {Qle : Le Q} `{!SemiRingOrder Qle}
    Z `{Integers Z} `{Apart Z} `{!TrivialApart Z}
    `{!FullPseudoSemiRingOrder (A:=Z) Zle Zlt}
    {f : Z → Q} `{!SemiRingPreserving f}.
(*   Add Field Q : (stdlib_field_theory Q). *)

  Lemma rationals_decompose_pos_den x :
    merely (∃ num, ∃ den, 0 < den ∧ x = f num / f den).
  Proof.
  apply (merely_destruct (rationals_decompose x)).
  intros [num [den [E1 E2]]].
  destruct (total (≤) den 0).
  - apply tr. exists (-num), (-den). split.
    + apply lt_iff_le_ne. split.
      { apply rings.flip_nonpos_negate. trivial. }
      { apply not_symmetry. apply flip_negate_ne_0. rewrite involutive. trivial. }
    + rewrite 2!(preserves_negate (f:=f)). rewrite E2.
      rewrite <-dec_recip_negate,negate_mult_negate.
      trivial.
  - apply tr.
    exists num. exists den. split; try assumption.
    apply lt_iff_le_ne. split;trivial. apply not_symmetry;trivial.
  Qed.
End rationals_and_integers.
(* 
(* A PseudoRingOrder uniquely specifies the orders on the rationals *)
Section rationals_and_another_rationals.
  Context `{Rationals Q1} `{Apart Q1} `{!TrivialApart Q1}
    {Q1le Q1lt} `{!FullPseudoSemiRingOrder (A:=Q1) Q1le Q1lt}.
  Context `{Rationals Q2} `{Apart Q2} `{!TrivialApart Q2}
    {Q2le Q2lt} `{!FullPseudoSemiRingOrder (A:=Q2) Q2le Q2lt}
    `{is_mere_relation Q2 le}
     {f : Q1 → Q2} `{!SemiRingPreserving f}.

(*   Add Field Q1 : (stdlib_field_theory Q1). *)

  Notation i_to_r := (integers.integers_to_ring (NatPair.Z nat) Q1).

  Let f_preserves_nonneg x : 0 ≤ x → 0 ≤ f x.
  Proof.
  intros E.
  apply (merely_destruct (rationals_decompose_pos_den (NatPair.Z nat)
    (FullPseudoSemiRingOrder0:=(NatPair.Z_full_pseudo_srorder nat)) x)).
  intros [num [den [E1 E2]]].
  rewrite E2 in E |- *. clear E2.
  rewrite preserves_mult, preserves_dec_recip.
  pose proof OrderReflecting_instance_0.
  apply (order_reflecting_pos (.*.) (f (i_to_r den))).
  - change (0 < (f ∘ i_to_r) den).
    rewrite (integers.to_ring_unique (compose f i_to_r)).
    pose proof rationals_embed_ints.
    apply (semirings.preserves_pos (Alt:=NatPair.Z_lt nat)).
    unfold lt in *. apply E1.
  - apply (order_preserving_nonneg (.*.) (i_to_r den)) in E.
    + rewrite right_absorb. rewrite right_absorb in E.
      rewrite (mult_comm (f (i_to_r num))), mult_assoc,
        dec_recip_inverse, left_identity.
      * rewrite (mult_comm (i_to_r num)), mult_assoc,
          dec_recip_inverse, left_identity in E.
        { change (0 ≤ (f ∘ i_to_r) num).
          rewrite (integers.to_ring_unique (compose f i_to_r)).
          rewrite <-(preserves_0 (f:=integers_to_ring (NatPair.Z nat) Q2)).
          apply (order_preserving _).
          apply (order_reflecting i_to_r).
          rewrite preserves_0. trivial. }
        { apply injective_ne_0. apply lt_ne_flip;trivial. }
      * apply (injective_ne_0 (f:=compose f i_to_r)).
        apply lt_ne_flip;trivial.
    + apply (semirings.preserves_nonneg (Ale:=NatPair.Z_le nat)).
      apply (lt_le _ _ E1).
  Qed.

  Instance morphism_order_preserving: OrderPreserving f.
  Proof. apply semirings.preserving_preserves_nonneg. apply f_preserves_nonneg. Qed.
End rationals_and_another_rationals.

Section rationals_order_isomorphic.
  Context `{Rationals Q1} `{Apart Q1} `{!TrivialApart Q1}
    `{!FullPseudoSemiRingOrder (A:=Q1) Q1le Q1lt}
    `{Rationals Q2} `{Apart Q2} `{!TrivialApart Q2}
      `{!FullPseudoSemiRingOrder (A:=Q2) Q2le Q2lt}
     {f : Q1 → Q2} `{!SemiRing_Morphism f}.

  Global Instance: OrderEmbedding f.
  Proof.
    split.
     apply morphism_order_preserving.
    repeat (split; try apply _).
    intros x y E.
    rewrite <-(to_rationals_involutive x (Q2:=Q2)),
      <-(to_rationals_involutive y (Q2:=Q2)).
    rewrite <-2!(to_rationals_unique f).
    now apply (morphism_order_preserving (f:=rationals_to_rationals Q2 Q1)).
  Qed.
End rationals_order_isomorphic.

Instance rationals_le `{Rationals Q} : Le Q | 10 := λ x y,
  ∃ num, ∃ den,
  y = x + naturals_to_semiring nat Q num / naturals_to_semiring nat Q den.
Instance rationals_lt  `{Rationals Q} : Lt Q | 10 := dec_lt.

Section default_order.
  Context `{Rationals Q} `{Apart Q} `{!TrivialApart Q}.

  Add Field F: (stdlib_field_theory Q).
  Notation n_to_sr := (naturals_to_semiring nat Q).

  Instance: Proper ((=) ==> (=) ==> iff) rationals_le.
  Proof.
    intros x x' E y y' E'. unfold rationals_le.
    split; intros [n [d d_nonzero]]; exists n, d.
     now rewrite <-E, <-E'.
    now rewrite E, E'.
  Qed.

  Instance: Reflexive rationals_le.
  Proof. intro. exists (0:nat), (0:nat). rewrite preserves_0. ring. Qed.

  (* rationals_le can actually only happen if the denominator is nonzero: *)
  Lemma rationals_decompose_le (x y: Q) :
    x ≤ y → ∃ num, ∃ den, den ≠ 0 ∧ y = x + n_to_sr num * / n_to_sr den.
  Proof with eauto.
    intros [n [d E]].
    destruct (decide (d = 0)) as [A|A]...
    exists (0:nat), (1:nat).
    split. discriminate.
    rewrite E, A, preserves_0, preserves_1, dec_recip_0.
    ring.
  Qed.

  Instance: Transitive rationals_le.
  Proof with auto.
    intros x y z E1 E2.
    destruct (rationals_decompose_le x y) as [n1 [d1 [A1 B1]]]...
    destruct (rationals_decompose_le y z) as [n2 [d2 [A2 B2]]]...
    exists (n1 * d2 + n2 * d1), (d1 * d2).
    rewrite B2, B1.
    rewrite preserves_plus.
    rewrite ?preserves_mult.
    field. split; now apply injective_ne_0.
  Qed.

  Instance: AntiSymmetric rationals_le.
  Proof with auto.
    intros x y E1 E2.
    destruct (rationals_decompose_le x y) as [n1 [d1 [A1 B1]]]...
    destruct (rationals_decompose_le y x) as [n2 [d2 [A2 B2]]]...
    rewrite B1 in B2 |- *.
    clear E1 E2 B1 y.
    rewrite <-associativity in B2. rewrite <-(plus_0_r x) in B2 at 1.
    apply (left_cancellation (+) x) in B2.
    destruct (zero_product n1 d2) as [F|F]...
      apply naturals.zero_sum with (d1 * n2).
      apply (injective n_to_sr).
      rewrite preserves_plus, preserves_mult, preserves_mult, preserves_0.
      apply (left_cancellation_ne_0 (.*.) (/n_to_sr d1)).
       apply dec_recip_ne_0. apply injective_ne_0...
      apply (left_cancellation_ne_0 (.*.) (/n_to_sr d2)).
       apply dec_recip_ne_0. apply injective_ne_0...
      ring_simplify.
      etransitivity.
       2: now symmetry; eauto.
      field.
      split; apply injective_ne_0...
     rewrite F. rewrite preserves_0. ring.
    contradiction.
  Qed.

  Instance: PartialOrder rationals_le.
  Proof. repeat (split; try apply _). Qed.

  Instance: SemiRingOrder rationals_le.
  Proof.
    apply from_ring_order.
     repeat (split; try apply _).
     intros x y [n [d E]]. exists n, d. rewrite E. ring.
    intros x y [n1 [d1 E1]] [n2 [d2 E2]].
    exists (n1 * n2), (d1 * d2).
    rewrite 2!preserves_mult.
    rewrite E1, E2, dec_recip_distr. ring.
  Qed.

  Notation i_to_r := (integers_to_ring (SRpair nat) Q).
  Instance: TotalRelation rationals_le.
  Proof with auto.
    assert (∀ xn xd yn yd, 0 < xd → 0 < yd →
      xn * yd ≤ yn * xd → i_to_r xn / i_to_r xd ≤ i_to_r yn / i_to_r yd) as P.
     intros xn xd yn yd.
     rewrite !lt_iff_le_apart.
     intros [xd_ge0 xd_ne0] [yd_ge0 yd_ne0] E.
     destruct (semirings.decompose_le E) as [z [Ez1 Ex2]].
     apply nat_int_le_plus in xd_ge0. apply nat_int_le_plus in yd_ge0.
      apply nat_int_le_plus in Ez1.
     destruct xd_ge0 as [xd' xd_ge0], yd_ge0 as [yd' yd_ge0], Ez1 as [z' Ez1].
     rewrite left_identity in xd_ge0, yd_ge0, Ez1.
     exists z'. exists (xd' * yd').
     assert (∀ a, (i_to_r ∘ naturals_to_semiring nat (SRpair nat)) a = n_to_sr a)
      as F.
      intros a. apply (naturals.to_semiring_unique _).
     rewrite preserves_mult, <-F, <-F, <-F.
     unfold compose. rewrite <-xd_ge0, <-yd_ge0, <-Ez1.
     transitivity ((i_to_r yn * i_to_r xd) / (i_to_r yd * i_to_r xd)).
      field. split; apply injective_ne_0; apply not_symmetry...
     rewrite <-preserves_mult, Ex2, preserves_plus, preserves_mult.
     field. split; apply injective_ne_0; apply not_symmetry...
    intros x y.
    destruct (rationals_decompose_pos_den (SRpair nat) x) as [xn [xd [E1x E2x]]].
    destruct (rationals_decompose_pos_den (SRpair nat) y) as [yn [yd [E1y E2y]]].
    rewrite E2x, E2y.
    destruct (total (≤) (xn * yd) (yn * xd)); [left | right]; now apply P.
  Qed.

  Global Instance: FullPseudoSemiRingOrder rationals_le rationals_lt.
  Proof. now apply dec_full_pseudo_srorder. Qed.
End default_order.
 *)