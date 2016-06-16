Require Import HoTT.Basics.Decidable.
Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.orders
  HoTTClasses.theory.apartness.

Lemma irrefl_neq `{R : relation A} `{!Irreflexive R} : forall x y, R x y -> ~ x = y.
Proof.
intros ?? E e;rewrite e in E. apply (irreflexivity _ _ E).
Qed.

Lemma le_flip `{Le A} `{!TotalRelation (≤)} x y : ¬y ≤ x → x ≤ y.
Proof.
intros nle.
destruct (total _ x y) as [?|le];auto.
destruct (nle le).
Qed.

Section partial_order.
  Context `{PartialOrder A}.

  Lemma eq_le x y : x = y → x ≤ y.
  Proof.
  intros E.
  rewrite E.
  apply reflexivity.
  Qed.

  Lemma eq_le_flip x y : x = y → y ≤ x.
  Proof.
  intros E.
  rewrite E.
  apply reflexivity.
  Qed.

  Lemma not_le_ne x y : ¬x ≤ y → x ≠ y.
  Proof.
  intros E1 E2.
  apply E1.
  rewrite E2.
  apply reflexivity.
  Qed.

  Lemma eq_iff_le x y : x = y ↔ x ≤ y ∧ y ≤ x.
  Proof.
  split; intros E.
  - rewrite E. split;apply reflexivity.
  - apply (antisymmetry (≤) x y);apply E.
  Qed.
End partial_order.

Section strict_order.
  Context `{StrictOrder A}.

  Lemma lt_flip x y : x < y → ¬y < x.
  Proof.
  intros E1 E2.
  apply (irreflexivity (<) x).
  transitivity y;assumption.
  Qed.

  Lemma lt_antisym x y : ¬(x < y < x).
  Proof.
  intros [E1 E2].
  destruct (lt_flip x y);assumption.
  Qed.

  Lemma lt_ne x y : x < y → x ≠ y.
  Proof.
  intros E1 E2.
  rewrite E2 in E1.
  apply (irreflexivity (<) y). assumption.
  Qed.

  Lemma lt_ne_flip x y : x < y → y ≠ x.
  Proof.
  intro.
  apply not_symmetry, lt_ne.
  assumption.
  Qed.

  Lemma eq_not_lt x y : x = y → ¬x < y.
  Proof.
  intros E.
  rewrite E.
  apply (irreflexivity (<)).
  Qed.
End strict_order.

Section pseudo_order.
  Context `{PseudoOrder A}.

  Instance: IsApart A := pseudo_order_apart.

  Lemma apart_total_lt x y : x ≶ y → x < y ∨ y < x.
  Proof.
  intros.
  apply apart_iff_total_lt.
  assumption.
  Qed.

  Lemma pseudo_order_lt_apart x y : x < y → x ≶ y.
  Proof.
  intros.
  apply apart_iff_total_lt.
  auto.
  Qed.

  Lemma pseudo_order_lt_apart_flip x y : x < y → y ≶ x.
  Proof.
  intros.
  apply apart_iff_total_lt.
  auto.
  Qed.

  Lemma not_lt_apart_lt_flip x y : ¬x < y → x ≶ y → y < x.
  Proof.
  intros nlt neq. apply apart_iff_total_lt in neq.
  destruct neq.
  - destruct nlt;auto.
  - auto.
  Qed.

  Lemma pseudo_order_cotrans_twice x₁ y₁ x₂ y₂ : x₁ < y₁ → x₂ < y₂ ∨ x₁ < x₂ ∨ y₂ < y₁.
  Proof.
  intros E1.
  destruct (cotransitive E1 x₂) as [?|E2];auto.
  destruct (cotransitive E2 y₂);auto.
  Qed.

  Lemma pseudo_order_lt_ext x₁ y₁ x₂ y₂ : x₁ < y₁ → x₂ < y₂ ∨ x₁ ≶ x₂ ∨ y₂ ≶ y₁.
  Proof.
  intros E.
  destruct (pseudo_order_cotrans_twice x₁ y₁ x₂ y₂ E) as [?|[?|?]];
  auto using pseudo_order_lt_apart.
  Qed.

  Global Instance: StrictOrder (_ : Lt A).
  Proof.
  split.
  - intros x E.
    destruct (pseudo_order_antisym x x); auto.
  - intros x y z E1 E2.
    destruct (cotransitive E1 z); trivial.
    destruct (pseudo_order_antisym y z); auto.
  Qed.

  Global Instance: Transitive (complement (<)).
  Proof.
  intros x y z.
  intros E1 E2 E3.
  destruct (cotransitive E3 y); contradiction.
  Qed.

  Global Instance: AntiSymmetric (complement (<)).
  Proof.
  intros x y H1 H2.
  apply tight_apart. intros nap. apply apart_iff_total_lt in nap.
  destruct nap;auto.
  Qed.

  Lemma ne_total_lt `{!TrivialApart A} x y : x ≠ y → x < y ∨ y < x.
  Proof.
  intros neq;apply trivial_apart in neq.
  apply apart_total_lt. assumption.
  Qed.

  Global Instance lt_trichotomy `{!TrivialApart A} `{DecidablePaths A}
    : Trichotomy (<).
  Proof.
  intros x y.
  destruct (decide (x = y)) as [?|?]; try auto.
  destruct (ne_total_lt x y); auto.
  Qed.
End pseudo_order.

Section full_partial_order.
  Context `{FullPartialOrder A}.

  Instance: IsApart A := strict_po_apart.

  (* Duplicate of strong_setoids.apart_ne. This is useful because a
    StrongSetoid is not defined as a substructure of a FullPartialOrder *)
  Instance strict_po_apart_ne x y : PropHolds (x ≶ y) → PropHolds (x ≠ y).
  Proof.
  intros; apply _.
  Qed.

  Global Instance: StrictOrder (<).
  Proof.
  split; try apply _.
  intros x. red. intros E;apply lt_iff_le_apart in E.
  destruct E as [_ ?].
  apply (irreflexivity (≶) x).
  assumption.
  Qed.

  Lemma lt_le x y : PropHolds (x < y) → PropHolds (x ≤ y).
  Proof.
  intro.
  apply lt_iff_le_apart.
  assumption.
  Qed.

  Lemma not_le_not_lt x y : ¬x ≤ y → ¬x < y.
  Proof.
  intros E1 E2.
  apply E1. apply lt_le. assumption.
  Qed.

  Lemma lt_apart x y : x < y → x ≶ y.
  Proof.
  intro.
  apply lt_iff_le_apart.
  assumption.
  Qed.

  Lemma lt_apart_flip x y : x < y → y ≶ x.
  Proof.
  intro.
  apply symmetry, lt_iff_le_apart.
  assumption.
  Qed.

  Lemma le_not_lt_flip x y : y ≤ x → ¬x < y.
  Proof.
  intros E1 E2;apply lt_iff_le_apart in E2.
  destruct E2 as [E2a E2b].
  revert E2b. apply tight_apart.
  apply (antisymmetry (≤));assumption.
  Qed.

  Lemma lt_not_le_flip x y : y < x → ¬x ≤ y.
  Proof.
  intros E1 E2.
  apply (le_not_lt_flip y x);assumption.
  Qed.

  Lemma lt_le_trans x y z : x < y → y ≤ z → x < z.
  Proof.
  intros E1 E2.
  apply lt_iff_le_apart. apply lt_iff_le_apart in E1.
  destruct E1 as [E1a E1b].
  split.
  - transitivity y;assumption.
  - destruct (cotransitive E1b z) as [E3 | E3]; trivial.
    apply lt_apart. apply symmetry in E3.
    transitivity y;apply lt_iff_le_apart; auto.
  Qed.

  Lemma le_lt_trans x y z : x ≤ y → y < z → x < z.
  Proof.
  intros E2 E1.
  apply lt_iff_le_apart. apply lt_iff_le_apart in E1.
  destruct E1 as [E1a E1b].
  split.
  - transitivity y;auto.
  - destruct (cotransitive E1b x) as [E3 | E3]; trivial.
    apply lt_apart. apply symmetry in E3.
    transitivity y; apply lt_iff_le_apart; auto.
  Qed.

  Lemma lt_iff_le_ne `{!TrivialApart A} x y : x < y ↔ x ≤ y ∧ x ≠ y.
  Proof.
   transitivity (x <= y /\ apart x y).
   apply lt_iff_le_apart.
   split;intros [E1 E2];split;trivial;apply trivial_apart;trivial.
   Qed.

  Lemma le_equiv_lt `{!TrivialApart A} `{∀ x y : A, Decision (x = y)} x y
    : x ≤ y → x = y ∨ x < y.
  Proof.
  intros.
  destruct (decide (x = y)); try auto.
  right.
  apply lt_iff_le_ne; auto.
  Qed.

  Instance dec_from_lt_dec `{!TrivialApart A} `{∀ x y, Decision (x ≤ y)}
    : DecidablePaths A.
  Proof.
  intros x y.
  destruct (decide_rel (<=) x y) as [E1|E1];
  [destruct (decide_rel (<=) y x) as [E2|E2]|].
  - left. apply (antisymmetry (<=));assumption.
  - right. intros E3;apply E2.
    pattern y. apply (transport _ E3).
    apply reflexivity.
  - right. intros E3;apply E1.
    pattern y; apply (transport _ E3).
    apply reflexivity.
  Defined.

  Definition lt_dec_slow `{!TrivialApart A} `{∀ x y, Decision (x ≤ y)} :
    ∀ x y, Decision (x < y).
  Proof.
  intros x y.
  destruct (decide (x ≤ y));
  [destruct (decide (x = y))|].
  - right. apply eq_not_lt. assumption.
  - left. apply lt_iff_le_ne. auto.
  - right. apply not_le_not_lt. assumption.
  Defined.
End full_partial_order.

(* Due to bug #2528 *)
Hint Extern 5 (PropHolds (_ ≠ _)) => eapply @strict_po_apart_ne :  typeclass_instances.
Hint Extern 10 (PropHolds (_ ≤ _)) => eapply @lt_le : typeclass_instances.
Hint Extern 20 (Decision (_ < _)) => eapply @lt_dec_slow : typeclass_instances.

Section full_pseudo_order.
  Context `{FullPseudoOrder A}.

  Instance: IsApart A := pseudo_order_apart.

  Lemma not_lt_le_flip x y : ¬y < x → x ≤ y.
  Proof.
  intros.
  apply le_iff_not_lt_flip.
  assumption.
  Qed.

  Instance: PartialOrder (≤).
  Proof.
  repeat split.
  - intros x. apply not_lt_le_flip, (irreflexivity (<)).
  - intros x y z E1 E2.
    apply le_iff_not_lt_flip;
    apply le_iff_not_lt_flip in E1;
    apply le_iff_not_lt_flip in E2.
    change (complement (<) z x).
    transitivity y;assumption.
  - intros x y E1 E2.
    apply le_iff_not_lt_flip in E1;
    apply le_iff_not_lt_flip in E2.
    apply (antisymmetry (complement (<)));assumption.
  Qed.

  Global Instance: FullPartialOrder (_ : Le A) (_ : Lt A).
  Proof.
  split; try apply _.
  intros x y.
  transitivity (~ lt y x /\ apart x y);[|
  split;intros [? ?];split;trivial;apply le_iff_not_lt_flip;trivial].
  split.
  - intros E. split.
    + apply lt_flip;assumption.
    + apply pseudo_order_lt_apart. assumption.
  - intros [? E].
    apply not_lt_apart_lt_flip.
    + assumption.
    + apply symmetry. assumption.
  Qed.

  Global Instance: ∀ x y, Stable (x ≤ y).
  Proof.
  intros x y. unfold Stable, DN.
  intros dn. apply le_iff_not_lt_flip.
  intros E. apply dn.
  intros E';apply le_iff_not_lt_flip in E';auto.
  Qed.

  Lemma le_or_lt `{!TrivialApart A} `{DecidablePaths A} x y : x ≤ y ∨ y < x.
  Proof.
  destruct (trichotomy (<) x y) as [|[|]]; try auto.
  - left. apply lt_le;trivial.
  - left. apply eq_le;trivial.
  Qed.

  Global Instance le_total `{!TrivialApart A} `{DecidablePaths A}
    : TotalOrder (≤).
  Proof.
  split; try apply _.
  intros x y.
  destruct (le_or_lt x y); auto.
  right. apply lt_le.
  trivial.
  Qed.

  Lemma not_le_lt_flip `{!TrivialApart A} `{DecidablePaths A} x y
    : ¬y ≤ x → x < y.
  Proof.
  intros.
  destruct (le_or_lt y x); auto.
  contradiction.
  Qed.

  Existing Instance dec_from_lt_dec.

  Definition lt_dec `{!TrivialApart A} `{∀ x y, Decision (x ≤ y)}
    : ∀ x y, Decision (x < y).
  Proof.
  intros.
  destruct (decide_rel (<=) y x).
  - right;apply le_not_lt_flip;assumption.
  - left; apply not_le_lt_flip;assumption.
  Defined.
End full_pseudo_order.

Hint Extern 8 (Decision (_ < _)) => eapply @lt_dec : typeclass_instances.
(*
The following instances would be tempting, but turn out to be a bad idea.

Hint Extern 10 (PropHolds (_ ≠ _)) => eapply @le_ne : typeclass_instances.
Hint Extern 10 (PropHolds (_ ≠ _)) => eapply @le_ne_flip : typeclass_instances.

It will then loop like:

semirings.lt_0_1 → lt_ne_flip → ...
*)

Section dec_strict_setoid_order.
  Context `{StrictOrder A} `{Apart A} `{!TrivialApart A} `{DecidablePaths A}.

  Instance: IsApart A := dec_strong_setoid.

  Context `{!Trichotomy (<)}.

  Instance dec_strict_pseudo_order: PseudoOrder (<).
  Proof.
  split; try apply _.
  - intros x y [??].
    destruct (lt_antisym x y); auto.
  - intros x y Exy z.
    destruct (trichotomy (<) x z) as [? | [Exz | Exz]]; try auto.
    right. rewrite <-Exz. assumption.
  - intros x y. transitivity (~ x = y);[split;apply trivial_apart|].
    split.
    + destruct (trichotomy (<) x y) as [?|[?|?]]; auto.
      intros E;contradiction E.
    + intros [?|?];[apply lt_ne|apply lt_ne_flip];trivial.
  Qed.
End dec_strict_setoid_order.

Section dec_partial_order.
  Context `{PartialOrder A} `{DecidablePaths A}.

  Definition dec_lt: Lt A := λ x y, x ≤ y ∧ x ≠ y.

  Context `{Alt : Lt A} (lt_correct : ∀ x y, x < y ↔ x ≤ y ∧ x ≠ y).

  Instance dec_order: StrictOrder (<).
  Proof.
  split.
  - intros x E. apply lt_correct in E. destruct E as [_ []];trivial.
  - intros x y z E1 E2.
    apply lt_correct;
    apply lt_correct in E1;
    apply lt_correct in E2.
    destruct E1 as [E1a E1b],E2 as [E2a E2b].
    split.
    + transitivity y;trivial.
    + intros E3. destruct E2b.
      apply (antisymmetry (≤)); trivial.
      rewrite <-E3. assumption.
  Qed.

  Context `{Apart A} `{!TrivialApart A}.

  Instance: IsApart A := dec_strong_setoid.

  Instance dec_full_partial_order: FullPartialOrder (≤) (<).
  Proof.
  split;try apply _.
  intros. transitivity (x <= y /\ ~ x = y);[|
  split;intros [? ?];split;trivial;apply trivial_apart;trivial].
  apply lt_correct.
  Qed.

  Context `{!TotalRelation (≤)}.

  Instance: Trichotomy (<).
  Proof.
  intros x y.
  destruct (decide (x = y)); try auto.
  destruct (total (≤) x y);[left|right;right];
  apply lt_correct;auto.
  split;auto.
  intro E;apply symmetry in E;auto.
  Qed.

  Instance dec_pseudo_order: PseudoOrder (<) := dec_strict_pseudo_order.

  Instance dec_full_pseudo_order: FullPseudoOrder (≤) (<).
  Proof.
  split; try apply _.
  intros x y.
  split.
  - intros ? E. apply lt_correct in E;destruct E as [? []].
    apply (antisymmetry (≤));assumption.
  - intros E1.
    destruct (total (≤) x y); trivial.
    destruct (decide (x = y)) as [E2|E2].
    + rewrite E2. apply reflexivity.
    + destruct E1. apply lt_correct;split;auto.
      apply symmetric_neq;assumption.
  Qed.
End dec_partial_order.

Lemma lt_eq_trans `{Lt A} : forall x y z, x < y -> y = z -> x < z.
Proof.
intros ???? [];trivial.
Qed.
