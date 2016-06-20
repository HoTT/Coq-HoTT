Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.implementations.peano_naturals
  HoTTClasses.theory.rings.
Require Export
  HoTTClasses.interfaces.naturals.

Lemma to_semiring_unique `{Naturals N} `{SemiRing SR} (f: N → SR)
  `{!SemiRing_Morphism f} x
  : f x = naturals_to_semiring N SR x.
Proof.
symmetry. apply naturals_initial.
Qed.

Lemma to_semiring_unique_alt `{Naturals N} `{SemiRing SR} (f g: N → SR)
  `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} x
  : f x = g x.
Proof.
rewrite (to_semiring_unique f), (to_semiring_unique g);reflexivity.
Qed.

Lemma to_semiring_involutive N `{Naturals N} N2 `{Naturals N2} x :
  naturals_to_semiring N2 N (naturals_to_semiring N N2 x) = x.
Proof.
change (compose (naturals_to_semiring N2 N) (naturals_to_semiring N N2) x = id x).
apply to_semiring_unique_alt;apply _.
Qed.

Lemma morphisms_involutive `{Naturals N} `{SemiRing R} (f : R → N) (g : N → R)
  `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} x : f (g x) = x.
Proof (to_semiring_unique_alt (f ∘ g) id _).

Lemma to_semiring_twice `{Naturals N} `{SemiRing R1} `{SemiRing R2}
  (f : R1 → R2) (g : N → R1) (h : N → R2)
  `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} `{!SemiRing_Morphism h} x
  : f (g x) = h x.
Proof (to_semiring_unique_alt (f ∘ g) h _).

Lemma to_semiring_self `{Naturals N} (f : N → N) `{!SemiRing_Morphism f} x
  : f x = x.
Proof (to_semiring_unique_alt f id _).

Lemma to_semiring_injective `{Naturals N} `{SemiRing A}
   (f: A → N) (g: N → A) `{!SemiRing_Morphism f} `{!SemiRing_Morphism g}
   : Injective g.
Proof.
split.
intros x y E.
change (id x = id y).
rewrite <-(to_semiring_twice f g id x), <-(to_semiring_twice f g id y).
apply ap,E.
Qed.

Instance naturals_to_naturals_injective `{Naturals N} `{Naturals N2} (f: N → N2)
  `{!SemiRing_Morphism f}
  : Injective f | 15.
Proof (to_semiring_injective (naturals_to_semiring N2 N) _).

Section retract_is_nat.
  Context `{Naturals N} `{SemiRing SR}.
  Context (f : N → SR) `{inv_f : !Inverse f} `{!Surjective f}
    `{!SemiRing_Morphism f} `{!SemiRing_Morphism (f⁻¹)}.

  (* If we make this an instance, instance resolution will loop *)
  Definition retract_is_nat_to_sr : NaturalsToSemiRing SR
    := λ R _ _ _ _ , naturals_to_semiring N R ∘ f⁻¹.

  Section for_another_semirings.
    Context `{SemiRing R}.

    Instance: SemiRing_Morphism (naturals_to_semiring N R ∘ f⁻¹) := {}.

    Context (h :  SR → R) `{!SemiRing_Morphism h}.

    Lemma same_morphism x : (naturals_to_semiring N R ∘ f⁻¹) x = h x.
    Proof.
    transitivity ((h ∘ (f ∘ f⁻¹)) x).
    - symmetry. apply (to_semiring_unique (h ∘ f)).
    - unfold compose. rewrite jections.surjective_applied;trivial.
    Qed.
  End for_another_semirings.

  (* If we make this an instance, instance resolution will loop *)
  Definition retract_is_nat : Naturals SR (U:=retract_is_nat_to_sr).
  Proof.
  split;try apply _.
  - unfold naturals_to_semiring, retract_is_nat_to_sr. apply _.
  - intros;apply same_morphism;apply _.
  Qed.
End retract_is_nat.

Section contents.
Universe U.

(* {U U} because we do forall n : N, {id} n = nat_to_sr N N n *)
Context `{Naturals@{U U} N}.

Section borrowed_from_nat.

  Lemma induction
    (P: N → Type):
    P 0 → (∀ n, P n → P (1 + n)) → ∀ n, P n.
  Proof.
  intros.
  assert (Hrw : n = naturals_to_semiring nat N
    (naturals_to_semiring N nat n)).
  - transitivity (naturals_to_semiring N N n).
    + apply symmetry. apply (naturals_initial (h:=id)).
    + eapply (naturals_initial (h := fun n => naturals_to_semiring@{U U} nat N
      (naturals_to_semiring@{U U} N nat n))).
  - rewrite Hrw.
    generalize (naturals_to_semiring N nat n). clear Hrw n.
    apply nat_induction.
    + rewrite preserves_0. trivial.
    + intros n. rewrite preserves_plus, preserves_1. auto.
  Unshelve.
  all:trivial.
  apply compose_sr_morphism;apply _.
  Qed.

  Global Instance: Biinduction N.
  Proof.
  hnf. intros P E0 ES.
  apply induction;trivial.
  apply ES.
  Qed.

  Lemma from_nat_stmt:
    ∀ (s: Statement varieties.semirings.theory)
      (w : Vars varieties.semirings.theory (varieties.semirings.object N) nat),
     (∀ v: Vars varieties.semirings.theory (varieties.semirings.object nat) nat,
       eval_stmt varieties.semirings.theory v s) →
       eval_stmt varieties.semirings.theory w s.
  Proof.
   pose proof (@naturals_initial nat _ _ _ _ _ _ _) as AI.
   pose proof (@naturals_initial N _ _ _ _ _ _ _) as BI.
   intros s w ?.
   apply (transfer_statement _ (@categories.initials_unique'
                                      semirings.Object _ _ _ _ _
     (semirings.object nat) (semirings.object N) _ AI _ BI)).
   intuition.
  Qed.

  Let three_vars (x y z : N) (_: unit) v
    := match v with 0%nat => x | 1%nat => y | _ => z end.
  Let two_vars (x y : N) (_: unit) v := match v with 0%nat => x | _ => y end.
  Let no_vars (_: unit) (v: nat) := 0:N.

  Local Notation x' := (Var varieties.semirings.sig _ 0 tt).
  Local Notation y' := (Var varieties.semirings.sig _ 1 tt).
  Local Notation z' := (Var varieties.semirings.sig _ 2%nat tt).

  (* Some clever autoquoting tactic might make what follows even more automatic. *)
  (* The ugly [pose proof ... . apply that_thing.]'s are because of
     Coq bug 2185. *)

  Global Instance: ∀ z : N, LeftCancellation (+) z.
  Proof.
    intros x y z.
    rapply (from_nat_stmt (x' + y' === x' + z' -=> y' === z') (three_vars x y z)).
    intro. simpl. apply Plus.plus_reg_l.
  Qed.

  Global Instance: ∀ z : N, RightCancellation (+) z.
  Proof. intro. apply (right_cancel_from_left (+)). Qed.

  Global Instance: ∀ z : N, PropHolds (z ≠ 0) → LeftCancellation (.*.) z.
  Proof.
    intros z E x y.
    rapply (from_nat_stmt ((z' === 0 -=> Ext _ False) -=>
      z' * x' === z' * y' -=> x' === y') (three_vars x y z)).
    intro. simpl. intros. now apply (left_cancellation_ne_0 (.*.) (v () 2)). easy.
  Qed.

  Global Instance: ∀ z : N, PropHolds (z ≠ 0) → RightCancellation (.*.) z.
  Proof. intros ? ?. apply (right_cancel_from_left (.*.)). Qed.

  Instance nat_nontrivial: PropHolds ((1:N) ≠ 0).
  Proof.
    now rapply (from_nat_stmt (1 === 0 -=> Ext _ False) no_vars).
  Qed.

  Instance nat_nontrivial_apart `{Apart N} `{!TrivialApart N} :
    PropHolds ((1:N) ≶ 0).
  Proof. apply strong_setoids.ne_apart. solve_propholds. Qed.

  Lemma zero_sum (x y : N) : x + y = 0 → x = 0 ∧ y = 0.
  Proof.
    rapply (from_nat_stmt (x' + y' === 0 -=> Conj _ (x' === 0) (y' === 0))
      (two_vars x y)).
    intro. simpl. apply Plus.plus_is_O.
  Qed.

  Lemma one_sum (x y : N) : x + y = 1 → (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1).
  Proof.
   rapply (from_nat_stmt (x' + y' === 1 -=> Disj _ (Conj _ (x' === 1) (y' === 0))
    (Conj _ (x' === 0) (y' === 1))) (two_vars x y)).
   intros. simpl. intros. edestruct Plus.plus_is_one; eauto.
  Qed.

  Global Instance: ZeroProduct N.
  Proof.
    intros x y.
    rapply (from_nat_stmt (x' * y' === 0 -=>Disj _ (x' === 0) (y' === 0))
      (two_vars x y)).
    intros ? E. destruct (Mult.mult_is_O _ _ E); red; intuition.
  Qed.
End borrowed_from_nat.

Lemma nat_1_plus_ne_0 x : 1 + x ≠ 0.
Proof. intro E. destruct (zero_sum 1 x E). now apply nat_nontrivial. Qed.

Global Program Instance: ∀ x y: N, Decision (x = y) | 10 := λ x y,
  match decide (naturals_to_semiring _ nat x = naturals_to_semiring _ nat y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation. now rewrite <-(to_semiring_involutive _ nat x),
  <-(to_semiring_involutive _ nat y), E. Qed.

Section with_a_ring.
  Context `{Ring R} `{!SemiRing_Morphism (f : N → R)} `{!Injective f}.

  Lemma to_ring_zero_sum x y :
    -f x = f y → x = 0 ∧ y = 0.
  Proof.
    intros E. apply zero_sum, (injective f).
    rewrite rings.preserves_0, rings.preserves_plus, <-E.
    now apply plus_negate_r.
  Qed.

  Lemma negate_to_ring x y :
    -f x = f y → f x = f y.
  Proof.
    intros E. destruct (to_ring_zero_sum x y E) as [E2 E3].
    now rewrite E2, E3.
  Qed.
End with_a_ring.
End contents.

(* Due to bug #2528 *)
Hint Extern 6 (PropHolds (1 ≠ 0)) =>
  eapply @nat_nontrivial : typeclass_instances.
Hint Extern 6 (PropHolds (1 ≶ 0)) =>
  eapply @nat_nontrivial_apart : typeclass_instances.
