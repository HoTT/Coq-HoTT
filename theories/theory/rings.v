Require
  HoTTClasses.theory.groups
  HoTTClasses.theory.apartness.
Require Import
  HoTTClasses.interfaces.abstract_algebra.

Definition is_ne_0 `(x : R) `{Zero R} `{p : PropHolds (x ≠ 0)}
  : x ≠ 0 := p.
Definition is_nonneg `(x : R) `{Le R} `{Zero R} `{p : PropHolds (0 ≤ x)}
  : 0 ≤ x := p.
Definition is_pos `(x : R) `{Lt R} `{Zero R} `{p : PropHolds (0 < x)}
  : 0 < x := p.

(* Lemma stdlib_semiring_theory R `{SemiRing R}
  : Ring_theory.semi_ring_theory 0 1 (+) (.*.) (=).
Proof.
Qed.
*)

(* We cannot apply [left_cancellation (.*.) z] directly in case we have
  no [PropHolds (0 ≠ z)] instance in the context. *)
Section cancellation.
  Context `(op : A → A → A) `{!Zero A}.

  Lemma left_cancellation_ne_0
    `{∀ z, PropHolds (z ≠ 0) → LeftCancellation op z} z
    : z ≠ 0 → LeftCancellation op z.
  Proof. auto. Qed.

  Lemma right_cancellation_ne_0
    `{∀ z, PropHolds (z ≠ 0) → RightCancellation op z} z
    : z ≠ 0 → RightCancellation op z.
  Proof. auto. Qed.

  Lemma right_cancel_from_left `{!Commutative op} `{!LeftCancellation op z}
    : RightCancellation op z.
  Proof.
  intros x y E.
  apply (left_cancellation op z).
  rewrite 2!(commutativity (f:=op) z _).
  assumption.
  Qed.
End cancellation.

Section strong_cancellation.
  Context `{IsApart A} (op : A → A → A).

  Lemma strong_right_cancel_from_left `{!Commutative op} 
    `{!StrongLeftCancellation op z}
    : StrongRightCancellation op z.
  Proof.
  intros x y E.
  rewrite 2!(commutativity _ z).
  apply (strong_left_cancellation op z);trivial.
  Qed.

  Global Instance strong_left_cancellation_cancel `{!StrongLeftCancellation op z}
    : LeftCancellation op z | 20.
  Proof.
  intros x y E1.
  apply tight_apart in E1;apply tight_apart;intros E2.
  apply E1. apply (strong_left_cancellation op);trivial.
  Qed.

  Global Instance strong_right_cancellation_cancel `{!StrongRightCancellation op z}
    : RightCancellation op z | 20.
  Proof.
  intros x y E1.
  apply tight_apart in E1;apply tight_apart;intros E2.
  apply E1. apply (strong_right_cancellation op);trivial.
  Qed.
End strong_cancellation.

Section semiring_props.
  Context `{SemiRing R}.
(*   Add Ring SR : (stdlib_semiring_theory R). *)

  Instance mult_ne_0 `{!NoZeroDivisors R} x y
    : PropHolds (x ≠ 0) → PropHolds (y ≠ 0) → PropHolds (x * y ≠ 0).
  Proof.
  intros Ex Ey Exy.
  unfold PropHolds in *.
  apply (no_zero_divisors x); split; eauto.
  Qed.

  Global Instance plus_0_r: RightIdentity (+) 0 := right_identity.
  Global Instance plus_0_l: LeftIdentity (+) 0 := left_identity.
  Global Instance mult_1_l: LeftIdentity (.*.) 1 := left_identity.
  Global Instance mult_1_r: RightIdentity (.*.) 1 := right_identity.

  Global Instance plus_assoc: Associative (+) := simple_associativity.
  Global Instance mult_assoc: Associative (.*.) := simple_associativity.

  Global Instance plus_comm: Commutative (+) := commutativity.
  Global Instance mult_comm: Commutative (.*.) := commutativity.

  Global Instance mult_0_l: LeftAbsorb (.*.) 0 := left_absorb.

  Global Instance mult_0_r: RightAbsorb (.*.) 0.
  Proof.
  intro. path_via (0 * x).
  - apply mult_comm.
  - apply left_absorb.
  Qed.

  Global Instance plus_mult_distr_r : RightDistribute (.*.) (+).
  Proof.
  intros x y z.
  etransitivity;[|etransitivity].
  - apply mult_comm.
  - apply distribute_l.
  - apply ap2;apply mult_comm.
  Qed.

  Lemma plus_mult_distr_l : LeftDistribute (.*.) (+).
  Proof.
  apply _.
  Qed.

  Global Instance: ∀ r : R, @Monoid_Morphism R R (0:R) (0:R) (+) (+) (r *.).
  Proof.
  repeat (constructor; try apply _).
  - apply distribute_l.
  - apply right_absorb.
  Qed.
End semiring_props.

(* Due to bug #2528 *)
Hint Extern 3 (PropHolds (_ * _ ≠ 0)) => eapply @mult_ne_0 : typeclass_instances.

Section semiringmor_props.
  Context `{SemiRing_Morphism A B f}.

  Lemma preserves_0: f 0 = 0.
  Proof (preserves_mon_unit (f:=f)).
  Lemma preserves_1: f 1 = 1.
  Proof (preserves_mon_unit (f:=f)).
  Lemma preserves_mult: ∀ x y, f (x * y) = f x * f y.
  Proof.
  intros. apply preserves_sg_op.
  Qed.
  Lemma preserves_plus: ∀ x y, f (x + y) = f x + f y.
  Proof.
  intros. apply preserves_sg_op.
  Qed.

  Instance: SemiRing B := semiringmor_b.

  Lemma preserves_2: f 2 = 2.
  Proof.
  rewrite preserves_plus. rewrite preserves_1. reflexivity.
  Qed.

  Lemma preserves_3: f 3 = 3.
  Proof.
  rewrite ?preserves_plus, ?preserves_1.
  reflexivity.
  Qed.

  Lemma preserves_4: f 4 = 4.
  Proof.
  rewrite ?preserves_plus, ?preserves_1.
  reflexivity.
  Qed.

  Context `{!Injective f}.
  Instance injective_ne_0 x : PropHolds (x ≠ 0) → PropHolds (f x ≠ 0).
  Proof.
  intros. rewrite <-preserves_0. apply (jections.injective_ne f).
  assumption.
  Qed.

  Lemma injective_ne_1 x : x ≠ 1 → f x ≠ 1.
  Proof.
  intros. rewrite <-preserves_1.
  apply (jections.injective_ne f).
  assumption.
  Qed.
End semiringmor_props.

(* Due to bug #2528 *)
Hint Extern 12 (PropHolds (_ _ ≠ 0)) =>
  eapply @injective_ne_0 : typeclass_instances.

(* Lemma stdlib_ring_theory R `{Ring R} :
  Ring_theory.ring_theory 0 1 (+) (.*.) (λ x y, x - y) (-) (=).
Proof.
Qed.
*)

Section ring_props.
  Context `{Ring R}.

(*   Add Ring R: (stdlib_ring_theory R). *)

  Instance: LeftAbsorb (.*.) 0.
  Proof.
  intro.
  rewrite (commutativity (f:=(.*.)) 0).
  apply (left_cancellation (+) (y * 0)).
  path_via (y * 0);[|apply symmetry, right_identity].
  path_via (y * (0 + 0)).
  - apply symmetry,distribute_l.
  - apply ap. apply right_identity.
  Qed.

  Global Instance Ring_Semi: SemiRing R.
  Proof.
  repeat (constructor; try apply _).
  Qed.

  Definition negate_involutive x : - - x = x := groups.negate_involutive x.
  (* alias for convenience *)

  Lemma plus_negate_r : forall x, x + -x = 0.
  Proof right_inverse.
  Lemma plus_negate_l : forall x, -x + x = 0.
  Proof left_inverse.

  Lemma negate_swap_r : forall x y, x - y = -(y - x).
  Proof.
  intros.
  rewrite groups.negate_sg_op.
  rewrite involutive.
  reflexivity.
  Qed.

  Lemma negate_swap_l x y : -x + y = -(x - y).
  Proof.
  rewrite groups.negate_sg_op_distr,involutive.
  reflexivity.
  Qed.

  Lemma negate_plus_distr : forall x y, -(x + y) = -x + -y.
  Proof groups.negate_sg_op_distr.

  Lemma negate_mult x : -x = - 1 * x.
  Proof.
  apply (left_cancellation (+) x).
  path_via 0.
  - apply right_inverse.
  - path_via (1 * x + (- 1) * x).
    + apply symmetry.
      rewrite <-distribute_r. rewrite right_inverse.
      apply left_absorb.
    + apply ap2;try reflexivity.
      apply left_identity.
  Qed.

  Lemma negate_mult_distr_l x y : -(x * y) = -x * y.
  Proof.
  rewrite negate_mult,(negate_mult x).
  apply associativity.
  Qed.

  Lemma negate_mult_distr_r x y : -(x * y) = x * -y.
  Proof.
  rewrite negate_mult,(negate_mult y).
  rewrite simple_associativity,(commutativity (- 1)).
  apply symmetry,associativity.
  Qed.

  Lemma negate_mult_negate x y : -x * -y = x * y.
  Proof.
  rewrite <-negate_mult_distr_l, <-negate_mult_distr_r.
  apply involutive.
  Qed.

  Lemma negate_0: -0 = 0.
  Proof groups.negate_mon_unit.

  Global Instance minus_0_r: RightIdentity (λ x y, x - y) 0.
  Proof.
  intro x; rewrite negate_0; apply plus_0_r.
  Qed.

  Lemma equal_by_zero_sum x y : x - y = 0 ↔ x = y.
  Proof.
  split; intros E.
  - rewrite <- (plus_0_l y). rewrite <- E.
    rewrite <-simple_associativity.
    rewrite left_inverse.
    apply symmetry,right_identity.
  - rewrite E. apply right_inverse.
  Qed.

  Lemma flip_negate x y : -x = y ↔ x = -y.
  Proof.
  split; intros E.
  - rewrite <-E, involutive. trivial.
  - rewrite E, involutive. trivial.
  Qed.

  Lemma flip_negate_0 x : -x = 0 ↔ x = 0.
  Proof.
  etransitivity.
  - apply flip_negate.
  - rewrite negate_0.
    apply reflexivity.
  Qed.

  Lemma flip_negate_ne_0 x : -x ≠ 0 ↔ x ≠ 0.
  Proof.
  split; intros E ?; apply E; apply flip_negate_0;trivial.
  path_via x. apply involutive.
  Qed.

  Lemma negate_zero_prod_l x y : -x * y = 0 ↔ x * y = 0.
  Proof.
  split; intros E.
  - apply (injective (-)). rewrite negate_mult_distr_l, negate_0. trivial.
  - apply (injective (-)).
    rewrite negate_mult_distr_l, negate_involutive, negate_0.
    trivial.
  Qed.

  Lemma negate_zero_prod_r x y : x * -y = 0 ↔ x * y = 0.
  Proof.
  rewrite (commutativity (f:=(.*.)) x (-y)), (commutativity (f:=(.*.)) x y).
  apply negate_zero_prod_l.
  Qed.

  Lemma unit_no_zero_divisor (x : R) {unit : RingUnit x}: ¬ZeroDivisor x.
  Proof.
  destruct unit as [y x_y_unit].
  intros [_ [z [z_nonzero xz_zero]]].
  apply z_nonzero.
  rewrite <-(mult_1_l z), <-x_y_unit, <-simple_associativity,
    (commutativity (f:=mult) y), simple_associativity, xz_zero.
  apply mult_0_l.
  Qed.

  Context `{!NoZeroDivisors R} `{∀ x y:R, Stable (x = y)}.

  Global Instance mult_left_cancel:  ∀ z, PropHolds (z ≠ 0) →
    LeftCancellation (.*.) z.
  Proof.
  intros z z_nonzero x y E.
  apply stable.
  intro U.
  apply (mult_ne_0 z (x - y) (is_ne_0 z)).
  - intro. apply U. apply equal_by_zero_sum. trivial.
  - rewrite distribute_l, E.
    rewrite <-simple_distribute_l,right_inverse.
    apply mult_0_r.
  Qed.

  Global Instance mult_right_cancel: ∀ z, PropHolds (z ≠ 0) →
    RightCancellation (.*.) z.
  Proof.
  intros ? ?.
  apply (right_cancel_from_left (.*.)).
  Qed.

  Lemma plus_conjugate x y : x = y + x - y.
  Proof.
  rewrite plus_comm, plus_assoc, plus_negate_l, plus_0_l.
  reflexivity.
  Qed.

  Lemma plus_conjugate_alt x y : x = y + (x - y).
  Proof.
  rewrite plus_comm, <-plus_assoc, plus_negate_l, plus_0_r.
  reflexivity.
  Qed.
End ring_props.

Section integral_domain_props.
  Context `{IntegralDomain R}.

  Instance intdom_nontrivial_apart `{Apart R} `{!TrivialApart R} :
    PropHolds (1 ≶ 0).
  Proof.
  apply apartness.ne_apart. solve_propholds.
  Qed.
End integral_domain_props.

(* Due to bug #2528 *)
Hint Extern 6 (PropHolds (1 ≶ 0)) =>
  eapply @intdom_nontrivial_apart : typeclass_instances.

Section ringmor_props.
  Context `{Ring A} `{Ring B} `{!SemiRing_Morphism (f : A → B)}.

  Definition preserves_negate x : f (-x) = -f x := groups.preserves_negate x.
  (* alias for convenience *)

  Lemma preserves_minus x y : f (x - y) = f x - f y.
  Proof.
  rewrite <-preserves_negate.
  apply preserves_plus.
  Qed.

  Lemma injective_preserves_0 : (∀ x, f x = 0 → x = 0) → Injective f.
  Proof.
  intros E1.
  split; try apply _.
  intros x y E.
  apply equal_by_zero_sum.
  apply E1.
  rewrite preserves_minus, E.
  apply plus_negate_r.
  Qed.
End ringmor_props.

Section from_another_ring.
  Context `{Ring A} `{IsHSet B}
   `{Bplus : Plus B} `{Zero B} `{Bmult : Mult B} `{One B} `{Bnegate : Negate B}
    (f : B → A) `{!Injective f}
    (plus_correct : ∀ x y, f (x + y) = f x + f y) (zero_correct : f 0 = 0)
    (mult_correct : ∀ x y, f (x * y) = f x * f y) (one_correct : f 1 = 1)
    (negate_correct : ∀ x, f (-x) = -f x).

  Lemma projected_ring: Ring B.
  Proof.
  split.
  - apply (groups.projected_ab_group f);assumption.
  - apply (groups.projected_com_monoid f mult_correct one_correct);assumption.
  - repeat intro; apply (injective f).
    rewrite plus_correct, !mult_correct, plus_correct.
    apply distribute_l.
  Qed.
End from_another_ring.

(* Section from_stdlib_semiring_theory.
  Context
    `(H: @semi_ring_theory R Rzero Rone Rplus Rmult Re)
    `{!@Setoid R Re}
    `{!Proper (Re ==> Re ==> Re) Rplus}
    `{!Proper (Re ==> Re ==> Re) Rmult}.

  Add Ring R2: H.

  Definition from_stdlib_semiring_theory: @SemiRing R Re Rplus Rmult Rzero Rone.
  Proof.
   repeat (constructor; try assumption); repeat intro
   ; unfold equiv, mon_unit, sg_op, zero_is_mon_unit, plus_is_sg_op,
     one_is_mon_unit, mult_is_sg_op, zero, mult, plus; ring.
  Qed.
End from_stdlib_semiring_theory.

Section from_stdlib_ring_theory.
  Context
    `(H: @ring_theory R Rzero Rone Rplus Rmult Rminus Rnegate Re)
    `{!@Setoid R Re}
    `{!Proper (Re ==> Re ==> Re) Rplus}
    `{!Proper (Re ==> Re ==> Re) Rmult}
    `{!Proper (Re ==> Re) Rnegate}.

  Add Ring R3: H.

  Definition from_stdlib_ring_theory: @Ring R Re Rplus Rmult Rzero Rone Rnegate.
  Proof.
   repeat (constructor; try assumption); repeat intro
   ; unfold equiv, mon_unit, sg_op, zero_is_mon_unit, plus_is_sg_op,
     one_is_mon_unit, mult_is_sg_op, mult, plus, negate; ring.
  Qed.
End from_stdlib_ring_theory. *)

Instance id_sr_morphism `{SemiRing A}: SemiRing_Morphism (@id A) := {}.

Section morphism_composition.
  Context `{Mult A} `{Plus A} `{One A} `{Zero A}
    `{Mult B} `{Plus B} `{One B} `{Zero B}
    `{Mult C} `{Plus C} `{One C} `{Zero C}
    (f : A → B) (g : B → C).

  Instance compose_sr_morphism:
    SemiRing_Morphism f → SemiRing_Morphism g → SemiRing_Morphism (g ∘ f).
  Proof.
  split; try apply _.
  - apply semiringmor_a.
  - apply semiringmor_b.
  Qed.

  Instance invert_sr_morphism:
    ∀ `{!Inverse f}, Bijective f → SemiRing_Morphism f → SemiRing_Morphism (f⁻¹).
  Proof.
  split; try apply _.
  - apply semiringmor_b.
  - apply semiringmor_a.
  Qed.
End morphism_composition.

Hint Extern 4 (SemiRing_Morphism (_ ∘ _)) =>
  class_apply @compose_sr_morphism : typeclass_instances.
Hint Extern 4 (SemiRing_Morphism (_⁻¹)) =>
  class_apply @invert_sr_morphism : typeclass_instances.
