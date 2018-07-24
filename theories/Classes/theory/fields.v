Require Import Basics.Trunc.
Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.theory.apartness.
Require Export
  HoTT.Classes.theory.rings.

Section field_properties.
Context `{Field F}.

(* Add Ring F : (stdlib_ring_theory F). *)

Lemma reciperse_alt (x : F) Px : x // (x;Px) = 1.
Proof.
rewrite <-(recip_inverse (x;Px)). trivial.
Qed.

Lemma recip_proper_alt x y Px Py : x = y -> // (x;Px) = // (y;Py).
Proof.
intro E. apply ap.
apply Sigma.path_sigma with E.
apply path_ishprop.
Qed.

Lemma recip_irrelevant x Px1 Px2 : // (x;Px1) = // (x;Px2).
Proof.
apply recip_proper_alt. reflexivity.
Qed.

Lemma apart_0_proper {x y} : x ≶ 0 -> x = y -> y ≶ 0.
Proof.
intros ? E. rewrite <-E. trivial.
Qed.

Global Instance: StrongInjective (-).
Proof.
repeat (split; try apply _); intros x y E.
- apply (strong_extensionality (+ x + y)).
  rewrite simple_associativity, left_inverse, plus_0_l.
  rewrite (commutativity (f:=plus) x y), simple_associativity,
    left_inverse, plus_0_l.
  apply symmetry;trivial.
- apply (strong_extensionality (+ -x + -y)).
  rewrite simple_associativity, right_inverse, plus_0_l.
  rewrite (commutativity (f:=plus) (- x) (- y)),
    simple_associativity, right_inverse, plus_0_l.
  apply symmetry;trivial.
Qed.

Global Instance: StrongInjective (//).
Proof.
repeat (split; try apply _); intros x y E.
- apply (strong_extensionality (x.1 *.)).
  rewrite recip_inverse, (commutativity (f:=mult)).
  apply (strong_extensionality (y.1 *.)).
  rewrite simple_associativity, recip_inverse.
  rewrite mult_1_l,mult_1_r. apply symmetry;trivial.
- apply (strong_extensionality (.* // x)).
  rewrite recip_inverse, (commutativity (f:=mult)).
  apply (strong_extensionality (.* // y)).
  rewrite <-simple_associativity, recip_inverse.
  rewrite mult_1_l,mult_1_r. apply symmetry;trivial.
Qed.

Global Instance: forall z, StrongLeftCancellation (+) z.
Proof.
intros z x y E. apply (strong_extensionality (+ -z)).
do 2 rewrite (commutativity (f:=plus) z _),
  <-simple_associativity,right_inverse,plus_0_r.
trivial.
Qed.

Global Instance: forall z, StrongRightCancellation (+) z.
Proof.
intros. apply (strong_right_cancel_from_left (+)).
Qed.

Global Instance: forall z, PropHolds (z ≶ 0) -> StrongLeftCancellation (.*.) z.
Proof.
intros z Ez x y E. red in Ez.
rewrite !(commutativity z).
apply (strong_extensionality (.* // (z;(Ez : (≶0) z)))).
rewrite <-!simple_associativity, !reciperse_alt.
rewrite !mult_1_r;trivial.
Qed.

Global Instance: forall z, PropHolds (z ≶ 0) -> StrongRightCancellation (.*.) z.
Proof.
intros. apply (strong_right_cancel_from_left (.*.)).
Qed.

Lemma mult_apart_zero_l x y : x * y ≶ 0 -> x ≶ 0.
Proof.
intros. apply (strong_extensionality (.* y)).
rewrite mult_0_l. trivial.
Qed.

Lemma mult_apart_zero_r x y : x * y ≶ 0 -> y ≶ 0.
Proof.
intros. apply (strong_extensionality (x *.)).
rewrite mult_0_r. trivial.
Qed.

Instance mult_apart_zero x y :
  PropHolds (x ≶ 0) -> PropHolds (y ≶ 0) -> PropHolds (x * y ≶ 0).
Proof.
intros Ex Ey.
apply (strong_extensionality (.* // (y;(Ey : (≶0) y)))).
rewrite <-simple_associativity, reciperse_alt, mult_1_r, mult_0_l.
trivial.
Qed.

Instance: NoZeroDivisors F.
Proof.
intros x [x_nonzero [y [y_nonzero E]]].
assert (~ ~ apart y 0) as Ey.
- intros E';apply y_nonzero,tight_apart,E'.
- apply Ey. intro y_apartzero.
  apply x_nonzero.
  rewrite <- (mult_1_r x). rewrite <- (reciperse_alt y y_apartzero).
  rewrite simple_associativity, E.
  apply mult_0_l.
Qed.

Global Instance: IntegralDomain F := {}.

Global Instance apart_0_sig_apart_0: forall (x : ApartZero F), PropHolds (x.1 ≶ 0).
Proof.
intros [??];trivial.
Qed.

Instance recip_apart_zero x : PropHolds (// x ≶ 0).
Proof.
red.
apply mult_apart_zero_r with (x.1).
rewrite recip_inverse. solve_propholds.
Qed.

Lemma field_div_0_l x y : x = 0 -> x // y = 0.
Proof.
intros E. rewrite E. apply left_absorb.
Qed.

Lemma field_div_diag x y : x = y.1 -> x // y = 1.
Proof.
intros E. rewrite E. apply recip_inverse.
Qed.

Lemma equal_quotients (a c: F) b d : a * d.1 = c * b.1 <-> a // b = c // d.
Proof.
split; intro E.
- rewrite <-(mult_1_l (a // b)),
  <- (recip_inverse d),
  (commutativity (f:=mult) d.1 (// d)),
  <-simple_associativity,
  (simple_associativity d.1),
  (commutativity (f:=mult) d.1 a),
  E,
  <-simple_associativity,
  simple_associativity,
  recip_inverse,
  mult_1_r.
  apply commutativity.
- rewrite <-(mult_1_r (a * d.1)),
  <- (recip_inverse b),
  <-simple_associativity,
  (commutativity (f:=mult) b.1 (// b)),
  (simple_associativity d.1),
  (commutativity (f:=mult) d.1),
  !simple_associativity,
  E,
  <-(simple_associativity c),
  (commutativity (f:=mult) (// d)),
  recip_inverse,
  mult_1_r.
  reflexivity.
Qed.

Lemma recip_distr_alt (x y : F) Px Py Pxy :
  // (x * y ; Pxy) = // (x;Px) * // (y;Py).
Proof.
apply (left_cancellation_ne_0 (.*.) (x * y)).
- apply apart_ne;trivial.
- transitivity ((x // (x;Px)) *  (y // (y;Py))).
  + rewrite 3!reciperse_alt,mult_1_r. reflexivity.
  + rewrite <-simple_associativity,<-simple_associativity.
    apply ap.
    rewrite simple_associativity.
    rewrite (commutativity (f:=mult) _ y).
    rewrite <-simple_associativity.
    reflexivity.
Qed.
End field_properties.

(* Due to bug #2528 *)
Hint Extern 8 (PropHolds (// _ ≶ 0)) =>
  eapply @recip_apart_zero : typeclass_instances.
Hint Extern 8 (PropHolds (_ * _ ≶ 0)) =>
  eapply @mult_apart_zero : typeclass_instances.

Section morphisms.
  Context `{Field F1} `{Field F2} `{!SemiRingStrongPreserving (f : F1 -> F2)}.

(*   Add Ring F1 : (stdlib_ring_theory F1). *)

  Lemma strong_injective_preserves_0 : (forall x, x ≶ 0 -> f x ≶ 0) -> StrongInjective f.
  Proof.
  intros E1. split; try apply _. intros x y E2.
  apply (strong_extensionality (+ -f y)).
  rewrite plus_negate_r, <-preserves_minus.
  apply E1.
  apply (strong_extensionality (+ y)).
  rewrite <-simple_associativity,left_inverse,plus_0_l,plus_0_r.
  trivial.
  Qed.

  (* We have the following for morphisms to non-trivial strong rings as well.
    However, since we do not have an interface for strong rings, we ignore it. *)
  Global Instance: StrongInjective f.
  Proof.
  apply strong_injective_preserves_0.
  intros x Ex.
  apply mult_apart_zero_l with (f (// exist (≶0) x Ex)).
  rewrite <-rings.preserves_mult.
  rewrite reciperse_alt.
  rewrite (rings.preserves_1 (f:=f)).
  solve_propholds.
  Qed.

  Lemma preserves_recip x Px Pfx : f (// (x;Px)) = // (f x;Pfx).
  Proof.
  apply (left_cancellation_ne_0 (.*.) (f x)).
  - apply apart_ne;trivial.
  - rewrite <-rings.preserves_mult.
    rewrite !reciperse_alt.
    apply preserves_1.
  Qed.
End morphisms.
