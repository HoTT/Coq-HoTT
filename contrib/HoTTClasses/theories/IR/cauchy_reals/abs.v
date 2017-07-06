Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.integers
  HoTTClasses.interfaces.naturals
  HoTTClasses.interfaces.rationals
  HoTTClasses.interfaces.orders
  HoTTClasses.implementations.natpair_integers
  HoTTClasses.theory.rings
  HoTTClasses.theory.integers
  HoTTClasses.theory.dec_fields
  HoTTClasses.orders.dec_fields
  HoTTClasses.theory.rationals
  HoTTClasses.orders.lattices
  HoTTClasses.theory.additional_operations
  HoTTClasses.theory.premetric
  HoTTClasses.IR.cauchy_completion.

Require Export
  HoTTClasses.IR.cauchy_reals.base.

Local Set Universe Minimization ToSet.

Definition Rabs_val := lipschitz_extend _ (Compose rat abs) 1.

Global Instance Rabs_nonexpanding : NonExpanding Rabs_val := _.
Typeclasses Opaque Rabs_val.

Lemma Rabs_of_nonneg' : forall x, 0 <= x -> Rabs_val x = x.
Proof.
unfold le;simpl. intros x E;rewrite <-E.
clear E;revert x;apply (unique_continuous_extension _);try apply _.
intros q;apply (ap rat).
apply ((abs_sig _).2). apply join_ub_l.
Qed.

Lemma Rabs_of_nonpos' : forall x, x <= 0 -> Rabs_val x = - x.
Proof.
intros x E.
apply meet_l in E. rewrite <-E.
clear E;revert x;apply (unique_continuous_extension _);try apply _.
intros q;apply (ap rat).
apply ((abs_sig _).2). apply meet_lb_r.
Qed.

Instance Rabs : Abs real.
Proof.
intros u. exists (Rabs_val u).
split.
- apply Rabs_of_nonneg'.
- apply Rabs_of_nonpos'.
Defined.

Lemma Rabs_of_nonneg@{} : forall x : real, 0 <= x -> abs x = x.
Proof.
intros x;apply ((abs_sig x).2).
Qed.

Lemma Rabs_of_nonpos : forall x : real, x <= 0 -> abs x = - x.
Proof.
intros x;apply ((abs_sig x).2).
Qed.

Lemma Rabs_of_0 : abs (A:=real) 0 = 0.
Proof.
apply Rabs_of_nonneg;reflexivity.
Qed.

Lemma Rabs_of_0' : forall x : real, x = 0 -> abs x = 0.
Proof.
intros x E;rewrite E;apply Rabs_of_0.
Qed.

Lemma Rabs_nonneg@{} : forall x : real, 0 <= abs x.
Proof.
unfold le;simpl. apply (unique_continuous_extension _);try apply _.
intros;apply (ap rat).
apply join_r. apply Qabs_nonneg.
Qed.

Instance Rabs_idempotent@{} : UnaryIdempotent (abs (A:=real)).
Proof.
hnf. apply path_forall. intros x. unfold Compose.
apply Rabs_of_nonneg, Rabs_nonneg.
Qed.

Lemma Rabs_neg_flip@{} : forall a b : real, abs (a - b) = abs (b - a).
Proof.
apply (unique_continuous_binary_extension _);try apply _.
intros q r;change (rat (abs (q - r)) = rat (abs (r - q)));apply (ap rat).
apply Qabs_neg_flip.
Qed.

Lemma Rabs_is_join@{} : forall x : real, abs x = join (- x) x.
Proof.
eapply @unique_continuous_extension;try apply _.
{ change (Continuous (uncurry join ∘ (map2 (-) (@id real)) ∘ BinaryDup));
  apply _. }
intros;apply (ap rat),Qabs_is_join.
Qed.

Lemma Rabs_le_raw@{} : forall x : real, x <= abs x.
Proof.
intros x;rewrite Rabs_is_join. apply join_ub_r.
Qed.

Lemma Rabs_le_neg_raw@{} : forall x : real, - x <= abs x.
Proof.
intros x;rewrite Rabs_is_join. apply join_ub_l.
Qed.

Lemma Rabs_neg@{} : forall x : real, abs (- x) = abs x.
Proof.
intros;rewrite !Rabs_is_join,involutive. apply commutativity.
Qed.

Lemma Rabs_le_pr@{} : forall x y : real, abs x <= y <-> - y <= x /\ x <= y.
Proof.
intros x y.
split.
- intros E. split.
  + apply Rneg_le_flip_equiv. rewrite involutive. transitivity (abs x);trivial.
    apply Rabs_le_neg_raw.
  + transitivity (abs x);trivial.
    apply Rabs_le_raw.
- intros [E1 E2].
  rewrite Rabs_is_join. apply join_le.
  + apply Rneg_le_flip_equiv;rewrite involutive;trivial.
  + trivial.
Qed.
