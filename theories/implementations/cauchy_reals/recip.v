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
  HoTTClasses.implementations.cauchy_completion.

Require Export
  HoTTClasses.implementations.cauchy_reals.base
  HoTTClasses.implementations.cauchy_reals.abs
  HoTTClasses.implementations.cauchy_reals.order
  HoTTClasses.implementations.cauchy_reals.metric
  HoTTClasses.implementations.cauchy_reals.ring
  HoTTClasses.implementations.cauchy_reals.full_order.

Local Set Universe Minimization ToSet.

Definition Qpos_upper_recip (e:Q+) : real -> real
  := lipschitz_extend _ (rat ∘ ((/) ∘ pr1 ∘ (Qpos_upper_inject e))) _.

Instance Qpos_upper_recip_lipschitz : forall e,
  Lipschitz (Qpos_upper_recip e) _
  := _.
Typeclasses Opaque Qpos_upper_recip.

Definition pos_back : (exists e : Q+, exists x : real, rat (' e) <= x) ->
  exists x : real, 0 < x.
Proof.
intros s;exists (s.2.1).
apply R_lt_le_trans with (rat (' s.1)).
- apply rat_lt_preserving;solve_propholds.
- apply s.2.2.
Defined.

Lemma Qpos_upper_recip_respects : ∀ (x : ∃ (e : Q+) (x : real), rat (' e) ≤ x)
  (y : ∃ (e : Q+) (x0 : real), rat (' e) ≤ x0),
  pos_back x = pos_back y →
  Qpos_upper_recip x.1 (x.2).1 = Qpos_upper_recip y.1 (y.2).1.
Proof.
intros [e1 [x Ex]] [e2 [y Ey]] E.
apply (ap pr1) in E. simpl in E.
simpl.
destruct E.
pose proof (join_le _ _ _ Ex Ey) as E;clear Ex Ey.
rewrite <-E;clear E.
revert x. apply (unique_continuous_extension _ _ _).
intros q. unfold Qpos_upper_recip;simpl.
change (rat ((dec_recip ∘ pr1 ∘ Qpos_upper_inject e1) ((' e1 ⊔ ' e2) ⊔ q)) =
rat ((dec_recip ∘ pr1 ∘ Qpos_upper_inject e2) ((' e1 ⊔ ' e2) ⊔ q))).
apply (ap rat). unfold compose;simpl.
apply ap.
rewrite <-(simple_associativity (f:=join)),(commutativity (f:=join) q).
rewrite (simple_associativity (f:=join)),(commutativity (f:=join) _ (' e1)).
rewrite (simple_associativity (f:=join)),(idempotency _ _).
set (LEFT := (' e1 ⊔ ' e2) ⊔ q) at 1.
rewrite <-(simple_associativity (f:=join)),(commutativity (f:=join) q).
rewrite (simple_associativity (f:=join)).
rewrite <-(simple_associativity (f:=join) (' e1)),(idempotency join (' e2)).
reflexivity.
Qed.

Instance pos_back_issurj : IsSurjection pos_back.
Proof.
apply BuildIsSurjection. intros s.
generalize s.2. apply (Trunc_ind _).
intros [q [r [E1 [E2 E3]]]].
apply tr. simple refine (existT _ _ _).
+ simple refine (existT _ _ _).
  * exists r. apply le_lt_trans with q;trivial. apply rat_le_reflecting;trivial.
  * simpl. exists s.1. unfold cast;simpl. trivial.
+ simpl. unfold pos_back. simpl. apply Sigma.path_sigma_hprop. reflexivity.
Defined.

Definition R_pos_recip : (exists x : real, 0 < x) -> real.
Proof.
simple refine (jections.surjective_factor@{UQ UQ UQ Uhuge Ularge
    Ularge UQ UQ Uhuge Ularge} _ pos_back _).
- intros s. exact (Qpos_upper_recip s.1 s.2.1).
- simpl. exact Qpos_upper_recip_respects.
Defined.

Lemma R_pos_recip_rat : forall q (Eq : 0 < rat q),
  R_pos_recip (existT _ (rat q) Eq) = rat (/ q).
Proof.
intros q. apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
unfold R_pos_recip.
unfold jections.surjective_factor,jections.surjective_factor_aux.
change ((rat ∘ (/)) (join q s) = (rat ∘ (/)) q).
apply ap. apply join_l.
apply rat_le_reflecting;trivial.
Qed.

Instance Rrecip : Recip real.
Proof.
intros [x [E|E]].
- apply negate,R_pos_recip;exists (- x). apply flip_neg_negate. trivial.
- apply R_pos_recip;exists x;trivial.
Defined.

Lemma Rrecip_rat@{} : forall q (Eq : apart (rat q) 0),
  // (existT (fun y => apart y 0) (rat q) Eq) = rat (/ q).
Proof.
simpl;intros q [Eq|Eq];unfold recip;simpl.
- change (- rat q) with (rat (- q)). rewrite R_pos_recip_rat.
  apply (ap rat).
  rewrite dec_recip_negate@{UQ Ularge},involutive. trivial.
- apply R_pos_recip_rat.
Qed.

Lemma Rneg_strong_ext : StrongExtensionality (negate (A:=real)).
Proof.
hnf. intros x y [E|E];[right|left];apply Rneg_lt_flip,E.
Defined.

Instance Rneg_strong_injective : StrongInjective (negate (A:=real)).
Proof.
split;try apply Rneg_strong_ext.
intros x y [E|E];[right|left];apply Rneg_lt_flip;rewrite !involutive;trivial.
Defined.

Definition R_apartzero_neg : ApartZero real -> ApartZero real.
Proof.
intros x. exists (- x.1).
destruct (x.2) as [E|E];[right|left].
- apply flip_neg_negate;trivial.
- apply flip_pos_negate;trivial.
Defined.

Lemma Rrecip_neg : forall x, - // x = // (R_apartzero_neg x).
Proof.
intros [x [E|E]];unfold recip;simpl.
- apply involutive.
- apply ap. apply ap. apply Sigma.path_sigma_hprop. simpl.
  symmetry;apply involutive.
Qed.

Lemma R_recip_upper_recip : forall x e, rat (' e) <= x ->
  forall (E : apart x 0),
  // (existT (fun y => apart y 0) x E)
    = Qpos_upper_recip e x.
Proof.
intros x e E1 [E2|E2].
- destruct (irreflexivity lt x).
  transitivity 0;trivial. apply R_lt_le_trans with (rat (' e));trivial.
  apply rat_lt_preserving;solve_propholds.
- unfold recip;simpl. revert E2;apply (Trunc_ind _);intros [q [r [E2 [E3 E4]]]].
  unfold R_pos_recip,jections.surjective_factor,jections.surjective_factor_aux.
  simpl.
  transparent assert (X : (exists (e : Q+) (x : real), rat (' e) ≤ x)).
  { exists {| pos := r;
      is_pos := le_lt_trans 0 q r (rat_le_reflecting 0 q E2) E3 |}, x.
    unfold cast;simpl. trivial. }
  apply (Qpos_upper_recip_respects X (existT _ _ (existT _ _ E1))).
  unfold pos_back,X;simpl. apply Sigma.path_sigma_hprop. simpl. reflexivity.
Qed.

Instance real_nontrivial : PropHolds (apart (A:=real) 1 0).
Proof.
right. apply rat_lt_preserving;solve_propholds.
Defined.

Lemma R_pos_recip_inverse : forall x E, x // (existT _ x (inr E)) = 1 :> real.
Proof.
intros x E.
apply (merely_destruct (Rlt_exists_pos_plus_le _ _ E)). intros [e E1].
rewrite plus_0_l in E1.
rewrite (R_recip_upper_recip _ _ E1).
rewrite <-E1. clear E E1;revert x.
apply (unique_continuous_extension _).
- change (Continuous (uncurry mult ∘
    map2 (join (rat (' e))) (Qpos_upper_recip e ∘ (join (rat (' e)))) ∘
  BinaryDup)).
  repeat apply continuous_compose;apply _.
- apply _.
- intros q.
  change (rat ((' e ⊔ q) * (dec_recip ∘ pr1 ∘ Qpos_upper_inject e) (' e ⊔ q)) =
    rat 1).
  apply (ap rat).
  unfold compose;simpl.
  rewrite (commutativity (f:=join) _ (' e)),(simple_associativity (f:=join)).
  rewrite (idempotency _ _).
  apply dec_recip_inverse.
  apply lt_ne_flip.
  apply lt_le_trans with (' e).
  + solve_propholds.
  + apply join_ub_l.
Unshelve. exact 1.
Qed.

Lemma R_recip_inverse@{} : forall x, x.1 // x = 1 :> real.
Proof.
intros [x [E|E]];simpl.
- rewrite <-negate_mult_negate,Rrecip_neg. unfold R_apartzero_neg. simpl.
  apply R_pos_recip_inverse.
- apply R_pos_recip_inverse.
Qed.
