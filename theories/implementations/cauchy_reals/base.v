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

Local Set Universe Minimization ToSet.

Definition real := C Q.
Definition rat : Q -> real := eta.

Instance R0@{} : Zero real := rat 0.

Instance R1@{} : One real := rat 1.

Instance Rneg@{} : Negate real.
Proof.
red. apply (lipschitz_extend _ (compose rat (-)) _).
Defined.

Instance Rneg_nonexpanding@{} : NonExpanding (@negate real _).
Proof.
apply _.
Qed.

Lemma Rneg_involutive@{} : forall x : real, - - x = x.
Proof.
change (forall x, - - x = id x).
apply (unique_continuous_extension _);try apply _.
intros;apply (ap rat). apply involutive.
Qed.

Global Instance Rplus@{} : Plus real
  := lipschitz_extend_binary _ _ (fun q r => eta (q + r)) 1 1.

Definition Rplus_rat_rat@{} q r : rat q + rat r = rat (q + r)
  := idpath.

Global Instance Rplus_nonexpanding_l@{} : forall s : real, NonExpanding (+ s)
  := fun _ => lipschitz_nonexpanding _.
Global Instance Rplus_nonexpanding_r@{} : forall s : real, NonExpanding (s +)
  := fun _ => lipschitz_nonexpanding _.

Typeclasses Opaque Rplus.

Lemma unique_continuous_binary_extension@{} (f : real -> real -> real)
  `{!Continuous (uncurry f)}
  (g : real -> real -> real)
  `{!Continuous (uncurry g)}
  : (forall q r, f (rat q) (rat r) = g (rat q) (rat r)) ->
  forall u v, f u v = g u v.
Proof.
intros E.
intros x;apply (unique_continuous_extension _).
{ change (Continuous (compose (uncurry f) (pair x))). apply _. }
{ change (Continuous (compose (uncurry g) (pair x))). apply _. }
intros r;revert x;apply (unique_continuous_extension _).
{ change (Continuous (compose (uncurry f) (fun x => (x, rat r)))). apply _. }
{ change (Continuous (compose (uncurry g) (fun x => (x, rat r)))). apply _. }
trivial.
Qed.

Lemma unique_continuous_ternary_extension@{} (f : real -> real -> real -> real)
  `{!Continuous (uncurry (uncurry f))}
  (g : real -> real -> real -> real)
  `{!Continuous (uncurry (uncurry g))}
  : (forall q r s, f (rat q) (rat r) (rat s) = g (rat q) (rat r) (rat s)) ->
  forall u v w, f u v w = g u v w.
Proof.
intros E u;apply unique_continuous_binary_extension.
{ change (Continuous (compose (uncurry (uncurry f)) (map2 (pair u) id))).
  apply _. }
{ change (Continuous (compose (uncurry (uncurry g)) (map2 (pair u) id))).
  apply _. }
intros q r;revert u;apply (unique_continuous_extension _).
{ change (Continuous (compose (uncurry (uncurry f))
    (compose (fun u => (u, rat r)) (fun u => (u, rat q))))).
  apply _. }
{ change (Continuous (compose (uncurry (uncurry g))
    (compose (fun u => (u, rat r)) (fun u => (u, rat q))))).
  apply _. }
auto.
Qed.

Notation prod_symm := (Prod.equiv_prod_symm _ _).
Notation prod_assoc := (Prod.equiv_prod_assoc _ _ _).

Instance Rplus_comm@{} : Commutative (@plus _ Rplus).
Proof.
hnf. apply unique_continuous_binary_extension.
{ apply _. }
{ apply _. }
intros q r;apply (ap rat),plus_comm.
Qed.

Lemma Rplus_assoc@{} : Associative (@plus _ Rplus).
Proof.
hnf. apply unique_continuous_ternary_extension.
{ change (Continuous (uncurry plus ∘ map2 id (uncurry plus) ∘
    ((Prod.equiv_prod_assoc _ real _)^-1))).
  apply _. }
{ change (Continuous (uncurry plus ∘ map2 (uncurry plus) (@id real))).
  apply _. }
intros;change (rat (q + (r + s)) = rat (q + r + s));apply (ap rat),plus_assoc.
Qed.

Instance Rplus_group@{} : Group real.
Proof.
repeat split.
- apply _.
- exact Rplus_assoc.
- hnf. change mon_unit with 0.
  change sg_op with plus.
  apply (unique_continuous_extension _);try apply _.
  intros;apply (ap rat);apply plus_0_l.
- hnf. change mon_unit with 0.
  change sg_op with plus.
  apply (unique_continuous_extension _);try apply _.
  intros;apply (ap rat);apply plus_0_r.
- hnf; change mon_unit with 0.
  change sg_op with plus.
  apply (unique_continuous_extension _);try apply _.
  { change (Continuous (compose (uncurry plus)
     (compose (map2 negate (@id real)) BinaryDup))). apply _.
  }
  intros;apply (ap rat),plus_negate_l.
- hnf; change mon_unit with 0.
  change sg_op with plus.
  apply (unique_continuous_extension _);try apply _.
  { change (Continuous (compose (uncurry plus)
     (compose (map2 (@id real) negate) BinaryDup)));apply _. }
  intros;apply (ap rat),plus_negate_r.
Unshelve. all:exact 1.
Qed.

Global Instance Rmeet@{} : Meet real
  := lipschitz_extend_binary _ _ (fun q r => eta (meet q r)) 1 1.

Global Instance Rmeet_lipschitz_l@{} : forall s : real, NonExpanding (⊓ s)
  := fun _ => lipschitz_nonexpanding _.
Global Instance Rmeet_lipschitz_r@{} : forall s : real, NonExpanding (s ⊓)
  := fun _ => lipschitz_nonexpanding _.

Typeclasses Opaque Rmeet.

Definition Rmeet_rat_rat@{} q r : meet (rat q) (rat r) = rat (meet q r)
  := idpath.

Global Instance Rjoin@{} : Join real
  := lipschitz_extend_binary _ _ (fun q r => eta (join q r)) 1 1.

Global Instance Rjoin_lipschitz_l@{} : forall s : real, NonExpanding (⊔ s)
  := fun _ => lipschitz_nonexpanding _.
Global Instance Rjoin_lipschitz_r@{} : forall s : real, NonExpanding (s ⊔)
  := fun _ => lipschitz_nonexpanding _.

Typeclasses Opaque Rjoin.

Definition Rjoin_rat_rat@{} q r : join (rat q) (rat r) = rat (join q r)
  := idpath.

Global Instance Rle@{} : Le real := fun x y => join x y = y.
Arguments Rle _ _ /.

Global Instance Rlt@{} : Lt real := fun x y =>
  merely (exists q r, x <= (rat q) /\ q < r /\ (rat r) <= y).
Arguments Rlt _ _ /.

Global Instance Rap@{} : Apart@{UQ UQ} real := fun x y => x < y \/ y < x.
Arguments Rap _ _ /.

Instance Rjoin_comm@{} : Commutative (@join _ Rjoin).
Proof.
hnf. apply unique_continuous_binary_extension.
{ apply _. }
{ apply _. }
intros;apply (ap rat).
apply join_sl_order_join_sl.
Qed.

Existing Instance lattice_order_lattice.

Lemma R_lattice' : LatticeOrder Rle.
Proof.
split.
- apply @alt_Build_MeetSemiLatticeOrder;[
  repeat split;unfold sg_op,meet_is_sg_op;change Rmeet with meet
  |apply _|].
  + apply _.
  + hnf.
    apply unique_continuous_ternary_extension.
    { change (Continuous (uncurry meet ∘ map2 (@id real) (uncurry meet) ∘
        prod_assoc^-1)).
      apply _. }
    { change (Continuous (uncurry meet ∘ map2 (uncurry meet) (@id real))).
      apply _. }
    intros;change (rat (q ⊓ (r ⊓ s)) = rat ((q ⊓ r) ⊓ s));apply (ap rat).
    apply associativity.
  + hnf.
    apply unique_continuous_binary_extension;try apply _.
    intros;apply (ap rat). apply commutativity.
  + hnf. red.
    apply (unique_continuous_extension _);try apply _.
    { change (Continuous (compose (uncurry meet) (@BinaryDup real)));apply _. }
    intros;apply (ap rat),idempotency,_.
  + unfold le,Rle. intros x y;split;intros E.
    * rewrite <-E.
      clear E;revert x y;apply unique_continuous_binary_extension.
      { change (Continuous (uncurry meet ∘ map2 id (uncurry join) ∘
          prod_assoc^-1 ∘ map2 BinaryDup (@id real))).
        apply _. }
      { apply _. }
      intros;apply (ap rat). apply (meet_join_absorption _).
    * rewrite <-E.
      clear E;revert x y;apply unique_continuous_binary_extension.
      { change (Continuous (uncurry join ∘ map2 (uncurry meet) (@id real) ∘
          prod_assoc ∘ map2 id BinaryDup)).
        apply _. }
      { apply _. }
      intros;apply (ap rat).
      rewrite (commutativity (f:=join)),(commutativity (f:=meet)).
      apply (join_meet_absorption _).
- apply @alt_Build_JoinSemiLatticeOrder;[|apply _|reflexivity].
  repeat split;unfold sg_op,join_is_sg_op;change Rjoin with join.
  + apply _.
  + hnf.
    apply unique_continuous_ternary_extension.
    { change (Continuous (uncurry join ∘ map2 (@id real) (uncurry join) ∘
        prod_assoc^-1)).
      apply _. }
    { change (Continuous (uncurry join ∘ map2 (uncurry join) (@id real))).
      apply _. }
    intros;apply (ap rat). apply associativity.
  + hnf.
    apply unique_continuous_binary_extension;try apply _.
    intros;apply (ap rat). apply commutativity.
  + hnf. red.
    apply (unique_continuous_extension _);try apply _.
    { change (Continuous (uncurry join ∘ (@BinaryDup real)));apply _. }
    intros;apply (ap rat),idempotency,_.
Qed.

Instance R_lattice@{} : LatticeOrder Rle
  := R_lattice'@{Ularge UQ}.

Lemma Rplus_le_preserving@{} : forall z : real,
  OrderPreserving (z +).
Proof.
intros z. hnf. unfold le;simpl. intros x y E.
rewrite <-E;clear E.
revert z x y;apply unique_continuous_ternary_extension.
{ change (Continuous (uncurry join ∘
    map2 (uncurry (+)) (uncurry (+) ∘ map2 id (uncurry join)) ∘
    prod_assoc ∘
    (* (u, (v, (u, (v, w)))) *)
    map2 id (map2 id prod_symm ∘ prod_assoc^-1 ∘
      prod_symm ∘ map2 id prod_assoc^-1) ∘
    (* (u, (u, ((v,v),w))) *)
    prod_assoc^-1 ∘ prod_assoc^-1 ∘
    (* (((u,u),(v,v)),w) *)
    map2 (map2 BinaryDup BinaryDup) (@id real))).
  apply _. }
{ change (Continuous (uncurry (+) ∘ map2 (@id real) (uncurry join) ∘
    prod_assoc^-1)).
  apply _. }
intros;change (rat ((q + r) ⊔ (q + (r ⊔ s))) = rat (q + (r ⊔ s)));apply (ap rat).
apply join_r. apply (order_preserving (q +)).
apply join_ub_l.
Qed.

Lemma Rplus_le_reflecting@{} : forall z : real,
  OrderReflecting (z +).
Proof.
intros z x y E.
apply (Rplus_le_preserving (- z)) in E.
rewrite !(simple_associativity (f:=plus) (-z) z),!left_inverse,!left_identity in E.
trivial.
Qed.

Instance Rplus_le_embedding@{} : forall z : real, OrderEmbedding (z +).
Proof.
intros;split.
- apply Rplus_le_preserving.
- apply Rplus_le_reflecting.
Qed.

Lemma rat_le_preserving : OrderPreserving rat.
Proof.
hnf. intros q r E;hnf.
apply (ap rat). apply join_r,E.
Qed.

Lemma rat_le_reflecting : OrderReflecting rat.
Proof.
hnf. intros q r E;unfold le,Rle in E.
apply (eta_injective _) in E. rewrite <-E;apply join_ub_l.
Qed.

Instance rat_le_embedding : OrderEmbedding rat.
Proof.
split.
- apply rat_le_preserving.
- apply rat_le_reflecting.
Qed.

Lemma rat_lt_preserving@{} : StrictlyOrderPreserving rat.
Proof.
hnf. intros x y E.
hnf. apply tr;exists x,y;repeat split;auto.
Qed.

Lemma rat_lt_reflecting@{} : StrictlyOrderReflecting rat.
Proof.
hnf. intros x y;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
apply (order_reflecting rat) in E1;apply (order_reflecting rat) in E3.
apply le_lt_trans with q;trivial.
apply lt_le_trans with r;trivial.
Qed.

Instance rat_lt_embedding : StrictOrderEmbedding rat.
Proof.
split.
- apply rat_lt_preserving.
- apply rat_lt_reflecting.
Qed.

Instance Rlt_irrefl@{} : Irreflexive Rlt.
Proof.
hnf. intros x;hnf;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
pose proof (transitivity E3 E1) as E4.
apply rat_le_reflecting in E4.
revert E2;apply le_iff_not_lt_flip. trivial.
Qed.

Instance Rlt_trans@{} : Transitive Rlt.
Proof.
intros a b c.
unfold Rlt.
apply (Trunc_ind (fun _ => _ -> _));intros [q1 [r1 [E1 [E2 E3]]]];
apply (Trunc_ind _);intros [q2 [r2 [E4 [E5 E6]]]].
apply tr. exists q1,r2. split;[|split];trivial.
pose proof (rat_le_reflecting _ _ (transitivity E3 E4)) as E7.
apply lt_le_trans with r1;trivial.
apply lt_le. apply le_lt_trans with q2;trivial.
Qed.

Instance Rapart_ishprop : forall x y : real, IsHProp (apart x y).
Proof.
unfold apart;simpl. intros x y.
apply Sum.ishprop_sum;try apply _.
intros E1 E2.
apply (irreflexivity lt x). transitivity y;trivial.
Qed.

Lemma R_le_lt_trans@{} : forall a b c : real, a <= b -> b < c -> a < c.
Proof.
intros a b c E1;apply (Trunc_ind _);intros [q [r [E2 [E3 E4]]]].
apply tr;exists q,r;auto.
Qed.

Lemma R_lt_le_trans@{} : forall a b c : real, a < b -> b <= c -> a < c.
Proof.
intros a b c E0 E1;revert E0;apply (Trunc_ind _);intros [q [r [E2 [E3 E4]]]].
apply tr;exists q,r;auto.
Qed.

Lemma R_lt_le@{} : forall a b : real, a < b -> a <= b.
Proof.
intros a b;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
transitivity (rat q);trivial.
transitivity (rat r);trivial.
apply rat_le_preserving. apply lt_le. trivial.
Qed.

Lemma R_archimedean@{} : forall u v, u < v -> merely (exists q, u < rat q < v).
Proof.
intros u v;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
apply tr;exists ((q+r)/2).
split.
- apply R_le_lt_trans with (rat q);trivial.
  apply rat_lt_preserving. apply Q_average_between. exact E2.
- apply R_lt_le_trans with (rat r);trivial.
  apply rat_lt_preserving. apply Q_average_between. exact E2.
Qed.

Lemma R_archimedean_pos@{} : forall u v, 0 <= u -> u < v ->
  merely (exists q : Q+, u < rat (' q) < v).
Proof.
intros u v Eu E.
apply (merely_destruct (R_archimedean _ _ E)). intros [q [E1 E2]].
apply tr. simple refine (existT _ (mkQpos q _) _).
- apply rat_lt_reflecting. apply R_le_lt_trans with u;trivial.
- simpl. unfold cast;simpl. split;trivial.
Qed.

Lemma Rneg_le_flip@{} : forall x y : real, x <= y -> - y <= - x.
Proof.
intros x y E.
rewrite <-E.
clear E;revert x y;apply unique_continuous_binary_extension.
{ change (Continuous (uncurry join ∘ map2 (negate ∘ uncurry join) negate ∘
    prod_symm ∘ prod_assoc^-1 ∘ map2 BinaryDup (@id real))).
  apply _. }
{ apply _. }
intros q r;change (rat (- (q ⊔ r) ⊔ - q) = rat (- q));apply (ap rat).
apply join_r. apply (snd (flip_le_negate _ _)). apply join_ub_l.
Qed.

Lemma Rneg_le_flip_equiv@{} : forall x y : real, - y <= - x <-> x <= y.
Proof.
intros x y;split.
- intros E. apply Rneg_le_flip in E. rewrite !involutive in E.
  exact E.
- apply Rneg_le_flip.
Qed.

Lemma Rneg_lt_flip@{} : forall x y : real, - y < - x <-> x < y.
Proof.
intros x y;split;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
- apply flip_lt_negate in E2.
  apply Rneg_le_flip in E1;apply Rneg_le_flip in E3.
  rewrite involutive in E1;rewrite involutive in E3.
  apply tr;exists (-r),(-q). auto.
- apply tr;exists (-r),(-q);repeat split.
  + change (- y <= - (rat r)). apply (snd (Rneg_le_flip_equiv _ _)),E3.
  + apply (snd (flip_lt_negate _ _)),E2.
  + change (- rat q <= - x). apply (snd (Rneg_le_flip_equiv _ _)),E1.
Qed.
