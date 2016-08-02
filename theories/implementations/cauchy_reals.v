Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.integers
  HoTTClasses.interfaces.naturals
  HoTTClasses.interfaces.rationals
  HoTTClasses.interfaces.orders
  HoTTClasses.implementations.field_of_fractions
  HoTTClasses.implementations.natpair_integers
  HoTTClasses.theory.rings
  HoTTClasses.theory.integers
  HoTTClasses.theory.dec_fields
  HoTTClasses.orders.dec_fields
  HoTTClasses.theory.rationals
  HoTTClasses.orders.lattices
  HoTTClasses.theory.additional_operations
  HoTTClasses.theory.premetric
  HoTTClasses.implementations.partiality
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

Instance Rle_trans@{} : Transitive Rle.
Proof.
hnf. unfold le,Rle.
intros x y z E1 E2. rewrite <-E2,<-E1. clear E1 E2;revert x y z.
apply unique_continuous_ternary_extension.
{ change (Continuous (uncurry join ∘
    map2 id (uncurry join ∘ map2 (uncurry join) (@id real) ∘ prod_assoc)
    ∘ prod_assoc^-1 ∘ map2 BinaryDup id ∘ (prod_assoc^-1))).
  apply _. }
{ change (Continuous (uncurry join ∘ map2 (uncurry join) (@id real))).
  apply _. }
intros q r s.
change (rat (q ⊔ ((q ⊔ r) ⊔ s)) = rat ((q ⊔ r) ⊔ s)).
apply (ap rat).
apply join_r. apply join_le_compat_r,join_ub_l.
Qed.

Instance Rle_refl@{} : Reflexive Rle.
Proof.
change (forall x, join x x = x).
apply (unique_continuous_extension _);try apply _.
+ change (Continuous (compose (uncurry join) (@BinaryDup real)));apply _.
+ intros;apply (ap rat),semilattice_idempotent,join_sl_order_join_sl.
Qed.

Instance Rlt_irrefl@{} : Irreflexive Rlt.
Proof.
hnf. intros x;hnf;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
pose proof (transitivity E3 E1) as E4.
hnf in E4. apply (eta_injective _) in E4.
revert E2;apply le_iff_not_lt_flip. rewrite <-E4.
apply join_ub_l.
Qed.

Instance rat_le_reflecting : OrderReflecting rat.
Proof.
hnf. intros q r E;unfold le,Rle in E.
apply (eta_injective _) in E. rewrite <-E;apply join_ub_l.
Qed.

Instance rat_le_preserve : OrderPreserving rat.
Proof.
hnf. intros q r E;hnf.
apply (ap rat). apply join_r,E.
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

Instance rat_lt_preserving@{} : StrictlyOrderPreserving rat.
Proof.
hnf. intros x y E.
hnf. apply tr;exists x,y;repeat split;auto.
Qed.

Lemma R_lt_le@{} : forall a b : real, a < b -> a <= b.
Proof.
intros a b;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
transitivity (rat q);trivial.
transitivity (rat r);trivial.
apply rat_le_preserve. apply lt_le. trivial.
Qed.

Lemma rat_lt_reflecting@{} : StrictlyOrderReflecting rat.
Proof.
hnf. intros x y;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
apply (order_reflecting rat) in E1;apply (order_reflecting rat) in E3.
apply le_lt_trans with q;trivial.
apply lt_le_trans with r;trivial.
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

Lemma Rle_close_rat_rat' : forall q r, r <= q -> forall v e, close e (rat r) v ->
  v <= rat (q + ' e).
Proof.
intros q r E.
apply (C_ind0 _ (fun v => forall e, _ -> _)).
+ intros s e E'.
  rewrite (equiv_eta_eta_def _) in E'.
  hnf in E'. apply (order_preserving rat).
  apply lt_le. rewrite plus_comm. apply flip_lt_minus_l.
  apply le_lt_trans with (s - r).
  * apply plus_le_compat;[reflexivity|].
    apply (snd (flip_le_negate _ _)),E.
  * apply flip_lt_negate. rewrite <-negate_swap_r. apply E'.
+ intros y IH e xi.
  apply (equiv_rounded _) in xi.
  revert xi;apply (Trunc_ind _);intros [d [d' [He xi]]].
  hnf. unfold join,Rjoin. rewrite lipschitz_extend_binary_lim.
  change (lipschitz_extend_binary _ _ (fun q r => eta (join q r)) 1 1) with join.
  assert (E1 : forall n n', d' = n + n' -> y n <= rat (q + ' e)).
  { intros n n' Hd.
    apply IH. rewrite He. apply (equiv_triangle _) with (lim y);trivial.
    apply (equiv_symm _). rewrite Hd,qpos_plus_comm. apply (equiv_lim _).
  }
  apply equiv_path. intros z.
  destruct (Qpos_lt_min z d') as [a [ca [cb [E2 E3]]]].
  eapply (equiv_lim_eta _);[|simpl;erewrite E1;[apply (equiv_refl _)|]].
  * exact E2.
  * rewrite <-(Qpos_mult_1_l a),pos_unconjugate. exact E3.
Qed.

Definition Rle_close_rat_rat@{}
  := Rle_close_rat_rat'@{UQ}.

Instance Rjoin_comm@{} : Commutative (@join _ Rjoin).
Proof.
hnf. apply unique_continuous_binary_extension.
{ apply _. }
{ apply _. }
intros;apply (ap rat).
apply join_sl_order_join_sl.
Qed.

Local Existing Instance lattice_order_lattice.

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

Lemma Rle_close_rat@{} : forall q u, u <= rat q -> forall v e, close e u v ->
  v <= rat (q + ' e).
Proof.
intros q u E v e xi.
pose proof (non_expanding (join (rat q)) xi) as E1.
hnf in E. rewrite Rjoin_comm in E1.
rewrite E in E1.
pose proof (Rle_close_rat_rat q q (reflexivity q) _ _ E1) as E2.
transitivity (join (rat q) v);trivial.
apply join_ub_r.
Qed.

Lemma Rlt_close_rat_plus@{} : forall u q, u < rat q ->
  forall v e, close e u v -> v < rat (q + ' e).
Proof.
intros u q;apply (Trunc_ind (fun _ => forall v e, _ -> _)).
intros [q' [r [E1 [E2 E3]]]] v e xi.
hnf. apply tr. exists (q' + ' e),(r + ' e).
split;[|split].
- apply Rle_close_rat with u;trivial.
- apply plus_lt_le_compat;[|reflexivity].
  trivial.
- apply (order_preserving rat).
  apply plus_le_compat;[|reflexivity].
  apply (order_reflecting rat);trivial.
Qed.

Lemma Rlt_close_exists_aux@{} : forall u q, u < rat q ->
  merely (exists e, forall v, close e u v -> v < rat q).
Proof.
intros u q;apply (Trunc_ind _);intros [q' [r [E1 [E2 E3]]]].
transparent assert (rq : Q+).
{ exists (r-q').
  abstract (apply flip_pos_minus in E2; trivial).
}
apply tr;exists (rq / 2);intros v xi.
pose proof (Rle_close_rat _ _ E1 _ _ xi) as E4.
change (v <= rat (q' + (r - q') / 2)) in E4.
apply tr;econstructor;exists r;repeat split;eauto.
apply flip_pos_minus. rewrite negate_plus_distr.
rewrite negate_mult_distr_l,<-negate_swap_l.
assert (Hrw : r + (- q' + (- r + q') / 2) = (r - q') / 2).
{ path_via (2 / 2 * r + (2 / 2 * (- q') + (- r + q') / 2)).
  { rewrite dec_recip_inverse;[|solve_propholds].
    rewrite !mult_1_l;trivial. }
  abstract ring_tac.ring_with_integers (NatPair.Z nat).
}
rewrite Hrw.
apply pos_mult_compat;[|apply _].
apply (snd (flip_pos_minus _ _)). trivial.
Qed.

Lemma Rlt_close_exists@{} : forall u v, u < v ->
  merely (exists e, forall w, close e u w -> w < v).
Proof.
intros u v;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
generalize (Rlt_close_exists_aux u r
  (R_le_lt_trans _ _ _ E1 (rat_lt_preserving _ _ E2))).
apply (Trunc_ind _);intros [e E4];apply tr;exists e.
intros w xi;apply R_lt_le_trans with (rat r);auto.
Qed.

Definition Rabs_val := lipschitz_extend _ (compose rat abs) 1.

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
hnf. apply path_forall. intros x. unfold compose.
apply Rabs_of_nonneg, Rabs_nonneg.
Qed.

Lemma equiv_0_metric' : forall e u, close e u 0 -> abs u < rat (' e).
Proof.
intros e u;revert u e;apply (C_ind0 _ (fun u => forall e, _ -> _)).
- intros q e E.
  rewrite (equiv_eta_eta_def _) in E.
  hnf in E. rewrite negate_0,plus_0_r in E.
  apply rat_lt_preserving.
  destruct (total_abs_either q) as [[_ E']|[_ E']];rewrite E'.
  + apply E.
  + apply flip_lt_negate. rewrite involutive. apply E.
- intros x IH e xi.
  generalize (fst (equiv_rounded _ _ _ _) xi).
  apply (Trunc_ind _);intros [d [d' [He xi']]].
  rewrite (equiv_lim_eta_def _) in xi'.
  revert xi';apply (Trunc_ind _);intros [n [n' [Hd E1]]].
  apply IH in E1.
  rewrite He,Hd.
  assert (Hrw : (' (n + n' + d')) = ' n' + ' (n + d'))
  by ring_tac.ring_with_nat.
  rewrite Hrw;clear Hrw.
  apply (Rlt_close_rat_plus _ _ E1).
  apply (non_expanding abs).
  rewrite qpos_plus_comm. apply (equiv_lim _).
Qed.

Definition equiv_0_metric@{}
  := equiv_0_metric'@{UQ UQ}.

Lemma equiv_to_metric@{} : forall e u v, close e u v -> abs (u - v) < rat (' e).
Proof.
intros e u v xi.
rewrite <-Rabs_idempotent.
apply equiv_0_metric.
rewrite <-(Rabs_of_0' (u - u));[|apply right_inverse].
apply (non_expanding (fun w => abs (u - w))).
apply (equiv_symm _),xi.
Qed.

Lemma metric_to_equiv_rat_lim@{} (q : Q)
  (y : Approximation real)
  (IHy : ∀ e e0 : Q+, abs (rat q - y e) < rat (' e0) → close e0 (rat q) (y e))
  (e : Q+)
  (E1 : abs (rat q - lim y) < rat (' e))
  : close e (rat q) (lim y).
Proof.
generalize (R_archimedean _ _ E1). apply (Trunc_ind _);intros [d [E2 E3]].
apply rat_lt_reflecting in E3.
pose proof (snd (flip_pos_minus _ _) E3) as E4.
assert (Hd : 0 < d).
{ revert E2;apply (Trunc_ind _).
  intros [s [s' [F1 [F2 F3]]]].
  apply rat_le_reflecting in F3.
  apply lt_le_trans with s';trivial.
  apply le_lt_trans with s;trivial.
  apply rat_le_reflecting.
  transitivity (abs (rat q - lim y));trivial.
  apply Rabs_nonneg.
}
pose (D := mkQpos d Hd).
pose (ED := mkQpos _ E4).
assert (Hrw : e = D + (ED / 4 + ED / 4) + (ED / 4 + ED / 4)).
{ path_via (D + ED).
  { apply pos_eq;unfold D, ED.
    abstract ring_tac.ring_with_integers (NatPair.Z nat).
  }
  path_via (D + 4 / 4 * ED).
  { rewrite pos_recip_r,Qpos_mult_1_l;trivial. }
  apply pos_eq;abstract ring_tac.ring_with_nat.
}
rewrite Hrw.
eapply (equiv_triangle _);[|apply (equiv_lim _)].
apply IHy. apply (Rlt_close_rat_plus _ _ E2).
apply (non_expanding (fun u => abs (rat q - u))).
apply (equiv_symm _),(equiv_lim _).
Qed.

Lemma Rabs_neg_flip@{} : forall a b : real, abs (a - b) = abs (b - a).
Proof.
apply (unique_continuous_binary_extension _);try apply _.
intros q r;change (rat (abs (q - r)) = rat (abs (r - q)));apply (ap rat).
apply Qabs_neg_flip.
Qed.

Lemma metric_to_equiv_lim_lim@{} (x : Approximation real)
  (IHx : ∀ (e : Q+) (v : real) (e0 : Q+),
        abs (x e - v) < rat (' e0) → close e0 (x e) v)
  (y : Approximation real)
  (IHy : ∀ e e0 : Q+, abs (lim x - y e) < rat (' e0) → close e0 (lim x) (y e))
  (e : Q+)
  (E1 : abs (lim x - lim y) < rat (' e))
  : close e (lim x) (lim y).
Proof.
generalize (R_archimedean _ _ E1). apply (Trunc_ind _);intros [d [E2 E3]].
apply rat_lt_reflecting in E3.
pose proof (snd (flip_pos_minus _ _) E3) as E4.
assert (Hd : 0 < d).
{ revert E2;apply (Trunc_ind _).
  intros [s [s' [F1 [F2 F3]]]].
  apply rat_le_reflecting in F3.
  apply lt_le_trans with s';trivial.
  apply le_lt_trans with s;trivial.
  apply rat_le_reflecting.
  transitivity (abs (lim x - lim y));trivial.
  apply Rabs_nonneg.
}
pose (D := mkQpos d Hd).
pose (ED := mkQpos _ E4).
assert (Hrw : e = D + (ED / 4 + ED / 4) + (ED / 4 + ED / 4)).
{ path_via (D + ED).
  { apply pos_eq;unfold D, ED.
    abstract ring_tac.ring_with_integers (NatPair.Z nat).
  }
  path_via (D + 4 / 4 * ED).
  { rewrite pos_recip_r,Qpos_mult_1_l;trivial. }
  apply pos_eq;abstract ring_tac.ring_with_nat.
}
rewrite Hrw.
eapply (equiv_triangle _);[|apply (equiv_lim _)].
apply IHy. apply (Rlt_close_rat_plus _ _ E2).
apply (non_expanding (fun u => abs (lim x - u))).
apply (equiv_symm _),(equiv_lim _).
Qed.

Lemma metric_to_equiv@{} : forall e u v, abs (u - v) < rat (' e) -> close e u v.
Proof.
intros e u v;revert u v e;apply (C_ind0 _ (fun u => forall v e, _ -> _));
[intros q|intros x IHx];
(apply (C_ind0 _ (fun v => forall e, _ -> _));[intros r|intros y IHy]);
intros e E1.
- apply equiv_eta_eta. apply Qclose_alt.
  apply rat_lt_reflecting,E1.
- apply metric_to_equiv_rat_lim;auto.
- apply (equiv_symm _),metric_to_equiv_rat_lim.
  + intros n n' E;apply (equiv_symm _),IHx.
    rewrite Rabs_neg_flip. trivial.
  + rewrite Rabs_neg_flip. trivial.
- apply metric_to_equiv_lim_lim;auto.
Qed.

Lemma equiv_metric_applied_rw'
  : forall e u v, close e u v = (abs (u - v) < rat (' e)).
Proof.
intros. apply TruncType.path_iff_ishprop_uncurried.
split.
- apply equiv_to_metric.
- apply metric_to_equiv.
Qed.

Definition equiv_metric_applied_rw@{} := equiv_metric_applied_rw'@{Ularge}.

Lemma equiv_metric_rw' : close = fun e u v => abs (u - v) < rat (' e).
Proof.
repeat (apply path_forall;intro).
apply equiv_metric_applied_rw.
Qed.

Definition equiv_metric_rw@{} := equiv_metric_rw'@{Ularge Ularge Ularge}.

Instance Rplus_le_preserving@{} : forall z : real,
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

Lemma Rlt_close_plus@{} : forall u v, u < v ->
  forall w e, close e u w -> w < v + rat (' e).
Proof.
intros u v E w e xi;revert E;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
apply R_lt_le_trans with (rat (r + ' e)).
- apply Rlt_close_rat_plus with u;trivial.
  apply R_le_lt_trans with (rat q);trivial.
  apply rat_lt_preserving;trivial.
- rewrite plus_comm. rewrite Rplus_comm.
  change (rat (' e) + rat r <= rat (' e) + v).
  apply (order_preserving (rat (' e) +)). trivial.
Qed.

Lemma Rplus_le_reflecting@{} : forall z : real,
  OrderReflecting (z +).
Proof.
intros z;hnf;unfold le;simpl;intros x y E.
assert (Hrw : y = z + y - z).
{ rewrite (commutativity (f:=plus) z y),
  <-(simple_associativity (f:=plus) y z (-z)).
  rewrite right_inverse,right_identity. trivial.
}
path_via (z + y - z);clear Hrw.
rewrite <-E. clear E.
revert z x y;apply unique_continuous_ternary_extension.
{ change (Continuous (uncurry join ∘ (@snd real (real /\ real)) ∘ prod_assoc^-1)).
  apply _. }
{ change (Continuous
    (uncurry (+) ∘ map2 (uncurry join ∘ map2 (uncurry (+)) (uncurry (+))) negate ∘
        map2 (map2 id prod_symm ∘ prod_assoc^-1 ∘
      map2 (prod_assoc ∘ prod_symm) id ∘ prod_symm ∘ prod_assoc^-1 ∘ prod_symm) id ∘
    prod_symm ∘ prod_assoc^-1 ∘ prod_assoc^-1 ∘ prod_assoc^-1 ∘
    map2 (map2 (map2 BinaryDup id ∘ BinaryDup) (@id real)) id)).
  apply _. }
intros;change (rat (r ⊔ s) = rat ((q + r) ⊔ (q + s) - q));apply (ap rat).
destruct (total le r s) as [E|E].
- rewrite (join_r _ _ E).
  rewrite (join_r _ _ (order_preserving (q +) _ _ E)).
  rewrite (plus_comm q s),<-plus_assoc,plus_negate_r,plus_0_r;trivial.
- rewrite (join_l _ _ E).
  rewrite (join_l _ _ (order_preserving (q +) _ _ E)).
  rewrite (plus_comm q r),<-plus_assoc,plus_negate_r,plus_0_r;trivial.
Qed.

Instance Rplus_le_embedding@{} : forall z : real, OrderEmbedding (z +).
Proof.
intros;split.
- apply Rplus_le_preserving.
- apply Rplus_le_reflecting.
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

Lemma Rlt_cotrans_rat@{} : forall x q r, q < r -> hor (rat q < x) (x < rat r).
Proof.
apply (C_ind0 _ (fun x => forall q r, _ -> _)).
- intros s q r E. generalize (cotransitive E s).
  apply (Trunc_ind _);intros [E'|E'];apply tr;[left|right];
  apply rat_lt_preserving,E'.
- intros x IH q r E0.
  destruct (Q_dense _ _ E0) as [q1 [E1 E2]].
  destruct (Q_dense _ _ E2) as [r1 [E3 E4]].
  clear E0 E2.
  destruct (Qpos_lt_min (Qpos_diff _ _ E1) (Qpos_diff _ _ E4))
    as [n [n1 [n2 [Hn1 Hn2]]]].
  generalize (IH n _ _ E3);apply (Trunc_ind _).
  intros [E5|E5];apply tr;[left|right].
  + apply Rneg_lt_flip. change (- lim x < rat (- q)).
    assert (Hrw : - q = - q1 + ' Qpos_diff q q1 E1).
    { set (D := Qpos_diff q q1 E1).
      rewrite (Qpos_diff_pr _ _ E1). unfold D;clear D.
      rewrite negate_plus_distr. rewrite <-plus_assoc,plus_negate_l,plus_0_r.
      trivial.
    }
    rewrite Hrw;clear Hrw.
    apply Rlt_close_rat_plus with (- (x n)).
    * apply (snd (Rneg_lt_flip _ _) E5).
    * apply (non_expanding (-)).
      rewrite Hn1. rewrite qpos_plus_comm. apply (equiv_lim _).
  + rewrite (Qpos_diff_pr _ _ E4).
    apply Rlt_close_rat_plus with (x n);trivial.
    rewrite Hn2,qpos_plus_comm. apply (equiv_lim _).
Qed.

Instance Rlt_cotrans@{} : CoTransitive (@lt real _).
Proof.
hnf. intros x y E z;revert E;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
generalize (Rlt_cotrans_rat z q r E2);apply (Trunc_ind _).
intros [E4|E4];apply tr;[left|right].
- apply R_le_lt_trans with (rat q);trivial.
- apply R_lt_le_trans with (rat r);trivial.
Qed.

Instance Rap_cotrans@{} : CoTransitive (@apart real _).
Proof.
hnf. intros x y [E|E] z.
- apply (merely_destruct (cotransitive E z)).
  intros [E1|E1];apply tr;[left|right];hnf;auto.
- apply (merely_destruct (cotransitive E z)).
  intros [E1|E1];apply tr;[right|left];hnf;auto.
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

Lemma R_Qpos_bounded@{} : forall x : real,
  merely (exists q : Q+, abs x < rat (' q)).
Proof.
apply (C_ind0 _ _).
- intros q;apply tr. simple refine (existT _ _ _).
  + exists (abs q + 1).
    abstract (apply le_lt_trans with (abs q);
    [apply Qabs_nonneg|apply pos_plus_lt_compat_r;solve_propholds]).
  + simpl. apply rat_lt_preserving. change (abs q < abs q + 1).
    abstract (apply pos_plus_lt_compat_r;solve_propholds).
- intros x IH.
  generalize (IH 1).
  apply (Trunc_ind _);intros [q E].
  apply tr;exists (q + 2).
  change (abs (lim x) < rat (' q + ' 2)).
  apply Rlt_close_rat_plus with (abs (x 1)).
  + trivial.
  + apply (non_expanding abs).
    apply (equiv_lim _).
Defined.

Definition QRmult@{} : Q -> real -> real
  := fun q => lipschitz_extend _ (compose rat (q *.)) (pos_of_Q q).

Instance QRmult_lipschitz : forall q, Lipschitz (QRmult q) (pos_of_Q q)
  := _.
Typeclasses Opaque QRmult.

Lemma QRmult_negate : forall q u, - QRmult q u = QRmult (- q) u.
Proof.
intro;apply (unique_continuous_extension _ _ _).
intros r;apply (ap rat). apply negate_mult_distr_l.
Qed.

Lemma QRmult_plus_distr : forall q r u, QRmult q u + QRmult r u = QRmult (q + r) u.
Proof.
intros q r;apply (unique_continuous_extension _);try apply _.
{ change (Continuous (uncurry (+) ∘ map2 (QRmult q) (QRmult r) ∘ BinaryDup)).
  apply _. }
intros s;apply (ap rat). Symmetry;apply distribute_r.
Qed.

Lemma QRmult_lipschitz_interval_aux (a:Q+)
  : forall x, abs x <= rat (' a) ->
  forall q r : Q, abs (QRmult q x - QRmult r x) <= rat (abs (q - r) * ' a).
Proof.
intros x E q r. rewrite QRmult_negate,QRmult_plus_distr.
change (rat (abs (q - r) * ' a)) with (QRmult (abs (q - r)) (rat (' a))).
rewrite <-E. clear E.
revert x;eapply @unique_continuous_extension;try apply _.
- change (Continuous (uncurry join ∘
    map2 (abs ∘ QRmult (q - r)) (QRmult (abs (q - r)) ∘ (⊔ rat (' a)) ∘ abs) ∘
    BinaryDup)).
  apply _.
- change (Continuous (QRmult (abs (q - r)) ∘ (⊔ rat (' a)) ∘ abs)).
  apply _.
- intros s.
  change (rat (abs ((q - r) * s) ⊔ abs (q - r) * (abs s ⊔ ' a)) =
    rat (abs (q - r) * (abs s ⊔ ' a))).
  apply (ap rat).
  apply join_r.
  rewrite Qabs_mult. apply mult_le_compat.
  + apply Qabs_nonneg.
  + apply Qabs_nonneg.
  + reflexivity.
  + apply join_ub_l.
Qed.

Instance Qbounded_lipschitz (a : Q+)
  : forall v : Interval (- rat (' a)) (rat (' a)),
    Lipschitz (λ q : Q, QRmult q (interval_proj _ _ v)) (a + 1).
Proof.
intros v e x y xi.
apply Qclose_alt in xi. apply metric_to_equiv.
apply R_le_lt_trans with (rat (' (a * e))).
- etransitivity.
  + apply (QRmult_lipschitz_interval_aux a).
    apply (snd (Rabs_le_pr _ _)).
    split;apply v.2.
  + apply rat_le_preserve. rewrite qpos_mult_comm.
    apply mult_le_compat;try solve_propholds.
    * apply Qabs_nonneg.
    * reflexivity.
- apply rat_lt_preserving. rewrite 2!(qpos_mult_comm _ e).
  apply pos_mult_le_lt_compat;try split;try solve_propholds.
  + reflexivity.
  + apply pos_plus_lt_compat_r. solve_propholds.
Qed.

Definition Rbounded_mult@{} (a : Q+)
  : real -> Interval (- rat (' a)) (rat (' a)) -> real
  := fun u v => lipschitz_extend _
      (fun q => QRmult q (interval_proj _ _ v)) (a+1) u.

Instance Rbounded_mult_lipschitz : forall a v,
  Lipschitz (fun u => Rbounded_mult a u v) (a+1)
  := _.
Typeclasses Opaque Rbounded_mult.

Definition interval_back
  : sigT (fun a : Q+ => Interval (- rat (' a)) (rat (' a))) -> real
  := fun x => x.2.1.

Instance interval_proj_issurj@{}
  : TrM.IsConnMap@{Uhuge Ularge UQ UQ Ularge} (trunc_S minus_two) interval_back.
Proof.
apply BuildIsSurjection. intros x.
generalize (R_Qpos_bounded x). apply (Trunc_ind _);intros [q E].
apply tr. simple refine (existT _ _ _).
- exists q. exists x. apply Rabs_le_pr. apply R_lt_le. exact E.
- simpl. reflexivity.
Defined.

Definition Rinterval_inject@{} : forall a b : Q, a <= b ->
  Interval (- rat a) (rat a) -> Interval (- (rat b)) (rat b).
Proof.
intros a b E s.
exists (s.1).
split.
- transitivity (- (rat a));[|apply s.2].
  apply Rneg_le_flip,rat_le_preserve,E.
- transitivity (rat a);[apply s.2|].
  apply rat_le_preserve,E.
Defined.

Lemma Rbounded_mult_respects : ∀ z x y, interval_back x = interval_back y →
  Rbounded_mult x.1 z x.2 = Rbounded_mult y.1 z y.2.
Proof.
intros z x y E.
revert z. apply (unique_continuous_extension _ _ _).
intros q. unfold Rbounded_mult.
exact (ap _ E).
Qed.

Definition Rmult@{} : Mult real
  := fun x => jections.surjective_factor@{UQ UQ UQ Uhuge Ularge
    Ularge UQ UQ Uhuge Ularge
    UQ} _ interval_back (Rbounded_mult_respects x).
Global Existing Instance Rmult.

Lemma Rmult_pr@{} x : (fun y => Rbounded_mult y.1 x y.2) =
  compose (x *.) interval_back.
Proof.
apply jections.surjective_factor_pr.
Qed.

Definition Rmult_rat_rat@{} q r : (rat q) * (rat r) = rat (q * r)
  := idpath.

Lemma Rmult_interval_proj_applied : forall a x y,
  x * interval_proj (rat (- ' a)) (rat (' a)) y =
  Rbounded_mult a x y.
Proof.
intros;change (Rbounded_mult a x) with
  ((fun y : exists a, Interval (rat (- ' a)) (rat (' a)) =>
    Rbounded_mult y.1 x y.2) ∘ (fun s => existT _ a s)).
rewrite Rmult_pr. reflexivity.
Qed.

Lemma Rmult_interval_proj : forall a y,
  (fun x => x * interval_proj (rat (- ' a)) (rat (' a)) y) =
  (fun x => Rbounded_mult a x y).
Proof.
intros. apply path_forall. intros x.
apply Rmult_interval_proj_applied.
Qed.

Lemma Rmult_lipschitz_aux : forall a y,
  Lipschitz (.* (interval_proj (rat (- ' a)) (rat (' a)) y)) (a+1).
Proof.
intros a y. rewrite Rmult_interval_proj. apply _.
Qed.

Lemma Rmult_lipschitz_aux_alt : forall a y, abs y <= rat (' a) ->
  Lipschitz (.* y) (a+1).
Proof.
intros a y E. apply Rabs_le_pr in E.
change y with (interval_proj (rat (- ' a)) (rat (' a)) (existT _ y E)).
apply Rmult_lipschitz_aux.
Qed.

Lemma uniform_on_intervals_continuous `{Closeness A} (f:real -> A)
  (mu : Q+ -> Q+ -> Q+)
  {Emu : forall a : Q+,
    Uniform (f ∘ interval_proj (rat (- ' a)) (rat (' a))) (mu a)}
  : Continuous f.
Proof.
intros u e.
apply (merely_destruct (R_Qpos_bounded u)). intros [a Ea].
hnf in Emu. unfold compose in Emu.
apply (merely_destruct (R_archimedean _ _ Ea)). intros [q [Eq Eq']].
apply rat_lt_reflecting in Eq'.
apply tr;exists (meet (mu a e) (Qpos_diff _ _ Eq')).
intros v xi.
assert (xi1 : close (mu a e) u v).
{ eapply rounded_le;[exact xi|].
  apply meet_lb_l. }
assert (xi2 : close (Qpos_diff q (' a) Eq') u v).
{ eapply rounded_le;[exact xi|].
  apply meet_lb_r. }
assert (E1 :  rat (- ' a) <= u /\ u <= rat (' a)).
{ change (rat (- ' a)) with (- (rat (' a))). apply Rabs_le_pr.
  transitivity (rat q);apply R_lt_le;trivial.
  apply rat_lt_preserving;trivial.
}
assert (E2 : rat (- ' a) <= v /\ v <= rat (' a)).
{ change (rat (- ' a)) with (- (rat (' a))). apply Rabs_le_pr.
  rewrite (Qpos_diff_pr _ _ Eq').
  apply R_lt_le.
  eapply Rlt_close_rat_plus;[exact Eq|].
  apply (non_expanding abs),xi2.
}
exact (Emu _ _ (existT _ _ E1) (existT _ _ E2) xi1).
Qed.

Lemma Rmult_continuous_r' : forall y : real, Continuous (.* y).
Proof.
intros. red. apply (merely_destruct (R_Qpos_bounded y)).
intros [a Eq]. apply R_lt_le in Eq. apply Rabs_le_pr in Eq.
change (Continuous (.* y)). eapply lipschitz_continuous.
change (.* y) with (.* (interval_proj (rat (- ' a)) (rat (' a)) (existT _ y Eq))).
apply Rmult_lipschitz_aux.
Qed.

Definition Rmult_continuous_r@{} := Rmult_continuous_r'@{Ularge Ularge}.
Existing Instance Rmult_continuous_r.

Lemma Rmult_rat_l q x : rat q * x = QRmult q x.
Proof.
apply (merely_destruct (R_Qpos_bounded x)).
intros [d Ed].
apply R_lt_le in Ed. apply Rabs_le_pr in Ed.
change (rat q * x) with
  (rat q * interval_proj (rat (- ' d)) (rat (' d)) (existT _ x Ed)).
rewrite Rmult_interval_proj_applied. reflexivity.
Qed.

Lemma Rmult_abs_l : forall a b c, abs (a * b - a * c) = abs a * abs (b - c).
Proof.
intros a b c;revert a. apply (unique_continuous_extension _).
{ change (Continuous (abs ∘ uncurry plus ∘ map2 (.* b) (negate ∘ (.* c)) ∘
    (@BinaryDup real))).
  repeat apply continuous_compose;apply _.
}
{ change (Continuous ((.* (abs (b - c))) ∘ abs)).
  apply _. }
intros q.
change (abs (rat q)) with (rat (abs q)).
rewrite !Rmult_rat_l.
revert b c. apply unique_continuous_binary_extension.
{ change (Continuous (abs ∘ uncurry plus ∘ map2 (QRmult q) (negate ∘ QRmult q))).
  apply _. }
{ change (Continuous (QRmult (abs q) ∘ abs ∘ uncurry plus ∘ map2 id negate)).
  apply _. }
intros r s. change (rat (abs (q * r - q * s)) = rat (abs q * abs (r - s))).
apply (ap rat).
rewrite negate_mult_distr_r,<-plus_mult_distr_l.
apply Qabs_mult.
Qed.

Lemma Rmult_le_compat_abs@{} : forall a b c d : real, abs a <= abs c ->
  abs b <= abs d ->
  abs a * abs b <= abs c * abs d.
Proof.
intros ???? E1 E2;rewrite <-E1,<-E2. clear E1 E2.
red;simpl.
revert a c. apply unique_continuous_binary_extension.
{ change (Continuous (uncurry join ∘ map2
    ((.* abs b) ∘ abs ∘ fst)
    ((.* (join (abs b) (abs d))) ∘ uncurry join ∘ map2 abs abs) ∘
  BinaryDup)).
  repeat apply continuous_compose. 1,3:apply _.
  apply map2_continuous. 1,2:apply _.
  { apply continuous_compose. 2:apply _.
    apply continuous_compose;apply _. }
  { apply continuous_compose;apply _. }
}
{ change (Continuous ((.* (join (abs b) (abs d))) ∘ uncurry join ∘ map2 abs abs)).
  apply _. }
intros q r.
change (abs (rat q)) with (rat (abs q));
change (abs (rat r)) with (rat (abs r)).
change (rat (abs q) ⊔ rat (abs r)) with
  (rat (abs q ⊔ abs r)).
rewrite !Rmult_rat_l.
revert b d. apply unique_continuous_binary_extension.
{ change (Continuous (uncurry join ∘ map2
    (QRmult (abs q) ∘ abs ∘ fst)
    (QRmult (join (abs q) (abs r)) ∘ uncurry join ∘ map2 abs abs) ∘
  BinaryDup)).
  apply _. }
{ change (Continuous (QRmult (join (abs q) (abs r)) ∘ uncurry join ∘ map2 abs abs)).
  apply _. }
intros s t.
change (rat (abs q * abs s ⊔ (abs q ⊔ abs r) * (abs s ⊔ abs t)) =
rat ((abs q ⊔ abs r) * (abs s ⊔ abs t))).
apply (ap rat).
apply join_r. apply mult_le_compat.
- apply Qabs_nonneg.
- apply Qabs_nonneg.
- apply join_ub_l.
- apply join_ub_l.
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

Lemma R_bounded_2@{} : forall u v,
  merely (exists d d' : Q+, abs u < rat (' d') /\ abs v < rat (' d')
  /\ ' d' < ' d).
Proof.
intros.
apply (merely_destruct (R_Qpos_bounded u)).
intros [d Ed].
apply (merely_destruct (R_Qpos_bounded v)).
intros [n En].
apply tr;exists (join d n + 1) ,(join d n).
repeat split.
- apply R_lt_le_trans with (rat (' d));trivial.
  apply rat_le_preserve,join_ub_l.
- apply R_lt_le_trans with (rat (' n));trivial.
  apply rat_le_preserve,join_ub_r.
- apply pos_plus_le_lt_compat_r.
  + solve_propholds.
  + reflexivity.
Qed.

Lemma Rmult_continuous@{} : Continuous (uncurry (@mult real _)).
Proof.
intros [u1 v1] e.
apply (merely_destruct (R_bounded_2 u1 v1));intros [d [d' [Ed1 [Ed2 Ed3]]]].
apply tr;exists (meet (Qpos_diff (' d') (' d) Ed3) (e / 2 / (d + 1)));
intros [u2 v2] [xi1 xi2];unfold uncurry;simpl in *.
rewrite (pos_split2 e). apply (triangular _ (u2 * v1)).
- apply R_lt_le in Ed2.
  pose proof (Rmult_lipschitz_aux_alt _ _ Ed2) as E1.
  apply lipschitz_uniform in E1.
  apply E1. eapply rounded_le;[exact xi1|].
  etransitivity;[apply meet_lb_r|].
  apply mult_le_compat;try solve_propholds.
  + reflexivity.
  + unfold cast;simpl. apply flip_le_dec_recip.
    * solve_propholds.
    * apply (order_preserving (+ 1)). apply lt_le;trivial.
- apply metric_to_equiv. rewrite Rmult_abs_l.
  apply R_le_lt_trans with (abs (rat (' d)) * abs (rat (' (e / 2 / (d + 1))))).
  + apply Rmult_le_compat_abs.
    * change (abs (rat (' d))) with (rat (abs (' d))).
      unfold abs at 2. rewrite (fst (abs_sig (' _)).2);[|solve_propholds].
      rewrite (Qpos_diff_pr _ _ Ed3).
      eapply Rle_close_rat;[|apply (non_expanding abs (x:=u1))].
      ** apply R_lt_le;trivial.
      ** eapply rounded_le;[exact xi1|]. apply meet_lb_l. 
    * change (abs (rat (' (e / 2 / (d + 1))))) with
        (rat (abs (' (e / 2 / (d+1))))).
      unfold abs at 2. rewrite (fst (abs_sig (' _)).2);[|solve_propholds].
      apply equiv_to_metric in xi2.
      etransitivity;[apply R_lt_le,xi2|].
      apply rat_le_preserve,meet_lb_r.
  + apply rat_lt_preserving.
    rewrite <-Qabs_mult.
    change (' d * ' (e / 2 / (d + 1))) with
      (' (d * (e / 2 / (d + 1)))).
    unfold abs;rewrite (fst (abs_sig (' _)).2);[|solve_propholds].
    assert (Hrw : e / 2 = (e / 2) * 1)
      by (apply pos_eq;ring_tac.ring_with_nat);
    rewrite Hrw;clear Hrw.
    assert (Hrw : d * (e / 2 * 1 / (d + 1)) = (e / 2) * (d / (d + 1)))
      by (apply pos_eq;ring_tac.ring_with_nat);
    rewrite Hrw;clear Hrw.
    apply pos_mult_le_lt_compat;try split;try solve_propholds.
    * reflexivity.
    * apply (strictly_order_reflecting (.* (' (d + 1)))).
      unfold cast;simpl.
      rewrite mult_1_l.
      rewrite <-mult_assoc, (mult_comm (/ _)),dec_recip_inverse,mult_1_r;
      [|apply lt_ne_flip;solve_propholds].
      apply pos_plus_le_lt_compat_r.
      ** solve_propholds.
      ** reflexivity.
Qed.
Global Existing Instance Rmult_continuous.

Instance Rmult_continuous_l : forall x : real, Continuous (x *.).
Proof.
change (forall x, Continuous (uncurry (@mult real _) ∘ (pair x))).
intros;apply continuous_compose; apply _.
Qed.

Instance real_ring@{} : Ring real.
Proof.
repeat (split;try apply _);
unfold sg_op,mon_unit,mult_is_sg_op,one_is_mon_unit;
change Rmult with mult;change R1 with one.
- hnf. apply unique_continuous_ternary_extension.
  + change (Continuous (uncurry mult ∘ map2 (@id real) (uncurry mult) ∘
      prod_assoc^-1)).
    (* Why does [apply _] not work here? *)
    repeat apply continuous_compose; apply _.
  + change (Continuous (uncurry mult ∘ map2 (uncurry mult) (@id real))).
    apply _.
  + intros. change (rat (q * (r * s)) = rat (q * r * s)). apply (ap rat).
    apply associativity.
- hnf. apply (unique_continuous_extension _ _ _).
  intros;apply (ap rat),left_identity.
- hnf. apply (unique_continuous_extension _ _ _).
  intros;apply (ap rat),right_identity.
- hnf. apply unique_continuous_binary_extension.
  + apply _.
  + change (Continuous (uncurry (@mult real _) ∘ prod_symm)). apply _.
  + intros;apply (ap rat),commutativity.
- hnf. apply unique_continuous_ternary_extension.
  + change (Continuous (uncurry mult ∘ map2 (@id real) (uncurry plus) ∘
      prod_assoc^-1)).
    apply _.
  + change (Continuous (uncurry (@plus real _) ∘
      map2 (uncurry mult) (uncurry mult) ∘
      map2 id prod_symm ∘ prod_assoc^-1 ∘ prod_symm ∘ map2 id prod_assoc ∘
      prod_assoc^-1 ∘ map2 BinaryDup id ∘ prod_assoc^-1)).
    repeat apply continuous_compose;apply _.
  + intros;change (rat (q * (r + s)) = rat (q * r + q * s));
    apply (ap rat),distribute_l.
Qed.

Lemma Rlt_exists_pos_plus_le@{} : forall x y : real, x < y ->
  merely (exists e : Q+, x + rat (' e) <= y).
Proof.
intros x y;apply (Trunc_ind _). intros [q [r [E1 [E2 E3]]]].
apply tr. exists (Qpos_diff _ _ E2).
transitivity (rat r);trivial.
set (d := Qpos_diff _ _ E2). rewrite (Qpos_diff_pr _ _ E2). unfold d;clear d.
change (rat (q + ' Qpos_diff q r E2)) with (rat q + rat (' Qpos_diff q r E2)).
rewrite 2!(plus_comm _ (rat (' _))).
apply (order_preserving (_ +)). trivial.
Qed.

Lemma Rle_close@{} : forall e u v, close e u v ->
  v <= u + rat (' e).
Proof.
intros e u v xi.
apply (order_reflecting ((- u) +)).
rewrite plus_assoc,plus_negate_l,plus_0_l.
apply equiv_to_metric in xi.
transitivity (abs (u - v));[|apply R_lt_le,xi].
rewrite <-Rabs_neg. rewrite <-negate_swap_l. apply Rabs_le_raw.
Qed.

Lemma Rlt_plus_pos@{} : forall x (e : Q+), x < x + rat (' e).
Proof.
apply (C_ind0 _ (fun x => forall e, _)).
- intros;apply rat_lt_preserving. apply pos_plus_lt_compat_r.
  solve_propholds.
- intros x IHx e.
  pose proof (fun a b c => Rlt_close_plus _ _ (IHx _ b) _ _ (equiv_lim _ _ c a))
    as E1.
  pose proof (fun a b c => cotransitive (E1 a b c) (lim x + (rat (' e)))) as E2.
  pose proof (fun a b => Rle_close _ _ _ (symmetry _ _ (equiv_lim _ x a b))) as E3.
  (* in the second branch of cotransitive,
     forall n : Q+, lim x + rat e < x a + a + n' <= lim x + 2a + n
     where a = E2.a + E3.b
     and n = E2.b + E2.c + E3.a *)
  apply (merely_destruct (E2 (e/3) (e/3/3) (e/3/3))).
  intros [E4|E4].
  + trivial.
  + pose proof (E3 (e/3/3) (e/3)) as E5.
    rewrite <-plus_assoc in E4.
    pose proof (Rplus_le_preserving
      (rat (' (e / 3 / 3)) + rat (' (e / 3 / 3 + e / 3))) _ _ E5) as E6.
    rewrite (plus_comm _ (x _)) in E6.
    pose proof (R_lt_le_trans _ _ _ E4 E6) as E7.
    set (d := e/3) in E7.
    assert (Hrw : rat (' (e / 3 / 3)) + rat (' (e / 3 / 3 + e / 3)) +
      (lim x + rat (' (e / 3 / 3 + e / 3)))
      = lim x + rat (' (d + d + ((d/3 + d/3 + d/3))))).
    { path_via (lim x + (rat (' (e / 3 / 3)) + rat (' (e / 3 / 3 + e / 3))
        + rat (' (e / 3 / 3 + e / 3)))).
      { abstract ring_tac.ring_with_nat. }
      { apply ap. apply (ap rat).
        unfold d;abstract ring_tac.ring_with_nat. }
    }
    rewrite Hrw in E7;clear Hrw.
    unfold d in E7;rewrite <-!pos_split3 in E7.
    destruct (irreflexivity lt _ E7).
Qed.

Instance Rplus_lt_preserving@{} : ∀ z : real, StrictlyOrderPreserving (z +).
Proof.
intros z x y E1. apply (merely_destruct (Rlt_exists_pos_plus_le _ _ E1)).
intros [e E2].
apply R_lt_le_trans with (z + x + rat (' e)).
- apply Rlt_plus_pos.
- rewrite <-plus_assoc. apply (order_preserving (z +)). trivial.
Qed.

Instance Rmult_nonneg_compat : ∀ x y : real, PropHolds (0 ≤ x) →
  PropHolds (0 ≤ y) →
  PropHolds (0 ≤ x * y).
Proof.
unfold PropHolds.
intros x y E1 E2;rewrite <-E1,<-E2;clear E1 E2.
revert x y;apply unique_continuous_binary_extension.
- change (Continuous ((join 0) ∘ uncurry (@mult real _) ∘ map2 (join 0) (join 0))).
  repeat apply continuous_compose;apply _.
- change (Continuous (uncurry (@mult real _) ∘ (map2 (join 0) (join 0)))).
  apply _.
- intros. change (rat (0 ⊔ (0 ⊔ q) * (0 ⊔ r)) = rat ((0 ⊔ q) * (0 ⊔ r))).
  apply ap. apply join_r.
  apply nonneg_mult_compat;apply join_ub_l.
Qed.

Instance real_srorder : SemiRingOrder Rle.
Proof.
apply from_ring_order;apply _.
Qed.

Instance real_strict_srorder : StrictSemiRingOrder Rlt.
Proof.
eapply @from_strict_ring_order;try apply _;[split;apply _|].
unfold PropHolds.
intros x y E1 E2.
apply (merely_destruct (Rlt_exists_pos_plus_le _ _ E1));intros [e1 E1'].
apply (merely_destruct (Rlt_exists_pos_plus_le _ _ E2));intros [e2 E2'].
apply R_lt_le_trans with (rat (' (e1 * e2))).
- apply rat_lt_preserving;solve_propholds.
- rewrite plus_0_l in E1';rewrite plus_0_l in E2'.
  change (rat (' (e1 * e2))) with (rat (' e1) * rat (' e2)).
  apply mult_le_compat;trivial;apply rat_le_preserve;solve_propholds.
Qed.

Lemma Rjoin_plus_r : forall a b c : real, join a b + c = join (a+c) (b+c).
Proof.
apply unique_continuous_ternary_extension.
- change (Continuous (uncurry (@plus real _) ∘ map2 (uncurry join) id)).
  apply _.
- change (Continuous (uncurry (@join real _) ∘ map2
      (uncurry plus ∘ map2 fst id)
      (uncurry plus ∘ map2 snd id) ∘
    BinaryDup)).
  apply _.
- intros q r s. change (rat (q ⊔ r + s) = rat ((q + s) ⊔ (r + s))). apply (ap rat).
  destruct (total le q r) as [E|E].
  + rewrite join_r;trivial.
    rewrite join_r;trivial.
    apply (order_preserving (+ s));trivial.
  + rewrite join_l;trivial.
    rewrite join_l;trivial.
    apply (order_preserving (+ s));trivial.
Qed.

Lemma Rlt_join : forall a b c : real, a < c -> b < c ->
  join a b < c.
Proof.
intros a b c E1 E2.
apply (merely_destruct (Rlt_exists_pos_plus_le _ _ E1));intros [e1 E1'].
apply (merely_destruct (Rlt_exists_pos_plus_le _ _ E2));intros [e2 E2'].
destruct (Qpos_lt_min e1 e2) as [n [n1 [n2 [En1 En2]]]].
apply R_lt_le_trans with (join a b + rat (' n));[apply Rlt_plus_pos|].
rewrite Rjoin_plus_r. apply join_le.
- etransitivity;[|exact E1'].
  apply (order_preserving (a +)),rat_le_preserve. rewrite En1.
  unfold cast at 2;simpl.
  apply nonneg_plus_le_compat_r. solve_propholds.
- etransitivity;[|exact E2'].
  apply (order_preserving (b +)),rat_le_preserve. rewrite En2.
  unfold cast at 2;simpl.
  apply nonneg_plus_le_compat_r. solve_propholds.
Qed.

Lemma from_below_is_approx (x : real) :
  ∀ d e : Q+, close (d + e) (x - rat (' d)) (x - rat (' e)).
Proof.
intros;apply metric_to_equiv.
assert (Hrw : (x - rat (' d) - (x - rat (' e))) =
  rat (' e) - rat (' d))
  by ring_tac.ring_with_integers (NatPair.Z nat).
rewrite Hrw;clear Hrw.
change (rat (abs (' e - ' d)) < rat (' (d + e))).
apply rat_lt_preserving.
destruct (total le (' e) (' d)) as [E|E].
- rewrite <-Qabs_neg, Qabs_of_nonneg
    by (apply flip_nonpos_negate,(snd (flip_nonpos_minus _ _)),E).
  rewrite <-negate_swap_r. apply (strictly_order_preserving ((' d) +)).
  apply between_pos. solve_propholds.
- rewrite Qabs_of_nonneg
    by (apply (snd (flip_nonneg_minus _ _)),E).
  rewrite plus_comm. apply (strictly_order_preserving (+ (' e))).
  apply between_pos. solve_propholds.
Qed.

Definition from_below (x : real) : Approximation real.
Proof.
exists (fun e => x - rat (' e)).
apply from_below_is_approx.
Defined.

Lemma from_below_pr : forall x, lim (from_below x) = x.
Proof.
intros. apply equiv_path. intros.
rewrite (pos_split2 e).
eapply (triangular _);[rewrite (pos_split2 (e/2));Symmetry;apply (equiv_lim _)|].
simpl. apply metric_to_equiv.
assert (Hrw : (x - rat (' (e / 2 / 2)) - x) = - (rat (' (e / 2 / 2))))
  by ring_tac.ring_with_integers (NatPair.Z nat).
rewrite Hrw;clear Hrw.
rewrite Rabs_neg.
apply rat_lt_preserving.
rewrite Qabs_of_nonneg by solve_propholds.
set (n := e / 2);clearbody n;clear e.
set (k := n / 2);rewrite (pos_split2 n).
fold k. clearbody k;clear n.
apply pos_plus_lt_compat_r. solve_propholds.
Qed.

Definition lipschitz_approx (f : real -> real) L
  `{!Lipschitz f L}
  (x : Approximation real)
  : Approximation real.
Proof.
exists (fun e => f (x (e / L))).
intros.
rewrite <-(pos_unconjugate L (d + e)),<-Qpos_mult_assoc.
apply (lipschitz f L).
assert (Hrw : ((d + e) / L) = d / L + e / L)
  by (apply pos_eq,plus_mult_distr_r);
rewrite Hrw;clear Hrw.
apply approx_equiv.
Defined.

Lemma lipschitz_approx_lim (f:real -> real) L `{!Lipschitz f L} x
  : f (lim x) = lim (lipschitz_approx f L x).
Proof.
apply equiv_path. intros.
rewrite (pos_split2 e).
eapply triangular;[|rewrite (pos_split2 (e/2));apply (equiv_lim _)].
simpl. set (N := e / 2 / 2 / L).
rewrite <-(pos_unconjugate L (e / 2)),<-Qpos_mult_assoc.
apply (lipschitz f L).
Symmetry. rewrite (pos_split2 (e / 2 / L)).
assert (Hrw : e / 2 / L / 2 = N)
  by (unfold N;apply pos_eq;ring_tac.ring_with_nat).
rewrite Hrw;clear Hrw.
apply (equiv_lim _).
Qed.

Lemma approx_eq : forall x y : Approximation real,
  approximate x = approximate y -> x = y.
Proof.
intros [x Ex] [y Ey];simpl;intros E.
destruct E. apply ap. apply path_ishprop.
Qed.

Lemma Rjoin_0_not_neg : forall x, (forall e : Q+, - rat (' e) < x) -> join 0 x = x.
Proof.
intros x E.
rewrite <-(from_below_pr 0).
rewrite (lipschitz_approx_lim (⊔ x) 1 (from_below 0)).
path_via (lim (const_approx _ x));[|apply lim_cons].
apply ap, approx_eq, path_forall;intros e.
simpl. apply join_r.
rewrite plus_0_l. apply R_lt_le;trivial.
Qed.

Lemma R_not_lt_le_flip : forall x y : real, ~ x < y -> y <= x.
Proof.
intros x y E.
apply flip_nonneg_minus.
apply Rjoin_0_not_neg.
intros. apply flip_lt_minus_r.
rewrite plus_comm.
assert (E1 : y - rat (' e) < y).
{ apply (strictly_order_reflecting (+ (rat (' e)))).
  rewrite <-plus_assoc,plus_negate_l,plus_0_r. apply Rlt_plus_pos. }
apply (merely_destruct (cotransitive E1 x));intros [E2|E2];trivial.
destruct (E E2).
Qed.

Instance real_full_pseudo_order@{} : FullPseudoOrder Rle Rlt.
Proof.
(* Avoid splitting iffs *)
repeat (split;try (revert x; fail 1);try apply _).
- hnf. unfold apart;simpl. intros ??. apply Sum.equiv_sum_symm.
- intros x y;split.
  + intros E.
    apply (antisymmetry le);apply R_not_lt_le_flip;intros E';apply E;hnf;auto.
  + intros [] [E|E];apply (irreflexivity _ _ E).
- apply lt_antisym.
- intros x y;split;intros E;exact E.
- intros x y;split.
  + intros E1 E2. apply (irreflexivity lt x).
    apply R_le_lt_trans with y;trivial.
  + apply R_not_lt_le_flip.
Qed.

Global Instance real_isapart : IsApart real.
Proof.
apply pseudo_order_apart.
Qed.

Lemma Rabs_triangle_alt : forall x y : real, abs (abs x - abs y) <= abs (x - y).
Proof.
intros x y.
apply R_not_lt_le_flip.
intros E. apply (merely_destruct (R_archimedean_pos _ _ (Rabs_nonneg _) E)).
intros [e [E1 E2]].
apply metric_to_equiv in E1. apply (non_expanding abs) in E1.
apply equiv_to_metric in E1.
apply (irreflexivity lt (rat (' e))).
etransitivity;eauto.
Qed.

Lemma apart_to_metric : forall x y : real, apart x y -> 0 < abs (x - y).
Proof.
intros x y [E|E];apply flip_pos_minus in E.
- rewrite <-Rabs_neg,<-negate_swap_r. rewrite Rabs_of_nonneg;trivial.
  apply R_lt_le;trivial.
- rewrite Rabs_of_nonneg;trivial.
  apply R_lt_le;trivial.
Qed.

Lemma Rlt_join_either : forall a b c, a < join b c -> hor (a < b) (a < c).
Proof.
intros a b c;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
apply (merely_destruct (cotransitive (rat_lt_preserving _ _ E2) b)).
intros [E4|E4].
- apply tr;left;apply R_le_lt_trans with (rat q);trivial.
- apply (merely_destruct (cotransitive (rat_lt_preserving _ _ E2) c)).
  intros [E5|E5].
  + apply tr;right;apply R_le_lt_trans with (rat q);trivial.
  + pose proof (Rlt_join _ _ _ E4 E5) as E6.
    destruct (irreflexivity lt (rat r)).
    apply R_le_lt_trans with (join b c);trivial.
Qed.

Lemma Rlt_join_l : forall a b, a < join a b -> a < b.
Proof.
intros a b E;apply (merely_destruct (Rlt_join_either _ _ _ E));
intros [E1|E1];trivial.
destruct (irreflexivity lt _ E1).
Qed.

Lemma Rlt_join_r : forall a b, b < join a b -> b < a.
Proof.
intros a b E;apply (merely_destruct (Rlt_join_either _ _ _ E));
intros [E1|E1];trivial.
destruct (irreflexivity lt _ E1).
Qed.

Lemma metric_to_apart : forall x y : real, 0 < abs (x - y) ->
  apart x y.
Proof.
intros x y E.
rewrite Rabs_is_join in E. apply (merely_destruct (Rlt_join_either _ _ _ E)).
intros [E1|E1].
- rewrite <-negate_swap_r in E1. apply flip_pos_minus in E1. left;trivial.
- apply flip_pos_minus in E1. right;trivial.
Qed.

Instance Rabs_strong_ext : StrongExtensionality (abs (A:=real)).
Proof.
intros x y E.
apply metric_to_apart.
eapply R_lt_le_trans;[|apply Rabs_triangle_alt].
apply apart_to_metric in E. trivial.
Qed.

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
    Ularge UQ UQ Uhuge Ularge
    UQ} _ pos_back _).
- intros s. exact (Qpos_upper_recip s.1 s.2.1).
- simpl. exact Qpos_upper_recip_respects.
Defined.

Lemma R_pos_recip_rat : forall q (Eq : 0 < rat q),
  R_pos_recip (existT _ (rat q) Eq) = rat (/ q).
Proof.
intros q Eq. unfold R_pos_recip.
unfold jections.surjective_factor,jections.surjective_factor_aux.
revert Eq. apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
simpl. apply (ap rat). unfold compose;simpl.
apply ap. apply join_l.
unfold cast;simpl. apply rat_le_reflecting;trivial.
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
  Symmetry;apply involutive.
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

Lemma Rmult_pos_decompose_nonneg : forall x y, 0 <= x ->
  0 < x * y ->
  0 < y.
Proof.
intros x y E1 E2.
assert (E3 : merely (exists e : Q+, rat (' e) < x * y)).
{ apply (merely_destruct (Rlt_exists_pos_plus_le _ _ E2)). intros [e E3].
  apply tr;exists (e/2). apply R_lt_le_trans with (0 + rat (' e));trivial.
  rewrite (plus_0_l (R:=real)).
  apply rat_lt_preserving. set (n:=e/2). rewrite (pos_split2 e).
  apply pos_plus_lt_compat_r. solve_propholds.
}
revert E3;apply (Trunc_ind _);intros [e E3].
apply (merely_destruct (R_Qpos_bounded x)). intros [n E4].
apply R_lt_le_trans with (rat (' (e/n)));[apply rat_lt_preserving;solve_propholds|].
apply R_not_lt_le_flip. intros E5.
apply (irreflexivity lt (rat (' e))).
eapply R_lt_le_trans;[apply E3|].
rewrite <-(pos_unconjugate n e). rewrite <-Qpos_mult_assoc.
change (x * y <= rat (' n) * rat (' (e / n))).
apply mult_le_compat;trivial.
- apply R_not_lt_le_flip;intros E6.
  apply (irreflexivity lt 0).
  apply R_lt_le_trans with (x * y);trivial.
  apply nonneg_nonpos_mult;trivial. apply R_lt_le;trivial.
- transitivity (abs x).
  + apply Rabs_le_raw.
  + apply R_lt_le;trivial.
- apply R_lt_le;trivial.
Qed.

Lemma Rabs_mult : forall x y : real, abs (x * y) = abs x * abs y.
Proof.
apply unique_continuous_binary_extension.
- change (Continuous (abs ∘ uncurry (@mult real _)));apply _.
- change (Continuous (uncurry (@mult real _) ∘ map2 abs abs));apply _.
- intros. change (rat (abs (q * r)) = rat (abs q * abs r)).
  exact (ap rat (Qabs_mult q r)).
Qed.

Lemma Rmult_lt_apart : forall z x y, z * x < z * y -> apart x y.
Proof.
intros z x y E.
Symmetry.
apply metric_to_apart.
apply Rmult_pos_decompose_nonneg with (abs z);[apply Rabs_nonneg|].
rewrite <-Rabs_mult.
apply R_lt_le_trans with (z * (y - x));[|apply Rabs_le_raw].
rewrite plus_mult_distr_l,<-negate_mult_distr_r.
apply (snd (flip_pos_minus _ _)).
trivial.
Qed.

Global Instance real_full_pseudo_srorder : FullPseudoSemiRingOrder Rle Rlt.
Proof.
apply from_full_pseudo_ring_order;try apply _.
apply @apartness.strong_binary_setoid_morphism_commutative;try apply _.
intros z x y [E|E];apply Rmult_lt_apart in E;trivial;Symmetry;trivial.
Qed.

Global Instance real_field : Field real.
Proof.
split;try apply _.
apply R_recip_inverse.
Qed.

Definition Rplus_lim_val : Approximation real -> real -> Approximation real.
Proof.
intros x y. exists (fun e => x e + y).
intros e d.
apply (non_expanding (fun a => a + y)).
apply approx_equiv.
Defined.

Definition Rplus_lim_compute : forall x y, lim x + y = lim (Rplus_lim_val x y).
Proof.
intros x y. unfold plus,Rplus.
rewrite lipschitz_extend_binary_lim. apply (ap lim).
apply approx_eq,path_forall;intros e;simpl.
rewrite Qpos_recip_1,Qpos_mult_1_r. reflexivity.
Qed.

Definition Rabs_lim_val : Approximation real -> Approximation real.
Proof.
intros x. exists (fun e => abs (x e)).
intros. apply (non_expanding _). apply approx_equiv.
Defined.

Definition Rabs_lim_compute@{} : forall x, abs (lim x) = lim (Rabs_lim_val x).
Proof.
intros. unfold abs;simpl;unfold Rabs_val;simpl.
apply (ap lim);apply approx_eq, path_forall; intros e;
change (abs (x (e / 1)) = abs (x e)). apply ap,ap.
path_via (1 * e / 1);[|apply pos_unconjugate].
rewrite Qpos_mult_1_l. trivial.
Qed.

Section real_initial.

Context `{Field F} `{!FullPseudoSemiRingOrder (A:=F) Fle Flt}.

Variable F_archimedean : forall x y : F, x < y ->
  merely (exists q, x < rationals_to_field Q F q < y).

Instance Fclose : Closeness F := fun e x y =>
  x - y < rationals_to_field Q F (' e) /\ y - x < rationals_to_field Q F (' e).

Instance rat_to_field_strict_order_embedding
  : StrictOrderEmbedding (rationals_to_field Q F).
Proof.
Admitted.

Lemma F_separated : Separated F.
Proof.
intros x y E.
apply (right_cancellation (+) (-y)). rewrite plus_negate_r.
apply tight_apart. intros E'. apply apart_iff_total_lt in E'.
destruct E' as [E'|E'];apply F_archimedean in E';revert E';apply (Trunc_ind _);
intros [q [E1 E2]].
- assert (Eq : 0 < - q).
  { rewrite <-(preserves_0 (f:=rationals_to_field Q F)) in E2.
    apply (strictly_order_reflecting _) in E2.
    apply flip_neg_negate. trivial.
  }
  pose proof (E (mkQpos _ Eq)) as [E3 E4];unfold cast in E3,E4;simpl in E3, E4.
  rewrite (preserves_negate (f:=rationals_to_field Q F)) in E4.
  apply flip_lt_negate in E4;rewrite involutive,<-negate_swap_r in E4.
  apply (irreflexivity lt (x - y)). transitivity (rationals_to_field Q F q);trivial.
- assert (Eq : 0 < q).
  { apply (strictly_order_reflecting _). rewrite preserves_0. trivial. }
  pose proof (E (mkQpos _ Eq)) as [E3 E4];unfold cast in E3,E4;simpl in E3, E4.
  apply (irreflexivity lt (x - y)). transitivity (rationals_to_field Q F q);trivial.
Qed.

Lemma pos_gt_both : forall a b : Q, forall e, a < ' e -> b < ' e ->
  exists d d', a < ' d /\ b < ' d /\ e = d + d'.
Proof.
Admitted.

Instance F_premetric : PreMetric F.
Proof.
split.
- apply _.
- intros e x. hnf. rewrite plus_negate_r.
  split;rewrite <-(preserves_0 (f:=rationals_to_field Q F));
  apply (strictly_order_preserving _);solve_propholds.
- intros e x y E. hnf. apply prod_symm,E.
- apply F_separated.
- intros x y z e d E1 E2.
  hnf. rewrite (preserves_plus (f:=_:Q -> F)).
  split.
  + assert (Hrw : x - z = (x - y) + (y - z))
      by ring_tac.ring_with_integers (NatPair.Z nat);
    rewrite Hrw;clear Hrw. apply plus_lt_compat.
    * apply E1.
    * apply E2.
  + assert (Hrw : z - x = (y - x) + (z - y))
      by ring_tac.ring_with_integers (NatPair.Z nat);
    rewrite Hrw;clear Hrw. apply plus_lt_compat.
    * apply E1.
    * apply E2.
- hnf. intros e x y. split.
  + intros [E1 E2].
    apply F_archimedean in E1;apply F_archimedean in E2.
    revert E1;apply (Trunc_ind _);intros [q1 [E1 E1']];
    revert E2;apply (Trunc_ind _);intros [q2 [E2 E2']].
    apply (strictly_order_reflecting _) in E1';
    apply (strictly_order_reflecting _) in E2'.
    assert (E3 : exists d d', q1 < ' d /\ q2 < ' d /\ e = d + d').
    { apply pos_gt_both;trivial. }
    destruct E3 as [d [d' [E3 [E4 E5]]]].
    apply tr;exists d,d';split;trivial.
    hnf. split;etransitivity;eauto;apply (strictly_order_preserving _);trivial.
  + apply (Trunc_ind _);intros [d [d' [E1 [E2 E3]]]].
    assert (rationals_to_field Q F (' d) < rationals_to_field Q F (' e))
      by (apply (strictly_order_preserving _); rewrite E1;
          apply pos_plus_lt_compat_r; solve_propholds).
    split;etransitivity;eauto.
Qed.

Context `{!Lim F} `{!CauchyComplete F}.

Definition real_embed : real -> F.
Proof.
simple refine (lipschitz_extend Q (rationals_to_field Q F) 1);try apply _.
apply nonexpanding_lipschitz.
hnf. intros e q r [E1 E2].
hnf. rewrite <-!preserves_negate,<-!preserves_plus.
apply flip_lt_negate in E1. rewrite involutive,<-negate_swap_r in E1.
split;apply (strictly_order_preserving _);trivial.
Defined.

Definition real_embed_rat q : real_embed (rat q) = rationals_to_field Q F q
  := idpath.

Instance real_embed_sr_mor : SemiRingPreserving real_embed.
Proof.
split;split;hnf.
- intros x;apply (unique_continuous_extension _).
  { apply _. }
  { (* need plus, mult continuous on F *)
Abort.

End real_initial.



