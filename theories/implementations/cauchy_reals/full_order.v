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
  HoTTClasses.implementations.cauchy_reals.ring.

Local Set Universe Minimization ToSet.

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
  apply mult_le_compat;trivial;apply rat_le_preserving;solve_propholds.
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
  apply (order_preserving (a +)),rat_le_preserving. rewrite En1.
  unfold cast at 2;simpl.
  apply nonneg_plus_le_compat_r. solve_propholds.
- etransitivity;[|exact E2'].
  apply (order_preserving (b +)),rat_le_preserving. rewrite En2.
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
eapply (triangular _);[rewrite (pos_split2 (e/2));symmetry;apply (equiv_lim _)|].
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
symmetry. rewrite (pos_split2 (e / 2 / L)).
assert (Hrw : e / 2 / L / 2 = N)
  by (unfold N;apply pos_eq;ring_tac.ring_with_nat).
rewrite Hrw;clear Hrw.
apply (equiv_lim _).
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
