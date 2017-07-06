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
  HoTTClasses.IR.cauchy_reals.base
  HoTTClasses.IR.cauchy_reals.abs
  HoTTClasses.IR.cauchy_reals.order.

Local Set Universe Minimization ToSet.

Lemma equiv_0_metric' : forall e u, close e u 0 -> abs u < rat (' e).
Proof.
intros e u;revert u e;apply (C_ind0 _ (fun u => forall e, _ -> _)).
- intros q e E.
  rewrite (equiv_eta_eta_def _) in E. apply Qclose_alt in E.
  rewrite negate_0,plus_0_r in E.
  apply rat_lt_preserving. trivial.
- intros x IH e xi.
  apply rounded in xi. revert xi.
  apply (Trunc_ind _);intros [d [d' [He xi]]].
  rewrite (equiv_lim_eta_def _) in xi.
  revert xi;apply (Trunc_ind _);intros [n [n' [Hd E1]]].
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
rewrite <-(Rabs_of_0' (v - v));[|apply right_inverse].
apply (non_expanding (fun w => abs (w - v))). trivial.
Qed.

Lemma metric_to_equiv_rat_lim@{} (q : Q)
  (y : Approximation real)
  (IHy : forall e e0 : Q+, abs (rat q - y e) < rat (' e0) -> close e0 (rat q) (y e))
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

Lemma metric_to_equiv_lim_lim@{} (x : Approximation real)
  (IHx : forall (e : Q+) (v : real) (e0 : Q+),
        abs (x e - v) < rat (' e0) -> close e0 (x e) v)
  (y : Approximation real)
  (IHy : forall e e0 : Q+, abs (lim x - y e) < rat (' e0) -> close e0 (lim x) (y e))
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

Definition equiv_metric_rw@{} := equiv_metric_rw'.
