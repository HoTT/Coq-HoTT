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
  HoTTClasses.implementations.cauchy_reals.base.

Local Set Universe Minimization ToSet.

Lemma Rle_close_rat_rat' : forall q v e, close e (rat q) v ->
  v <= rat (q + ' e).
Proof.
intros q.
apply (C_ind0 _ (fun v => forall e, _ -> _)).
+ intros s e E'.
  rewrite (equiv_eta_eta_def _) in E'.
  hnf in E'. apply (order_preserving rat).
  rewrite plus_comm. apply flip_le_minus_l.
  apply flip_le_negate. rewrite <-negate_swap_r. apply lt_le,E'.
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

Lemma Rle_close_rat@{} : forall q u, u <= rat q -> forall v e, close e u v ->
  v <= rat (q + ' e).
Proof.
intros q u E v e xi.
pose proof (non_expanding (join (rat q)) xi) as E1.
hnf in E. rewrite Rjoin_comm in E1.
rewrite E in E1.
apply Rle_close_rat_rat in E1.
transitivity (join (rat q) v);trivial.
apply join_ub_r.
Qed.

Lemma Rlt_close_rat_plus@{} : forall u q, u < rat q ->
  forall v e, close e u v -> v < rat (q + ' e).
Proof.
intros u q E;apply R_archimedean in E;revert E;
apply (Trunc_ind (fun _ => forall v e, _ -> _)).
intros [r [E1 E2]] v e xi.
apply R_lt_le in E1. pose proof (Rle_close_rat _ _ E1 _ _ xi) as E3.
apply R_le_lt_trans with (rat (r + ' e));trivial.
apply rat_lt_preserving. apply rat_lt_reflecting in E2.
apply (strictly_order_preserving (+ (' e))). trivial.
Qed.

Lemma Rlt_close_plus@{} : forall u v, u < v ->
  forall w e, close e u w -> w < v + rat (' e).
Proof.
intros u v E w e xi;apply R_archimedean in E;revert E;apply (Trunc_ind _);
intros [q [E1 E2]].
apply R_lt_le_trans with (rat (q + ' e)).
- apply Rlt_close_rat_plus with u;trivial.
- rewrite plus_comm. rewrite Rplus_comm.
  change (rat (' e) + rat q <= rat (' e) + v).
  apply (order_preserving (rat (' e) +)),R_lt_le;trivial.
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
