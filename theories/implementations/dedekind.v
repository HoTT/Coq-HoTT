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
  HoTTClasses.theory.lattices
  HoTTClasses.orders.lattices
  HoTTClasses.theory.additional_operations
  HoTTClasses.theory.premetric
  HoTTClasses.implementations.partiality
  HoTTClasses.implementations.sierpinsky.

Local Set Universe Minimization ToSet.

Definition QPred : Type@{UQ} := Q -> Sier.

Section iscut_def.
Variables (lower upper : QPred).

Class IsCut@{} : Type@{UQ} :=
  { iscut_lower_inhab : merely@{UQ} (exists q, lower q)
  ; iscut_upper_inhab : merely@{UQ} (exists q, upper q)
  ; iscut_lower_rounded : forall q, iff@{Set UQ UQ} (lower q)
    (merely (exists r, q < r /\ lower r))
  ; iscut_upper_rounded : forall r, iff@{Set UQ UQ} (upper r)
    (merely (exists q, q < r /\ upper q))
  ; iscut_cut_disjoint : forall q, lower q -> upper q -> Empty
  ; iscut_cut_located : forall q r, q < r -> hor (lower q) (upper r) }.
End iscut_def.

Record Cut@{} :=
  { lower : QPred
  ; upper : QPred
  ; cut_iscut : IsCut lower upper }.
Global Existing Instance cut_iscut.

Definition lower_inhab (c : Cut) := iscut_lower_inhab (lower c) _.
Definition upper_inhab (c : Cut) := iscut_upper_inhab (lower c) _.
Definition lower_rounded (c : Cut) := iscut_lower_rounded (lower c) _.
Definition upper_rounded (c : Cut) := iscut_upper_rounded (lower c) _.
Definition cut_disjoint (c : Cut) := iscut_cut_disjoint (lower c) _.
Definition cut_located (c : Cut) := iscut_cut_located (lower c) _.

Lemma lower_le : forall a q r, lower a q -> r <= q -> lower a r.
Proof.
intros a q r E1 E2.
destruct (le_or_lt q r) as [E3|E3].
- destruct (antisymmetry le _ _ E2 E3);trivial.
- apply lower_rounded. apply tr. exists q;auto.
Qed.

Lemma upper_le : forall a q r, upper a q -> q <= r -> upper a r.
Proof.
intros a q r E1 E2.
destruct (le_or_lt r q) as [E3|E3].
- destruct (antisymmetry le _ _ E2 E3);trivial.
- apply upper_rounded. apply tr. exists q;auto.
Qed.

Definition IsCut_conjunction l u : IsCut l u -> _
  := fun c => (iscut_lower_inhab l u, iscut_upper_inhab l u,
    iscut_lower_rounded l u, iscut_upper_rounded l u,
    iscut_cut_disjoint l u, iscut_cut_located l u).

Global Instance iscut_conj_isequiv {l u}
  : IsEquiv@{UQ UQ} (IsCut_conjunction@{UQ UQ} l u).
Proof.
simple refine (BuildIsEquiv _ _ _ _ _ _ _).
- intros E;split;apply E.
- red;simpl. intros [[[[[? ?] ?] ?] ?] ?]. reflexivity.
- red;simpl. reflexivity.
- simpl. reflexivity.
Defined.

Section contents.
Context `{Funext} `{Univalence}.

Global Instance IsCut_hprop : forall l u, IsHProp (IsCut l u).
Proof.
intros. apply (@trunc_equiv _ _ ((IsCut_conjunction l u)^-1) _ _ _).
Qed.

Lemma cut_eq0 : forall a b : Cut, lower a = lower b -> upper a = upper b ->
  a = b.
Proof.
intros [la ua Ea] [lb ub Eb];simpl;intros E1 E2;destruct E1,E2;apply ap.
apply path_ishprop.
Qed.

Instance cut_isset : IsHSet Cut.
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => lower a = lower b /\ upper a = upper b)).
- intros a;split;reflexivity.
- apply _.
- intros a b E;apply cut_eq0;apply E.
Qed.

Lemma cut_eq : forall a b : Cut, (forall q, lower a q <-> lower b q) ->
  (forall r, upper a r <-> upper b r) ->
  a = b.
Proof.
intros a b E1 E2;apply cut_eq0;apply path_forall;intros q;apply (antisymmetry le);
apply imply_le;(apply E1 || apply E2).
Qed.

Lemma cut_orders : forall (c : Cut) (q r : Q), lower c q -> upper c r -> q < r.
Proof.
intros c q r E1 E2.
destruct (le_or_lt r q) as [E|E];trivial.
destruct (cut_disjoint c q);trivial.
apply upper_le with r;trivial.
Qed.

Lemma cut_bounds : forall (c : Cut) (e : Q+),
  merely (exists q r, r - q < ' e /\ lower c q /\ upper c r).
Proof.
intros c e.
generalize (lower_inhab c);apply (Trunc_ind _);intros [q Eq].
generalize (upper_inhab c);apply (Trunc_ind _);intros [r Er].
Abort.

Global Instance CutLe : Le Cut
  := fun a b => forall q, lower a q -> lower b q.
Arguments CutLe _ _ /.

Lemma CutLe_upper : forall a b : Cut, a <= b <-> (forall r, upper b r -> upper a r).
Proof.
unfold le;simpl;intros a b;split.
- intros E r E1.
  apply upper_rounded in E1;revert E1;apply (Trunc_ind _);intros [q [E1 E2]].
  generalize (cut_located a _ _ E1). apply (Trunc_ind _);intros [E3|E3].
  + apply E in E3. destruct (cut_disjoint _ _ E3 E2).
  + trivial.
- intros E q E1.
  apply lower_rounded in E1;revert E1;apply (Trunc_ind _);intros [r [E1 E2]].
  generalize (cut_located b _ _ E1);apply (Trunc_ind _);intros [E3|E3].
  + trivial.
  + apply E in E3. destruct (cut_disjoint _ _ E2 E3).
Qed.

Instance CutLe_partial_order : PartialOrder CutLe.
Proof.
repeat split.
- apply _.
- apply _.
- intros a q;trivial.
- intros a b c E1 E2 q E3. auto.
- intros a b E1 E2. apply cut_eq.
  + intros;split;(apply E1 || apply E2).
  + intros;split;apply CutLe_upper;trivial.
Qed.

Global Instance CutLt : Lt Cut :=
  fun a b => merely (exists q, upper a q /\ lower b q).
Arguments CutLt _ _ /.

Global Instance CutApart : Apart Cut
  := fun a b => a < b \/ b < a.
Arguments CutApart _ _ /.

Instance CutLt_strict_order : StrictOrder CutLt.
Proof.
repeat split.
- apply _.
- intros a;hnf;apply (Trunc_ind _);intros [q [E1 E2]].
  revert E2 E1;apply cut_disjoint.
- intros a b c E E';revert E; apply (Trunc_ind _);intros [q [E1 E2]];
  revert E';apply (Trunc_ind _);intros [r [E3 E4]].
  apply tr;exists q. split.
  + trivial.
  + apply lower_le with r;trivial.
    apply lt_le;apply cut_orders with b;trivial.
Qed.

Instance QIsCut : forall q : Q,
  IsCut (fun r => DecSier (r < q)) (fun r => DecSier (q < r)).
Proof.
intros q;split.
- apply tr;exists (q - 1);apply dec_sier_pr.
  apply flip_lt_minus_l. apply pos_plus_lt_compat_r;solve_propholds.
- apply tr;exists (q + 1);apply dec_sier_pr.
  apply pos_plus_lt_compat_r;solve_propholds.
- intros r;split.
  + intros E;apply dec_sier_pr in E.
    apply tr;econstructor;split;[|apply dec_sier_pr];
    apply Q_average_between;trivial.
  + apply (Trunc_ind _);intros [s [E1 E2]];
    apply dec_sier_pr;apply dec_sier_pr in E2.
    transitivity s;trivial.
- intros r;split.
  + intros E;apply dec_sier_pr in E.
    apply tr;econstructor;split;[|apply dec_sier_pr];
    apply Q_average_between;trivial.
  + apply (Trunc_ind _);intros [s [E1 E2]];
    apply dec_sier_pr;apply dec_sier_pr in E2.
    transitivity s;trivial.
- intros r E1 E2;apply dec_sier_pr in E1;apply dec_sier_pr in E2.
  apply (lt_antisym r q);auto.
- intros r s E1.
  generalize (cotransitive E1 q).
  apply (Trunc_ind _);intros [E2|E2];apply tr;[left|right];
  apply dec_sier_pr;trivial.
Qed.

Global Instance QCut : Cast Q Cut
  := fun q => Build_Cut _ _ (QIsCut q).
Arguments QCut _ /.

Global Instance CutZero : Zero Cut := ' 0.
Arguments CutZero /.
Global Instance CutOne : One Cut := ' 1.
Arguments CutOne /.

Definition straddle (a : Cut) (q : Q) :=
  merely (exists l u : Q, lower a l /\ upper a u /\ u - l < q).


Lemma straddle_monotone (x : Cut) (q r : Q) (E : q < r) :
  straddle x q -> straddle x r.
Proof.
apply (Trunc_ind _);intros [l [u [E1 [E2 E3]]]].
apply tr;exists l,u. repeat split;trivial.
transitivity q;trivial.
Qed.


Lemma trisect (a : Cut) (q : Q) :
  straddle a q -> straddle a ((2/3) * q).
Proof.
apply (Trunc_ind _);intros [l [u [E1 [E2 E3]]]].
assert (E4 : (2 * l + u) / 3 < (2 * u + l) / 3).
- apply (strictly_order_preserving (.* (/ 3))).
  apply (strictly_order_reflecting (+ (- l - u))).
  assert (Hrw : 2 * l + u + (- l - u) = l)
  by abstract ring_tac.ring_with_integers (NatPair.Z nat);
  rewrite Hrw;clear Hrw.
  assert (Hrw : 2 * u + l + (- l - u) = u)
  by abstract ring_tac.ring_with_integers (NatPair.Z nat);
  rewrite Hrw;clear Hrw.
  apply cut_orders with a;trivial.
- generalize (cut_located a _ _ E4). apply (Trunc_ind _);intros [E5|E5].
  + apply tr;exists ((2 * l + u) / 3),u.
    split ; [assumption | split ; [assumption | idtac]].
    set (U := u) at 1.
    assert (Hrw : U = 3 / 3 * U);[|rewrite Hrw;unfold U;clear U Hrw].
    { unfold U;clear U. rewrite (dec_recip_inverse 3),mult_1_l;trivial.
      apply lt_ne_flip;solve_propholds. }
    assert (Hrw : 3 / 3 * u - (2 * l + u) / 3 = (u - l) * (2 / 3))
    by abstract ring_tac.ring_with_integers (NatPair.Z nat);
    rewrite Hrw;clear Hrw.
    assert (Hrw : 2 / 3 * q = q * (2 / 3)) by abstract ring_tac.ring_with_nat;
    rewrite Hrw;clear Hrw.
    apply (strictly_order_preserving (.* _)).
    trivial.
  + apply tr;exists l, ((2 * u + l) / 3).
    split ; [assumption | split ; [assumption | idtac]].
    set (L := l) at 2.
    assert (Hrw : L = 3 / 3 * L);[|rewrite Hrw;unfold L;clear L Hrw].
    { unfold L;clear L. rewrite (dec_recip_inverse 3),mult_1_l;trivial.
      apply lt_ne_flip;solve_propholds. }
    assert (Hrw : (2 * u + l) / 3 - 3 / 3 * l = (u - l) * (2 / 3))
    by abstract ring_tac.ring_with_integers (NatPair.Z nat);
    rewrite Hrw;clear Hrw.
    assert (Hrw : 2 / 3 * q = q * (2 / 3)) by abstract ring_tac.ring_with_nat;
    rewrite Hrw;clear Hrw.
    apply (strictly_order_preserving (.* _)).
    trivial.
Qed.

Lemma trisect_pow : forall a q, straddle a q ->
  forall n, straddle a (repeat n ((2/3) *.) q).
Proof.
intros a q E. induction n as [|n IHn].
- exact E.
- apply trisect in IHn;exact IHn.
Qed.

Lemma two_thirds_power_small : forall q r, 0 < q -> 0 < r ->
  exists n, repeat n ((2/3) *.) q < r.
Proof. Admitted.

Lemma straddle_pos : forall a q, 0 < q -> straddle a q.
Proof.
intros a q E.
generalize (lower_inhab a);apply (Trunc_ind _);intros [l El].
generalize (upper_inhab a);apply (Trunc_ind _);intros [u Eu].
pose proof (cut_orders _ _ _ El Eu) as E1.
apply flip_pos_minus in E1.
apply (pos_mult_compat 2) in E1;[|apply _]. red in E1.
destruct (two_thirds_power_small _ _ E1 E) as [n E2].
apply (straddle_monotone _ _ _ E2).
apply trisect_pow.
apply tr;exists l,u. repeat split;trivial.
set (UL := u - l) at 1;rewrite <-(mult_1_l UL);unfold UL;clear UL.
assert (E3 : PropHolds (0 < u - l)).
{ red. apply (strictly_order_reflecting (2 *.)). rewrite mult_0_r. trivial. }
apply (strictly_order_preserving (.* _)).
apply pos_plus_lt_compat_r. solve_propholds.
Qed.


Instance pred_plus : Plus QPred.
Proof.
intros x y q.
apply (EnumerableSup Q). intros r. apply (EnumerableSup Q). intros s.
exact (meet (meet (x r) (y s)) (DecSier (q = r + s))).
Defined.
Arguments pred_plus _ _ / _.

Lemma pred_plus_pr : forall a b : QPred,
  forall q, (a + b) q <-> merely (exists r s, a r /\ b s /\ q = r + s).
Proof.
unfold plus at 1;simpl. intros a b q;split.
- intros E.
  apply top_le_enumerable_sup in E;revert E;apply (Trunc_ind _);intros [r E].
  apply top_le_enumerable_sup in E;revert E;apply (Trunc_ind _);intros [s E].
  apply top_le_meet in E;destruct E as [E1 E3].
  apply top_le_meet in E1;destruct E1 as [E1 E2].
  apply dec_sier_pr in E3.
  apply tr;exists r,s;auto.
- apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
  apply top_le_enumerable_sup. apply tr;exists r.
  apply top_le_enumerable_sup. apply tr;exists s.
  repeat (apply top_le_meet;split);trivial.
  apply dec_sier_pr;trivial.
Qed.

Lemma lower_plus_pr : forall a b : Cut, forall q,
  (lower a + lower b) q <->
  merely (exists r s, lower a r /\ lower b s /\ q < r + s).
Proof.
intros a b q;split.
- intros E;apply pred_plus_pr in E;revert E;apply (Trunc_ind _);
  intros [r [s [E1 [E2 E3]]]].
  apply lower_rounded in E1. revert E1;apply (Trunc_ind _);intros [r' [Er E1]].
  apply tr;exists r',s;repeat split;trivial.
  rewrite E3. apply (strictly_order_preserving (+ _)). trivial.
- apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
  apply pred_plus_pr.
  apply tr;exists r, (s - (r + s - q));repeat split.
  + trivial.
  + apply lower_le with s;trivial. apply lt_le;red.
    apply flip_lt_minus_l. apply pos_plus_lt_compat_r.
    apply flip_lt_minus_l. rewrite involutive,plus_0_l. trivial.
  + abstract ring_tac.ring_with_integers (NatPair.Z nat).
Qed.

Lemma upper_plus_pr : forall a b : Cut, forall q,
  (upper a + upper b) q <->
  merely (exists r s, upper a r /\ upper b s /\ r + s < q).
Proof.
intros a b q;split.
- intros E;apply pred_plus_pr in E;revert E;apply (Trunc_ind _);
  intros [r [s [E1 [E2 E3]]]].
  apply upper_rounded in E1. revert E1;apply (Trunc_ind _);intros [r' [Er E1]].
  apply tr;exists r',s;repeat split;trivial.
  rewrite E3. apply (strictly_order_preserving (+ _)). trivial.
- apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
  apply pred_plus_pr.
  apply tr;exists r, (s - (r + s - q));repeat split.
  + trivial.
  + apply upper_le with s;trivial. apply lt_le;red.
    apply pos_plus_lt_compat_r. apply flip_neg_negate.
    apply flip_lt_minus_l. rewrite plus_0_l. trivial.
  + abstract ring_tac.ring_with_integers (NatPair.Z nat).
Qed.

Lemma plus_iscut : forall a b : Cut,
  IsCut (lower a + lower b) (upper a + upper b).
Proof.
intros a b;split.
- generalize (lower_inhab a).
  apply (Trunc_ind _);intros [r Er].
  generalize (lower_inhab b).
  apply (Trunc_ind _);intros [s Es].
  apply tr;exists (r+s). apply pred_plus_pr.
  apply tr;exists r,s;auto.
- generalize (upper_inhab a).
  apply (Trunc_ind _);intros [r Er].
  generalize (upper_inhab b).
  apply (Trunc_ind _);intros [s Es].
  apply tr;exists (r+s). apply pred_plus_pr.
  apply tr;exists r,s;auto.
- intros q;split.
  + intros E. apply pred_plus_pr in E.
    revert E;apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
    apply (lower_rounded a) in E1.
    apply (lower_rounded b) in E2.
    revert E1;apply (Trunc_ind _);intros [r' [E1 E1']];
    revert E2;apply (Trunc_ind _);intros [s' [E2 E2']].
    apply tr;exists (r' + s'). split.
    * rewrite E3. apply plus_lt_compat;trivial.
    * apply pred_plus_pr. apply tr;eauto.
  + apply (Trunc_ind _);intros [q' [E1 E2]].
    apply pred_plus_pr in E2. revert E2.
    apply (Trunc_ind _);intros [r' [s' [E2 [E3 E4]]]].
    assert (Hq : q = (r' - (q' - q)) + s')
    by (rewrite E4;ring_tac.ring_with_integers (NatPair.Z nat)).
    rewrite Hq. apply pred_plus_pr.
    apply tr;econstructor;econstructor;split;[|split;[|reflexivity]];trivial.
    apply lower_le with r';trivial.
    apply flip_le_minus_l. apply nonneg_plus_le_compat_r.
    apply (snd (flip_nonneg_minus _ _)). apply lt_le;trivial.
- intros r;split.
  + intros E. apply pred_plus_pr in E.
    revert E;apply (Trunc_ind _);intros [q [s [E1 [E2 E3]]]].
    apply (upper_rounded a) in E1.
    apply (upper_rounded b) in E2.
    revert E1;apply (Trunc_ind _);intros [r' [E1 E1']];
    revert E2;apply (Trunc_ind _);intros [s' [E2 E2']].
    apply tr;exists (r' + s'). split.
    * rewrite E3. apply plus_lt_compat;trivial.
    * apply pred_plus_pr. apply tr;eauto.
  + apply (Trunc_ind _);intros [r' [E1 E2]].
    apply pred_plus_pr in E2. revert E2.
    apply (Trunc_ind _);intros [q' [s' [E2 [E3 E4]]]].
    assert (Hr : r = (q' - (r' - r)) + s')
    by (rewrite E4;ring_tac.ring_with_integers (NatPair.Z nat)).
    rewrite Hr. apply pred_plus_pr.
    apply tr;econstructor;econstructor;split;[|split;[|reflexivity]];trivial.
    apply upper_le with q';trivial.
    apply nonneg_plus_le_compat_r. rewrite <-negate_swap_r.
    apply (snd (flip_nonneg_minus _ _)). apply lt_le;trivial.
- intros q E1 E2.
  apply pred_plus_pr in E1;apply pred_plus_pr in E2.
  revert E1;apply (Trunc_ind _);intros [r1 [s1 [E1 [E1' E1'']]]].
  revert E2;apply (Trunc_ind _);intros [r2 [s2 [E2 [E2' E2'']]]].
  rewrite E1'' in E2'';clear E1'' q.
  destruct (total le r1 r2) as [E3|E3].
  + destruct (total le s1 s2) as [E4|E4].
    * assert (E5 : r2 <= r1).
      { apply not_lt_le_flip. intros E5.
        assert (E6 : r1 + s1 < r2 + s2)
        by (apply plus_lt_le_compat;trivial).
        rewrite E2'' in E6. revert E6;apply (irreflexivity lt). }
      apply (cut_disjoint a r2);trivial. apply lower_le with r1;trivial.
    * apply (cut_disjoint b s1);trivial. apply upper_le with s2;trivial.
  + apply (cut_disjoint a r2);trivial. apply lower_le with r1;trivial.
- intros q r E.
  assert (E1 : 0 < (r - q) / 2).
  { apply pos_mult_compat;[|solve_propholds].
    red. apply (snd (flip_pos_minus _ _)). trivial. }
  generalize (straddle_pos a _ E1);apply (Trunc_ind _);
  intros [La [Ua [Ea1 [Ea2 Ea3]]]].
  generalize (straddle_pos b _ E1);apply (Trunc_ind _);
  intros [Lb [Ub [Eb1 [Eb2 Eb3]]]].
  destruct (le_or_lt r (La + Lb)) as [E2|E2].
  + apply tr;left. apply lower_plus_pr.
    apply tr;exists La,Lb;repeat split;trivial.
    apply lt_le_trans with r;trivial.
  + destruct (le_or_lt r (Ua + Ub)) as [E3|E3].
    * { apply tr;left.
      apply lower_plus_pr. apply tr;exists La,Lb;repeat split;trivial.
      apply flip_lt_negate. rewrite negate_plus_distr.
      apply (strictly_order_reflecting (r +)).
      transitivity ((r - q) / 2 + (Ub - Lb)).
      - eapply le_lt_trans;[apply (order_preserving (+ _) _ _ E3)|].
        assert (Hrw : Ua + Ub + (- La - Lb) = Ua - La + (Ub - Lb))
        by abstract ring_tac.ring_with_nat;
        rewrite Hrw;clear Hrw.
        apply (strictly_order_preserving (+ _)).
        trivial.
      - set (RQ := r - q) at 2;assert (Hrw : RQ = RQ / 2 + RQ / 2);
        [|rewrite Hrw;unfold RQ;clear RQ Hrw].
        { path_via (RQ * (2 / 2));[|abstract ring_tac.ring_with_nat].
          rewrite dec_recip_inverse,mult_1_r;trivial.
          apply lt_ne_flip;solve_propholds. }
        apply (strictly_order_preserving (_ +)). trivial. }
    * apply tr;right;apply upper_plus_pr. apply tr. exists Ua,Ub. auto.
Qed.

Global Instance CutPlus : Plus Cut
  := fun a b => Build_Cut _ _ (plus_iscut a b).
Arguments CutPlus _ _ /.

Lemma iscut_negate : forall a : Cut,
  IsCut (fun q => upper a (- q)) (fun q => lower a (- q)).
Proof.
intros a;split.
- generalize (upper_inhab a);apply (Trunc_ind _);
  intros [q E];apply tr;exists (- q).
  rewrite involutive;trivial.
- generalize (lower_inhab a);apply (Trunc_ind _);
  intros [q E];apply tr;exists (- q).
  rewrite involutive;trivial.
- intros. split.
  + intros E;apply upper_rounded in E;revert E;apply (Trunc_ind _);
    intros [r [E1 E2]]. apply tr;exists (- r);split.
    * apply flip_lt_negate. rewrite involutive;trivial.
    * rewrite involutive;trivial.
  + apply (Trunc_ind _);intros [r [E1 E2]]. apply upper_rounded.
    apply tr;exists (- r);split.
    * apply (snd (flip_lt_negate _ _)). trivial.
    * trivial.
- intros. split.
  + intros E;apply lower_rounded in E;revert E;apply (Trunc_ind _);
    intros [q [E1 E2]]. apply tr;exists (- q);split.
    * apply flip_lt_negate. rewrite involutive;trivial.
    * rewrite involutive;trivial.
  + apply (Trunc_ind _);intros [q [E1 E2]]. apply lower_rounded.
    apply tr;exists (- q);split.
    * apply (snd (flip_lt_negate _ _)). trivial.
    * trivial.
- intros q E1 E2;revert E2 E1;apply cut_disjoint.
- intros q r E. apply flip_lt_negate in E. apply (cut_located a) in E.
  revert E;apply (Trunc_ind _);intros [E|E];apply tr;auto.
Qed.

Global Instance CutNeg : Negate Cut
  := fun a => Build_Cut _ _ (iscut_negate a).
Arguments CutNeg _ /.

Lemma CutPlus_comm : Commutative CutPlus.
Proof.
intros a b;apply cut_eq;simpl;intros q;split;intros E;
apply pred_plus_pr in E;apply pred_plus_pr;
revert E;apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]];
apply tr;exists s,r;repeat split;trivial;
rewrite E3;apply commutativity.
Qed.

Lemma CutPlus_assoc : Associative CutPlus.
Proof.
intros a b c;apply (antisymmetry le);red;simpl;intros q E;
apply pred_plus_pr in E;revert E;apply (Trunc_ind _);
[intros [r [s [E1 [E2 E3]]]] | intros [r [s [E2 [E1 E3]]]]];
apply pred_plus_pr in E2;revert E2;apply (Trunc_ind _);
intros [l [u [E2 [E4 E5]]]];rewrite E3,E5;
[rewrite plus_assoc | rewrite <-plus_assoc];
(apply pred_plus_pr;apply tr;do 2 econstructor;split;[|split;[|reflexivity]]);
trivial;apply pred_plus_pr;apply tr;eauto.
Qed.

Lemma CutPlus_left_id : LeftIdentity CutPlus 0.
Proof.
intros a;apply (antisymmetry le);red;simpl;intros q E.
- apply pred_plus_pr in E;revert E;apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
  apply dec_sier_pr in E1. rewrite E3. apply lower_le with s;trivial.
  set (S:=s) at 2;rewrite <-(plus_0_l S);unfold S;clear S.
  apply (order_preserving (+ _)). apply lt_le;trivial.
- apply pred_plus_pr.
  apply lower_rounded in E;revert E;apply (Trunc_ind _);intros [s [E1 E2]].
  apply tr;exists (q - s),s;repeat split.
  + apply dec_sier_pr. apply flip_neg_minus in E1. trivial.
  + trivial.
  + abstract ring_tac.ring_with_integers (NatPair.Z nat).
Qed.

Lemma CutPlus_left_inverse : LeftInverse CutPlus CutNeg 0.
Proof.
intros a;apply (antisymmetry le);red;simpl;intros q E.
- apply dec_sier_pr;apply pred_plus_pr in E. revert E;apply (Trunc_ind _);
  intros [r [s [E1 [E2 E3]]]].
  rewrite E3. pose proof (cut_orders _ _ _ E2 E1) as E.
  apply flip_neg_minus in E. rewrite involutive,plus_comm in E;trivial.
- apply dec_sier_pr in E. apply flip_neg_negate in E.
  generalize (straddle_pos a _ E). apply (Trunc_ind _).
  intros [l [u [E1 [E2 E3]]]].
  apply flip_lt_negate in E3;rewrite involutive,<-negate_swap_r,plus_comm in E3.
  change ((lower (- a) + lower a) q). apply lower_plus_pr.
  apply tr;exists (- u),l;repeat split;trivial.
  change (upper a (- - u)). rewrite involutive;trivial.
Qed.

Instance CutPlus_abgroup : AbGroup Cut (Aop:=CutPlus) (Aunit:=0).
Proof.
repeat split;unfold sg_op,mon_unit;simpl.
- apply _.
- apply CutPlus_assoc.
- apply CutPlus_left_id.
- intros a. rewrite CutPlus_comm;apply CutPlus_left_id.
- apply CutPlus_left_inverse.
- intros a. rewrite CutPlus_comm;apply CutPlus_left_inverse.
- apply CutPlus_comm.
Qed.

End contents.

