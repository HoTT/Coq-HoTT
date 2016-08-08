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
  ; iscut_cut_disjoint : forall q, disjoint (lower q) (upper q)
  ; iscut_cut_located : forall q r, q < r -> hor (lower q) (upper r) }.
End iscut_def.

Record Cut@{} :=
  { lower : QPred
  ; upper : QPred
  ; cut_iscut : IsCut lower upper }.
Global Existing Instance cut_iscut.

Definition lower_inhab@{} (c : Cut) := iscut_lower_inhab (lower c) _.
Definition upper_inhab@{} (c : Cut) := iscut_upper_inhab (lower c) _.
Definition lower_rounded@{} (c : Cut) := iscut_lower_rounded (lower c) _.
Definition upper_rounded@{} (c : Cut) := iscut_upper_rounded (lower c) _.
Definition cut_disjoint@{} (c : Cut) := iscut_cut_disjoint (lower c) _.
Definition cut_located@{} (c : Cut) := iscut_cut_located (lower c) _.

Lemma lower_le@{} : forall a q r, lower a q -> r <= q -> lower a r.
Proof.
intros a q r E1 E2.
destruct (le_or_lt q r) as [E3|E3].
- destruct (antisymmetry le _ _ E2 E3);trivial.
- apply lower_rounded. apply tr. exists q;auto.
Qed.

Lemma upper_le@{} : forall a q r, upper a q -> q <= r -> upper a r.
Proof.
intros a q r E1 E2.
destruct (le_or_lt r q) as [E3|E3].
- destruct (antisymmetry le _ _ E2 E3);trivial.
- apply upper_rounded. apply tr. exists q;auto.
Qed.

(* Show that IsCut is equivalent to a big conjunction of hProps
   so we can use typeclasses to prove IsHProp IsCut. *)
Definition IsCut_conjunction l u : IsCut l u -> _
  := fun c => (iscut_lower_inhab l u, iscut_upper_inhab l u,
    iscut_lower_rounded l u, iscut_upper_rounded l u,
    iscut_cut_disjoint l u, iscut_cut_located l u).

Global Instance iscut_conj_isequiv@{} {l u}
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

Global Instance IsCut_hprop@{} : forall l u, IsHProp (IsCut l u).
Proof.
intros. apply (@trunc_equiv _ _ ((IsCut_conjunction l u)^-1) _ _ _).
Qed.

Lemma cut_eq0@{} : forall a b : Cut, lower a = lower b -> upper a = upper b ->
  a = b.
Proof.
intros [la ua Ea] [lb ub Eb];simpl;intros E1 E2;destruct E1,E2;apply ap.
apply path_ishprop.
Qed.

Instance cut_isset@{} : IsHSet Cut.
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => lower a = lower b /\ upper a = upper b)).
- intros a;split;reflexivity.
- apply _.
- intros a b E;apply cut_eq0;apply E.
Qed.

Lemma cut_eq@{} : forall a b : Cut, (forall q, lower a q <-> lower b q) ->
  (forall r, upper a r <-> upper b r) ->
  a = b.
Proof.
intros a b E1 E2;apply cut_eq0;apply path_forall;intros q;apply (antisymmetry le);
apply imply_le;(apply E1 || apply E2).
Qed.

Lemma cut_orders@{} : forall (c : Cut) (q r : Q), lower c q -> upper c r -> q < r.
Proof.
intros c q r E1 E2.
destruct (le_or_lt r q) as [E|E];trivial.
destruct (cut_disjoint c q);trivial.
apply upper_le with r;trivial.
Qed.

Global Instance CutLe@{} : Le@{UQ UQ} Cut
  := fun a b => forall q, lower a q -> lower b q.
Arguments CutLe _ _ /.

Lemma CutLe_upper' : forall a b : Cut,
  a <= b <-> (forall r, upper b r -> upper a r).
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

Definition CutLe_upper@{} := CutLe_upper'@{UQ UQ}.

Instance CutLe_partial_order@{} : PartialOrder CutLe.
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

Global Instance CutLt@{} : Lt@{UQ UQ} Cut :=
  fun a b => merely (exists q, upper a q /\ lower b q).
Arguments CutLt _ _ /.

Global Instance CutApart@{} : Apart@{UQ UQ} Cut
  := fun a b => a < b \/ b < a.
Arguments CutApart _ _ /.

Instance CutLt_strict_order@{} : StrictOrder CutLt.
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

Lemma QIsCut@{} : forall q : Q,
  IsCut (fun r => semi_decide (r < q)) (fun r => semi_decide (q < r)).
Proof.
intros q;split.
- apply tr;exists (q - 1). apply (snd semi_decidable).
  apply flip_lt_minus_l. apply pos_plus_lt_compat_r;solve_propholds.
- apply tr;exists (q + 1);apply (snd semi_decidable).
  apply pos_plus_lt_compat_r;solve_propholds.
- intros r;split.
  + intros E;apply semi_decidable in E.
    apply tr;econstructor;split;[|apply (snd semi_decidable)];
    apply Q_average_between;trivial.
  + apply (Trunc_ind _);intros [s [E1 E2]];
    apply (snd semi_decidable);apply semi_decidable in E2.
    transitivity s;trivial.
- intros r;split.
  + intros E;apply semi_decidable in E.
    apply tr;econstructor;split;[|apply (snd semi_decidable)];
    apply Q_average_between;trivial.
  + apply (Trunc_ind _);intros [s [E1 E2]];
    apply (snd semi_decidable);apply semi_decidable in E2.
    transitivity s;trivial.
- intros r E1 E2;apply semi_decidable in E1;apply semi_decidable in E2.
  apply (lt_antisym r q);auto.
- intros r s E1.
  generalize (cotransitive E1 q).
  apply (Trunc_ind _);intros [E2|E2];apply tr;[left|right];
  apply (snd semi_decidable);trivial.
Qed.

Global Instance QCut@{} : Cast Q Cut
  := fun q => Build_Cut _ _ (QIsCut q).
Arguments QCut _ /.

Global Instance CutZero@{} : Zero Cut := ' 0.
Arguments CutZero /.
Global Instance CutOne@{} : One Cut := ' 1.
Arguments CutOne /.

Lemma cut_lt_lower : forall a q, ' q < a <-> lower a q.
Proof.
intros;split.
- apply (Trunc_ind _);intros [r [E1 E2]].
  apply lower_le with r;trivial. change (IsTop (semi_decide (q < r))) in E1.
  apply semi_decidable in E1.
  apply lt_le;trivial.
- intros E;apply lower_rounded in E;revert E;apply (Trunc_ind _);intros [r [E1 E2]].
  apply tr;exists r;split;trivial.
  change (semi_decide (q < r)).
  apply (snd semi_decidable);trivial.
Qed.

Lemma cut_lt_upper : forall a q, a < ' q <-> upper a q.
Proof.
intros;split.
- apply (Trunc_ind _);intros [r [E1 E2]].
  apply upper_le with r;trivial. change (IsTop (semi_decide (r < q))) in E2.
  apply (fst semi_decidable) in E2. apply lt_le;trivial.
- intros E;apply upper_rounded in E;revert E;apply (Trunc_ind _);
  intros [r [E1 E2]].
  apply tr;exists r;split;trivial.
  apply (snd semi_decidable);trivial.
Qed.

Definition straddle@{} (a : Cut) (q : Q) :=
  merely@{UQ} (exists l u : Q, lower a l /\ upper a u /\ u - l < q).

Lemma straddle_monotone@{} (x : Cut) (q r : Q) (E : q < r) :
  straddle x q -> straddle x r.
Proof.
apply (Trunc_ind _);intros [l [u [E1 [E2 E3]]]].
apply tr;exists l,u. repeat split;trivial.
transitivity q;trivial.
Qed.

Lemma trisect@{} (a : Cut) (q : Q) :
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

Lemma trisect_pow@{} : forall a q, straddle a q ->
  forall n, straddle a (repeat n ((2/3) *.) q).
Proof.
intros a q E. induction n as [|n IHn].
- exact E.
- apply trisect in IHn;exact IHn.
Qed.

Lemma two_thirds_power_small@{} : forall q r, 0 < q -> 0 < r ->
  exists n, repeat n ((2/3) *.) q < r.
Proof. Admitted.

Lemma straddle_pos@{} : forall a q, 0 < q -> straddle a q.
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


Instance pred_plus@{} : Plus QPred.
Proof.
intros x y q.
apply (EnumerableSup Q). intros r. apply (EnumerableSup Q). intros s.
exact (meet (meet (x r) (y s)) (semi_decide (q = r + s))).
Defined.
Arguments pred_plus _ _ / _.

Lemma pred_plus_pr' : forall a b : QPred,
  forall q, (a + b) q <-> merely (exists r s, a r /\ b s /\ q = r + s).
Proof.
unfold plus at 1;simpl. intros a b q;split.
- intros E.
  apply top_le_enumerable_sup in E;revert E;apply (Trunc_ind _);intros [r E].
  apply top_le_enumerable_sup in E;revert E;apply (Trunc_ind _);intros [s E].
  apply top_le_meet in E;destruct E as [E1 E3].
  apply top_le_meet in E1;destruct E1 as [E1 E2].
  apply semi_decidable in E3.
  apply tr;exists r,s;auto.
- apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
  apply top_le_enumerable_sup. apply tr;exists r.
  apply top_le_enumerable_sup. apply tr;exists s.
  repeat (apply top_le_meet;split);trivial.
  apply semi_decidable in E3;trivial.
Qed.

Definition pred_plus_pr@{} := pred_plus_pr'@{UQ UQ UQ UQ UQ
  Set Set Ularge Set Set
  Set Uhuge Set Set Set
  Set Set Set Set Set
  Set Set Set Set Set
  Set Set Set Set Set
  Set Set Set Set Set
  Set Set Set Set Set
  Set Set Set Set Set
  Set Set Set Set Set
  Set Set Set Set Set
  Set Set Set Set}.

Lemma lower_pred_plus_pr' : forall a b : Cut, forall q,
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

Definition lower_pred_plus_pr@{} := lower_pred_plus_pr'@{UQ UQ UQ UQ UQ}.

Lemma upper_pred_plus_pr' : forall a b : Cut, forall q,
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

Definition upper_pred_plus_pr@{} := upper_pred_plus_pr'@{UQ UQ UQ UQ UQ}.

Lemma plus_iscut@{} : forall a b : Cut,
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
  + apply tr;left. apply lower_pred_plus_pr.
    apply tr;exists La,Lb;repeat split;trivial.
    apply lt_le_trans with r;trivial.
  + destruct (le_or_lt r (Ua + Ub)) as [E3|E3].
    * { apply tr;left.
      apply lower_pred_plus_pr. apply tr;exists La,Lb;repeat split;trivial.
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
    * apply tr;right;apply upper_pred_plus_pr. apply tr. exists Ua,Ub. auto.
Qed.

Global Instance CutPlus@{} : Plus Cut
  := fun a b => Build_Cut _ _ (plus_iscut a b).
Arguments CutPlus _ _ /.

Lemma lower_plus_eq_pr : forall a b : Cut, forall q,
  lower (a + b) q <->
  merely (exists r s, lower a r /\ lower b s /\ q = r + s).
Proof.
intros a b q;apply pred_plus_pr.
Qed.

Lemma upper_plus_eq_pr : forall a b : Cut, forall q,
  upper (a + b) q <->
  merely (exists r s, upper a r /\ upper b s /\ q = r + s).
Proof.
intros a b q;apply pred_plus_pr.
Qed.

Lemma lower_plus_lt_pr : forall a b : Cut, forall q,
  lower (a + b) q <->
  merely (exists r s, lower a r /\ lower b s /\ q < r + s).
Proof.
exact lower_pred_plus_pr.
Qed.

Lemma upper_plus_lt_pr : forall a b : Cut, forall q,
  upper (a + b) q <->
  merely (exists r s, upper a r /\ upper b s /\ r + s < q).
Proof.
exact upper_pred_plus_pr.
Qed.

Lemma iscut_negate@{} : forall a : Cut,
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

Global Instance CutNeg@{} : Negate Cut
  := fun a => Build_Cut _ _ (iscut_negate a).
Arguments CutNeg _ /.

Lemma CutPlus_comm@{} : Commutative CutPlus.
Proof.
intros a b;apply cut_eq;simpl;intros q;split;intros E;
apply pred_plus_pr in E;apply pred_plus_pr;
revert E;apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]];
apply tr;exists s,r;repeat split;trivial;
rewrite E3;apply commutativity.
Qed.

Lemma CutPlus_assoc@{} : Associative CutPlus.
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

Lemma CutPlus_left_id@{} : LeftIdentity CutPlus 0.
Proof.
intros a;apply (antisymmetry le);red;simpl;intros q E.
- apply pred_plus_pr in E;revert E;apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
  apply semi_decidable in E1. rewrite E3. apply lower_le with s;trivial.
  set (S:=s) at 2;rewrite <-(plus_0_l S);unfold S;clear S.
  apply (order_preserving (+ _)). apply lt_le;trivial.
- apply pred_plus_pr.
  apply lower_rounded in E;revert E;apply (Trunc_ind _);intros [s [E1 E2]].
  apply tr;exists (q - s),s;repeat split.
  + apply (snd semi_decidable). apply flip_neg_minus in E1. trivial.
  + trivial.
  + abstract ring_tac.ring_with_integers (NatPair.Z nat).
Qed.

Lemma CutPlus_left_inverse@{} : LeftInverse CutPlus CutNeg 0.
Proof.
intros a;apply (antisymmetry le);red;simpl;intros q E.
- apply (snd semi_decidable);apply pred_plus_pr in E. revert E;apply (Trunc_ind _);
  intros [r [s [E1 [E2 E3]]]].
  rewrite E3. pose proof (cut_orders _ _ _ E2 E1) as E.
  apply flip_neg_minus in E. rewrite involutive,plus_comm in E;trivial.
- apply semi_decidable in E. apply flip_neg_negate in E.
  generalize (straddle_pos a _ E). apply (Trunc_ind _).
  intros [l [u [E1 [E2 E3]]]].
  apply flip_lt_negate in E3;rewrite involutive,<-negate_swap_r,plus_comm in E3.
  change ((lower (- a) + lower a) q). apply lower_pred_plus_pr.
  apply tr;exists (- u),l;repeat split;trivial.
  change (upper a (- - u)). rewrite involutive;trivial.
Qed.

Global Instance CutPlus_abgroup@{} : AbGroup Cut (Aop:=CutPlus) (Aunit:=0).
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

Lemma CutPlus_rat@{} : forall q r : Q, ' (q + r) = ' q + ' r :> Cut.
Proof.
intros;apply (antisymmetry le).
- intros s E. change (IsTop (semi_decide (s < q + r))) in E.
  apply (fst semi_decidable) in E.
  change (IsTop ((lower (' q) + lower (' r)) s)). apply pred_plus_pr.
  apply tr. exists (q - (q + r - s) / 2), (r - (q + r - s) / 2).
  repeat split.
  + apply (snd semi_decidable). apply flip_lt_minus_l.
    apply pos_plus_lt_compat_r.
    apply pos_mult_compat;[|solve_propholds].
    red. apply flip_pos_minus in E. trivial.
  + apply (snd semi_decidable). apply flip_lt_minus_l.
    apply pos_plus_lt_compat_r.
    apply pos_mult_compat;[|solve_propholds].
    red. apply flip_pos_minus in E. trivial.
  + set (QRS := q + r - s).
    path_via (q + r - QRS * (2 / 2));
    [|abstract ring_tac.ring_with_integers (NatPair.Z nat)].
    rewrite dec_recip_inverse;[|apply lt_ne_flip;solve_propholds].
    rewrite mult_1_r;unfold QRS;clear QRS.
    abstract ring_tac.ring_with_integers (NatPair.Z nat).
- intros s E. simpl. apply (snd semi_decidable).
  simpl in E. apply pred_plus_pr in E.
  revert E;apply (Trunc_ind _);intros [r' [s' [E1 [E2 E3]]]].
  apply semi_decidable in E1;apply semi_decidable in E2.
  rewrite E3. apply plus_lt_compat;trivial.
Qed.

Lemma CutNeg_rat@{} : forall q : Q, ' (- q) = - ' q :> Cut.
Proof.
intros;apply (antisymmetry le);intros r E;
apply (fst (@semi_decidable (_ < _) _ _)) in E;apply (snd semi_decidable);
apply flip_lt_negate;rewrite involutive;trivial.
Qed.

Lemma CutLt_rat_preserving@{} : StrictlyOrderPreserving (cast Q Cut).
Proof.
intros q r E. apply tr.
econstructor;split;apply (snd semi_decidable),Q_average_between;trivial.
Qed.

Lemma CutLt_rat_reflecting@{} : StrictlyOrderReflecting (cast Q Cut).
Proof.
intros q r;apply (Trunc_ind _);intros [s [E1 E2]].
apply (@semi_decidable (_ < _) _ _) in E1;
apply (@semi_decidable (_ < _) _ _) in E2.
transitivity s;trivial.
Qed.

Global Instance CutLt_rat_embedding@{} : StrictOrderEmbedding (cast Q Cut).
Proof.
split.
- apply CutLt_rat_preserving.
- apply CutLt_rat_reflecting.
Qed.

Lemma Cut_archimedean@{} : forall a b : Cut, a < b ->
  merely (exists q : Q, a < ' q < b).
Proof.
intros a b;apply (Trunc_ind _);intros [q [E1 E2]].
apply upper_rounded in E1;revert E1;apply (Trunc_ind _);intros [qa [Ea1 Ea2]].
apply lower_rounded in E2;revert E2;apply (Trunc_ind _);intros [qb [Eb1 Eb2]].
apply tr;exists q.
split;apply tr;[exists qa|exists qb];split;trivial;apply (snd semi_decidable);
trivial.
Qed.

Lemma CutJoin_iscut' : forall a b : Cut,
  IsCut (fun q => join (lower a q) (lower b q))
    (fun q => meet (upper a q) (upper b q)).
Proof.
intros a b;split.
- generalize (lower_inhab a);apply (Trunc_ind _);intros [q E].
  apply tr;exists q;apply top_le_join,tr,inl,E.
- generalize (upper_inhab a);apply (Trunc_ind _);intros [q E1].
  generalize (upper_inhab b);apply (Trunc_ind _);intros [r E2].
  apply tr;exists (join q r);apply top_le_meet;split;
  eapply upper_le;eauto.
  + apply join_ub_l.
  + apply join_ub_r.
- intros q;split.
  + intros E;apply top_le_join in E;revert E;apply (Trunc_ind _);intros [E|E];
    apply lower_rounded in E;revert E;apply (Trunc_ind _);intros [r [E1 E2]];
    apply tr;exists r;split;trivial;apply top_le_join,tr;auto.
  + apply (Trunc_ind _);intros [r [E1 E2]];apply top_le_join in E2;revert E2.
    apply (Trunc_ind _);intros [E2|E2];
    apply top_le_join,tr;[left|right];apply lower_rounded,tr;
    eauto.
- intros q;split.
  + intros E;apply top_le_meet in E;destruct E as [E1 E2].
    apply upper_rounded in E1;revert E1;apply (Trunc_ind _);intros [r [Er E1]].
    apply upper_rounded in E2;revert E2;apply (Trunc_ind _);intros [s [Es E2]].
    apply tr;exists (join r s);split;[|apply top_le_meet;split].
    * destruct (total le r s) as [E3|E3];rewrite ?(join_l _ _ E3),?(join_r _ _ E3);
      trivial.
    * apply upper_le with r;trivial. apply join_ub_l.
    * apply upper_le with s;trivial. apply join_ub_r.
  + apply (Trunc_ind _);intros [r [E1 E2]];
    apply top_le_meet in E2;destruct E2 as [E2 E3].
    apply top_le_meet;split;apply upper_le with r;trivial;apply lt_le;trivial.
- intros q E1 E2.
  apply top_le_meet in E2;destruct E2 as [E2 E3].
  apply top_le_join in E1;revert E1;apply (Trunc_ind _);intros [E1|E1];
  eapply cut_disjoint;eauto.
- intros q r E.
  generalize (cut_located a _ _ E). apply (Trunc_ind _);intros [E1|E1].
  + apply tr,inl,top_le_join,tr,inl,E1.
  + generalize (cut_located b _ _ E). apply (Trunc_ind _);intros [E2|E2].
    * apply tr,inl,top_le_join,tr,inr,E2.
    * apply tr,inr,top_le_meet;split;trivial.
Qed.

Definition CutJoin_iscut@{} := CutJoin_iscut'@{Set Set Set Set Set
  Set Set Set Set Set
  Set Set Set Set Set
  Set Set Set Set Set
  Set Set Set Set Set
  Set Set Set Set Set
  Set}.

Global Instance CutJoin@{} : Join Cut
  := fun a b => Build_Cut _ _ (CutJoin_iscut a b).
Arguments CutJoin _ _ /.

Lemma CutMeet_iscut' : forall a b : Cut,
  IsCut (fun q => meet (lower a q) (lower b q))
    (fun q => join (upper a q) (upper b q)).
Proof.
intros a b;split.
- generalize (lower_inhab a);apply (Trunc_ind _);intros [q E1].
  generalize (lower_inhab b);apply (Trunc_ind _);intros [r E2].
  apply tr;exists (meet q r);apply top_le_meet;split;
  eapply lower_le;eauto.
  + apply meet_lb_l.
  + apply meet_lb_r.
- generalize (upper_inhab a);apply (Trunc_ind _);intros [q E].
  apply tr;exists q;apply top_le_join,tr,inl,E.
- intros q;split.
  + intros E;apply top_le_meet in E;destruct E as [E1 E2].
    apply lower_rounded in E1;revert E1;apply (Trunc_ind _);intros [r [Er E1]].
    apply lower_rounded in E2;revert E2;apply (Trunc_ind _);intros [s [Es E2]].
    apply tr;exists (meet r s);split;[|apply top_le_meet;split].
    * destruct (total le r s) as [E3|E3];rewrite ?(meet_l _ _ E3),?(meet_r _ _ E3);
      trivial.
    * apply lower_le with r;trivial. apply meet_lb_l.
    * apply lower_le with s;trivial. apply meet_lb_r.
  + apply (Trunc_ind _);intros [r [E1 E2]];
    apply top_le_meet in E2;destruct E2 as [E2 E3].
    apply top_le_meet;split;apply lower_le with r;trivial;apply lt_le;trivial.
- intros q;split.
  + intros E;apply top_le_join in E;revert E;apply (Trunc_ind _);intros [E|E];
    apply upper_rounded in E;revert E;apply (Trunc_ind _);intros [r [E1 E2]];
    apply tr;exists r;split;trivial;apply top_le_join,tr;auto.
  + apply (Trunc_ind _);intros [r [E1 E2]];apply top_le_join in E2;revert E2.
    apply (Trunc_ind _);intros [E2|E2];
    apply top_le_join,tr;[left|right];apply upper_rounded,tr;
    eauto.
- intros q E2 E1.
  apply top_le_meet in E2;destruct E2 as [E2 E3].
  apply top_le_join in E1;revert E1;apply (Trunc_ind _);intros [E1|E1];
  refine (cut_disjoint _ _ _ E1);trivial.
- intros q r E.
  generalize (cut_located a _ _ E). apply (Trunc_ind _);intros [E1|E1].
  + generalize (cut_located b _ _ E). apply (Trunc_ind _);intros [E2|E2].
    * apply tr,inl,top_le_meet;split;trivial.
    * apply tr,inr,top_le_join,tr,inr,E2.
  + apply tr,inr,top_le_join,tr,inl,E1.
Qed.

Definition CutMeet_iscut@{} := CutMeet_iscut'@{Set Set Set Set Set
  Set Set Set Set Set
  Set Set Set Set Set
  Set Set Set Set Set
  Set Set Set Set Set
  Set Set Set Set Set
  Set}.

Global Instance CutMeet@{} : Meet Cut
  := fun a b => Build_Cut _ _ (CutMeet_iscut a b).
Arguments CutMeet _ _ /.

Lemma cut_lattice_order' : LatticeOrder CutLe.
Proof.
split;split;try apply _.
- intros a b q;unfold meet;simpl;intros E;apply top_le_meet in E.
  destruct E as [E1 _];trivial.
- intros a b q;unfold meet;simpl;intros E;apply top_le_meet in E.
  destruct E as [_ E2];trivial.
- intros a b c E1 E2 q E. apply top_le_meet.
  split;[apply E1|apply E2];apply E.
- intros a b q E. apply top_le_join,tr,inl,E.
- intros a b q E. apply top_le_join,tr,inr,E.
- intros a b c E1 E2 q E;apply top_le_join in E.
  revert E;apply (Trunc_ind _);intros [E|E];[apply E1|apply E2];apply E.
Qed.

Definition cut_lattice_order@{} := cut_lattice_order'@{Set Set Set Set Set
  Set Set Set Set Set
  Set Set}.
Global Existing Instance cut_lattice_order.

Local Existing Instance join_sl_order_join_sl.
Local Existing Instance meet_sl_order_meet_sl.

Lemma cut_not_lt_le_flip@{} : forall a b : Cut, ~ a < b -> b <= a.
Proof.
intros a b E q E1.
apply lower_rounded in E1;revert E1;apply (Trunc_ind _);intros [r [E1 E2]].
generalize (cut_located a _ _ E1). apply (Trunc_ind _).
intros [E3|E3];trivial.
destruct E. apply tr;exists r. split;trivial.
Qed.

Lemma CutLt_cotrans@{} : CoTransitive (@lt Cut CutLt).
Proof.
intros a b E c;revert E;apply (Trunc_ind _). intros [q [E1 E2]].
apply lower_rounded in E2;revert E2;apply (Trunc_ind _);intros [s [Es E2]].
apply upper_rounded in E1;revert E1;apply (Trunc_ind _);intros [r [Er E1]].
generalize (cut_located c _ _ (transitivity Er Es)).
apply (Trunc_ind _);intros [E3|E3].
- apply tr;left. apply tr;exists r;split;trivial.
- apply tr;right. apply tr;exists s;split;trivial.
Qed.

Instance Cut_isapart@{} : IsApart Cut.
Proof.
split.
- apply _.
- unfold apart;simpl;intros a b;apply Sum.ishprop_sum;try apply _.
  intros E1 E2;apply (lt_antisym a b);split;trivial.
- intros a b [E|E];[right|left];trivial.
- intros a b [E|E] c;generalize (CutLt_cotrans _ _ E c);apply (Trunc_ind _);
  intros [E1|E1];apply tr;unfold apart;simpl;auto.
- intros a b;split.
  + intros E. apply (antisymmetry le);apply cut_not_lt_le_flip;intros E1;
    apply E;unfold apart;simpl;auto.
  + intros E;destruct E;intros [E|E];revert E;apply (irreflexivity lt).
Qed.

Global Instance Cut_fullpseudoorder@{} : FullPseudoOrder CutLe CutLt.
Proof.
repeat (split;try (revert x; fail 1);try apply _).
- apply lt_antisym.
- apply CutLt_cotrans.
- intros a b;split; trivial.
- intros a b;split.
  + intros E1;red;apply (Trunc_ind _);intros [q [E2 E3]].
    apply E1 in E3. revert E3 E2;apply cut_disjoint.
  + apply cut_not_lt_le_flip.
Qed.

Lemma CutLe_rat_preserving@{} : OrderPreserving (cast Q Cut).
Proof.
apply full_pseudo_order_preserving.
Qed.

Lemma CutLe_rat_reflecting@{} : OrderReflecting (cast Q Cut).
Proof.
apply full_pseudo_order_reflecting.
Qed.

Instance CutLe_rat_embedding@{} : OrderEmbedding (cast Q Cut).
Proof.
split.
- apply CutLe_rat_preserving.
- apply CutLe_rat_reflecting.
Qed.

Lemma cut_plus_le_preserving@{} : forall a : Cut, OrderPreserving (a +).
Proof.
intros a b c E q E1. apply lower_plus_eq_pr in E1.
revert E1;apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
apply lower_plus_eq_pr. apply tr;exists r,s;repeat split;trivial.
apply E. trivial.
Qed.

Lemma cut_plus_le_reflecting@{} : forall a : Cut, OrderReflecting (a +).
Proof.
intros a b c E.
apply (cut_plus_le_preserving (- a)) in E.
unfold plus in E.
rewrite !CutPlus_assoc,(CutPlus_left_inverse a),!CutPlus_left_id in E.
trivial.
Qed.

Instance cut_plus_le_embedding@{} : forall a : Cut, OrderEmbedding (a +).
Proof.
intros;split.
- apply cut_plus_le_preserving.
- apply cut_plus_le_reflecting.
Qed.

Lemma cut_lt_plus_pos@{} : forall (a : Cut) (e : Q), 0 < e -> a < a + ' e.
Proof.
intros a e E. generalize (straddle_pos a e E). apply (Trunc_ind _).
intros [l [u [E1 [E2 E3]]]]. apply tr;exists u. split;trivial.
apply lower_plus_eq_pr.
apply tr;exists l,(u - l). repeat split;trivial.
- apply (snd semi_decidable). trivial.
- ring_tac.ring_with_integers (NatPair.Z nat).
Qed.

Lemma cut_lt_exists_pos_plus_le@{} : forall x y : Cut, x < y ->
  merely (exists e : Q, 0 < e /\ x + ' e <= y).
Proof.
intros a b;apply (Trunc_ind _). intros [q [E1 E2]].
apply lower_rounded in E2. revert E2;apply (Trunc_ind _);intros [r [E2 E3]].
apply tr;exists (r - q). split.
- apply flip_pos_minus in E2. trivial.
- intros s E4. apply lower_plus_eq_pr in E4.
  revert E4;apply (Trunc_ind _);intros [q' [r' [E4 [E5 E6]]]].
  apply (@semi_decidable (_ < _) _ _) in E5. apply lower_le with r;trivial.
  rewrite E6.
  transitivity (q' + (r - q)).
  { apply lt_le,(strictly_order_preserving (q' +)). trivial. }
  assert (Hrw : q' + (r - q) = r - (q - q'))
  by abstract ring_tac.ring_with_integers (NatPair.Z nat);
  rewrite Hrw;clear Hrw.
  apply flip_le_minus_l. apply nonneg_plus_le_compat_r.
  apply (snd (flip_nonneg_minus _ _)). apply lt_le,(cut_orders a);trivial.
Qed.

Lemma cut_plus_lt_preserving@{} : forall a : Cut, StrictlyOrderPreserving (a +).
Proof.
intros a b c E.
apply cut_lt_exists_pos_plus_le in E;revert E;apply (Trunc_ind _);
intros [e [Ee E]].
apply lt_le_trans with (a + b + ' e).
- apply cut_lt_plus_pos. trivial.
- rewrite <-(simple_associativity (f:=@plus Cut _)).
  apply (order_preserving (a +)). trivial.
Qed.

Lemma cut_lt_plus_reflecting@{} : forall a : Cut, StrictlyOrderReflecting (a +).
Proof.
intros a b c E.
apply (cut_plus_lt_preserving (- a)) in E.
unfold plus in E.
rewrite !CutPlus_assoc,(CutPlus_left_inverse a),!CutPlus_left_id in E.
trivial.
Qed.

Instance cut_lt_plus_embedding@{} : forall a : Cut, StrictOrderEmbedding (a +).
Proof.
intros;split.
- apply cut_plus_lt_preserving.
- apply cut_lt_plus_reflecting.
Qed.

Section redundant.
(* This section is redundant one we have ring structure
   since then we can use lemmas from orders.rings etc *)
Lemma cut_plus_lt_compat : forall a b c d : Cut, a < c -> b < d -> a + b < c + d.
Proof.
intros a b c d E1 E2.
transitivity (c + b).
- rewrite 2!(commutativity _ b). apply (strictly_order_preserving (b +)). trivial.
- apply (strictly_order_preserving (c +));trivial.
Qed.

Lemma cut_flip_lt_negate : forall a b : Cut, - a < - b <-> b < a.
Proof.
assert (Eaux : forall a b : Cut, a < b -> - b < - a).
- intros a b E. apply (strictly_order_reflecting (a +)).
  rewrite right_inverse. rewrite (commutativity (f:=plus)).
  apply (strictly_order_reflecting (b +)). rewrite simple_associativity.
  rewrite right_inverse,left_identity,right_identity. trivial.
- intros a b;split;intros E;apply Eaux in E;rewrite ?involutive in E;trivial.
Qed.

End redundant.

Lemma CutAbs_of_nonneg_aux : forall a, 0 <= a -> join (- a) a = a.
Proof.
intros a E.
apply join_r.
apply (order_reflecting (a +)).
rewrite right_inverse.
transitivity (a + 0).
- rewrite right_identity. trivial.
- apply (order_preserving (a +));trivial.
Qed.

Lemma CutAbs_of_nonpos_aux : forall a, a <= 0 -> join (- a) a = - a.
Proof.
intros a E;apply join_l.
apply (order_reflecting (a +)).
rewrite right_inverse.
transitivity (a + 0).
- apply (order_preserving (a +));trivial.
- rewrite right_identity. trivial.
Qed.

Global Instance CutAbs : Abs Cut.
Proof.
intros a;exists (join (- a) a).
split.
- apply CutAbs_of_nonneg_aux.
- apply CutAbs_of_nonpos_aux.
Defined.
Arguments CutAbs _ /.

Lemma CutAbs_of_nonneg : forall a : Cut, 0 <= a -> abs a = a.
Proof.
intros a;apply ((CutAbs a).2).
Qed.

Lemma CutAbs_of_nonpos : forall a : Cut, a <= 0 -> abs a = - a.
Proof.
intros a;apply ((CutAbs a).2).
Qed.

Lemma CutAbs_is_join : forall a : Cut, abs a = join (- a) a.
Proof. reflexivity. Defined.

Lemma CutAbs_nonneg : forall a : Cut, 0 <= abs a.
Proof.
intros a q E. apply (@semi_decidable (_ < _) _ _) in E.
apply (strictly_order_preserving (cast Q Cut)) in E.
generalize (cotransitive E a). apply (Trunc_ind _);intros [E1|E1].
- apply cut_lt_lower in E1.
  unfold abs;simpl. apply top_le_join. apply tr;right;trivial.
- generalize (cotransitive E (- a)). apply (Trunc_ind _);intros [E2|E2].
  + apply cut_lt_lower in E2.
    unfold abs;simpl. apply top_le_join. apply tr;left;trivial.
  + pose proof (cut_plus_lt_compat _ _ _ _ E1 E2) as E3.
    rewrite right_inverse,left_identity in E3. destruct (irreflexivity lt _ E3).
Qed.

Lemma CutAbs_rat : forall q : Q, ' (abs q) = abs (' q) :> Cut.
Proof.
intros q. Symmetry.
destruct (total le 0 q) as [E|E].
- rewrite (Qabs_of_nonneg q);trivial.
  apply CutAbs_of_nonneg.
  apply (order_preserving (cast Q Cut)). trivial.
- rewrite (Qabs_of_nonpos q);trivial. rewrite CutNeg_rat.
  apply CutAbs_of_nonpos.
  apply (order_preserving (cast Q Cut)). trivial.
Qed.

Lemma CutAbs_neg : forall a : Cut, abs (- a) = abs a.
Proof.
intros;unfold abs;simpl. rewrite involutive. apply commutativity.
Qed.

Lemma CutLt_join : forall a b c : Cut, a < c -> b < c -> join a b < c.
Proof.
intros a b c E1 E2.
revert E1;apply (Trunc_ind _);intros [q [E1 E1']].
revert E2;apply (Trunc_ind _);intros [r [E2 E2']].
apply tr;exists (join q r);split.
- simpl. apply top_le_meet. split;eapply upper_le;eauto.
  + apply join_ub_l.
  + apply join_ub_r.
- destruct (total le q r) as [E3|E3];
  rewrite ?(join_l _ _ E3),?(join_r _ _ E3);trivial.
Qed.

Global Instance CutClose@{} : Closeness Cut
  := fun e a b => abs (a - b) < ' ' e.
Arguments CutClose _ _ _ /.

Global Instance QCut_nonexpanding@{} : NonExpanding (cast Q Cut).
Proof.
intros e q r E.
red;simpl. rewrite <-CutNeg_rat,<-CutPlus_rat,<-CutAbs_rat.
apply (strictly_order_preserving _). apply Qclose_alt. trivial.
Qed.

Lemma Cut_separated_aux@{} : forall a b : Cut, (forall e, close e a b) -> a <= b.
Proof.
intros a b E. apply cut_not_lt_le_flip.
intros E1;apply cut_lt_exists_pos_plus_le in E1;revert E1;apply (Trunc_ind _);
intros [e [Ee E1]].
pose proof (E (mkQpos e Ee)) as E2. red in E2;simpl in E2.
unfold cast at 3 in E2;simpl in E2.
apply (irreflexivity lt (' e)). apply le_lt_trans with (abs (a - b));trivial.
transitivity (a - b);[|apply join_ub_r].
apply (order_reflecting (b +)).
assert (Hrw : b + (a - b) = a);[|rewrite Hrw;trivial].
path_via (a - b + b);[apply commutativity|].
path_via (a + (- b + b));[Symmetry;apply associativity|].
path_via (a + 0);[apply ap,left_inverse|].
apply right_identity.
Qed.

Lemma CutClose_symm : forall e, Symmetric (close (A:=Cut) e).
Proof.
intros e a b E. red;simpl. rewrite <-CutAbs_neg.
rewrite groups.negate_sg_op,involutive. trivial.
Qed.

Lemma Cut_triangular : Triangular Cut.
Proof.
intros a b c e d E1 E2.
red;simpl. apply CutLt_join.
- assert (Hrw : - (a - c) = (c - b) + (b - a)).
  { (* TODO ring *)
    rewrite groups.negate_sg_op,involutive.
    rewrite <-(simple_associativity (f:=plus)),(simple_associativity (- b)).
    rewrite left_inverse. rewrite (left_identity (op:=plus) (x:=0)). trivial.
  }
  rewrite Hrw;clear Hrw. unfold cast at 2;simpl.
  rewrite (plus_comm (' e) (' d)). rewrite CutPlus_rat.
  apply cut_plus_lt_compat.
  + apply le_lt_trans with (abs (c - b));[apply join_ub_r|].
    rewrite <-CutAbs_neg,groups.negate_sg_op,involutive.
    apply E2.
  + apply le_lt_trans with (abs (b - a));[apply join_ub_r|].
    rewrite <-CutAbs_neg,groups.negate_sg_op,involutive.
    apply E1.
- assert (Hrw : a - c = (a - b) + (b - c)).
  { (* TODO ring *)
    rewrite <-(simple_associativity (f:=plus)),(simple_associativity (- b)).
    rewrite left_inverse. rewrite (left_identity (op:=plus) (x:=0)). trivial.
  }
  rewrite Hrw;clear Hrw. unfold cast at 2;simpl. rewrite CutPlus_rat.
   apply cut_plus_lt_compat;(eapply le_lt_trans;[|(apply E1 || apply E2)]);
   apply join_ub_r.
Qed.

Lemma Cut_rounded : Rounded Cut.
Proof.
intros e u v;split.
- intros E. red in E;simpl in E.
  apply Cut_archimedean in E. revert E;apply (Trunc_ind _);intros [q [E1 E2]].
  assert (E3 : 0 < q).
  { apply (strictly_order_reflecting (cast Q Cut)).
    apply le_lt_trans with (abs (u - v));trivial.
    apply CutAbs_nonneg. }
  apply (strictly_order_reflecting (cast Q Cut)) in E2.
  apply tr;exists (mkQpos _ E3),(Qpos_diff _ _ E2).
  split.
  + apply pos_eq. unfold cast at 2;simpl.
    unfold cast at 2 3;simpl.
    abstract ring_tac.ring_with_integers (NatPair.Z nat).
  + apply E1.
- apply (Trunc_ind _);intros [d [d' [He E]]].
  red;simpl. transitivity (' ' d).
  + apply E.
  + apply (strictly_order_preserving _). rewrite He;unfold cast at 2;simpl.
    apply pos_plus_lt_compat_r. solve_propholds.
Qed.

Global Instance Cut_premetric : PreMetric Cut.
Proof.
split.
- apply _.
- intros e a;red;simpl. rewrite right_inverse.
  rewrite CutAbs_of_nonneg;[|reflexivity].
  apply (strictly_order_preserving (cast Q Cut)). solve_propholds.
- apply CutClose_symm.
- intros a b E. apply (antisymmetry le);apply Cut_separated_aux;trivial.
  intros e. apply CutClose_symm;trivial.
- exact Cut_triangular.
- apply Cut_rounded.
Qed.

Global Instance CutPlus_nonexpanding_l : forall a : Cut, NonExpanding (a +).
Proof.
intros a e b c xi.
unfold close in *;simpl in *.
assert (Hrw : a + b - (a + c) = b - c);[|rewrite Hrw;trivial].
rewrite (groups.negate_sg_op a c).
unfold plus,sg_op.
rewrite (CutPlus_comm (- c)), CutPlus_assoc.
apply (ap (fun x => CutPlus x _)).
rewrite CutPlus_comm, CutPlus_assoc,CutPlus_left_inverse.
apply CutPlus_left_id.
Qed.

Global Instance CutPlus_nonexpanding_r : forall a : Cut, NonExpanding (+ a).
Proof.
intros a e b c xi.
unfold close in *;simpl in *.
unfold plus;rewrite !(CutPlus_comm _ a).
apply CutPlus_nonexpanding_l. trivial.
Qed.

Global Instance CutNeg_nonexpanding : NonExpanding (@negate Cut _).
Proof.
intros e a b xi.
red;simpl. pose proof (groups.negate_sg_op (- b) a) as Hrw.
unfold sg_op,plus_is_sg_op,plus in *;rewrite <-Hrw.
rewrite CutAbs_neg,CutPlus_comm. trivial.
Qed.

Definition lim_lower_cut (x : Approximation Cut) : QPred
  := fun q => EnumerableSup Q+ (fun e => EnumerableSup Q+ (fun d =>
    lower (x e) (q + 'e + ' d))).

Definition lim_upper_cut (x : Approximation Cut) : QPred
  := fun q => EnumerableSup Q+ (fun e => EnumerableSup Q+ (fun d =>
    upper (x e) (q - ' e - ' d))).

Lemma lim_lower_cut_pr : forall x q, lim_lower_cut x q <->
  merely (exists e d : Q+, lower (x e) (q + ' e + ' d)).
Proof.
intros x q;split.
- intros E. apply top_le_enumerable_sup in E;revert E;apply (Trunc_ind _);
  intros [e E]. apply top_le_enumerable_sup in E;revert E;apply (Trunc_ind _);
  intros [d E].
  apply tr;exists e,d;trivial.
- apply (Trunc_ind _);intros [e [d E]].
  apply top_le_enumerable_sup;apply tr;exists e.
  apply top_le_enumerable_sup;apply tr;exists d.
  trivial.
Qed.

Lemma lim_upper_cut_pr : forall x q, lim_upper_cut x q <->
  merely (exists e d : Q+, upper (x e) (q - ' e - ' d)).
Proof.
intros x q;split.
- intros E. apply top_le_enumerable_sup in E;revert E;apply (Trunc_ind _);
  intros [e E]. apply top_le_enumerable_sup in E;revert E;apply (Trunc_ind _);
  intros [d E].
  apply tr;exists e,d;trivial.
- apply (Trunc_ind _);intros [e [d E]].
  apply top_le_enumerable_sup;apply tr;exists e.
  apply top_le_enumerable_sup;apply tr;exists d.
  trivial.
Qed.

Lemma lim_iscut (x : Approximation Cut)
  : IsCut (lim_lower_cut x) (lim_upper_cut x).
Proof.
split.
- generalize (lower_inhab (x 1)).
  apply (Trunc_ind _);intros [q E].
  apply tr;exists (q - 1 - 1).
  apply lim_lower_cut_pr. apply tr;exists (1:Q+),(1:Q+).
  unfold cast;simpl.
  assert (Hrw : q - 1 - 1 + 1 + 1 = q)
  by abstract ring_tac.ring_with_integers (NatPair.Z nat);
  rewrite Hrw;clear Hrw.
  trivial.
- generalize (upper_inhab (x 1)).
  apply (Trunc_ind _);intros [q E].
  apply tr;exists (q + 1 + 1).
  apply lim_upper_cut_pr. apply tr;exists (1:Q+),(1:Q+).
  unfold cast;simpl.
  assert (Hrw : q + 1 + 1 - 1 - 1 = q)
  by abstract ring_tac.ring_with_integers (NatPair.Z nat);
  rewrite Hrw;clear Hrw.
  trivial.
- intros q;split.
  + intros E;apply lim_lower_cut_pr in E;revert E;apply (Trunc_ind _);
    intros [e [d E]].
    apply lower_rounded in E;revert E;apply (Trunc_ind _);intros [r [Er E]].
    apply tr;exists (r - ' e - ' d);split.
    * apply flip_lt_minus_r,(snd (flip_lt_minus_r _ _ _)).
      rewrite <-plus_assoc,(plus_comm (' d)),plus_assoc. trivial.
    * apply lim_lower_cut_pr. apply tr;exists e,d.
      assert (Hrw : r - ' e - ' d + ' e + ' d = r)
      by abstract ring_tac.ring_with_integers (NatPair.Z nat);
      rewrite Hrw;trivial.
  + apply (Trunc_ind _);intros [r [Er E]];apply lim_lower_cut_pr in E;
    revert E;apply (Trunc_ind _);intros [e [d E]].
    apply lim_lower_cut_pr. apply tr;exists e,d.
    apply lower_le with (r + ' e + ' d);trivial.
    rewrite <-!plus_assoc. apply (order_preserving (+ _)).
    apply lt_le;trivial.
- intros q;split.
  + intros E;apply lim_upper_cut_pr in E;revert E;apply (Trunc_ind _);
    intros [e [d E]].
    apply upper_rounded in E;revert E;apply (Trunc_ind _);intros [r [Er E]].
    apply tr;exists (r + ' e + ' d);split.
    * apply flip_lt_minus_r,flip_lt_minus_r.
      rewrite <-plus_assoc,(plus_comm (- ' d)),plus_assoc. trivial.
    * apply lim_upper_cut_pr. apply tr;exists e,d.
      assert (Hrw : r + ' e + ' d - ' e - ' d = r)
      by abstract ring_tac.ring_with_integers (NatPair.Z nat);
      rewrite Hrw;trivial.
  + apply (Trunc_ind _);intros [r [Er E]];apply lim_upper_cut_pr in E;
    revert E;apply (Trunc_ind _);intros [e [d E]].
    apply lim_upper_cut_pr. apply tr;exists e,d.
    apply upper_le with (r - ' e - ' d);trivial.
    rewrite <-!plus_assoc. apply (order_preserving (+ _)).
    apply lt_le;trivial.
- intros q E1 E2;apply lim_lower_cut_pr in E1;apply lim_upper_cut_pr in E2.
  revert E1;apply (Trunc_ind _);intros [e1 [d1 E1]].
  revert E2;apply (Trunc_ind _);intros [e2 [d2 E2]].
  apply cut_lt_lower in E1. apply cut_lt_upper in E2.
  pose proof (approx_equiv x e1 e2) as E3.
  red in E3;simpl in E3. apply cut_flip_lt_negate in E2.
  pose proof (cut_plus_lt_compat _ _ _ _ E1 E2) as E4.
  pose proof (le_lt_trans _ _ _ (join_ub_r _ _) E3) as E5.
  pose proof (transitivity E4 E5) as E6.
  rewrite <-CutNeg_rat,<-CutPlus_rat in E6.
  apply (strictly_order_reflecting (cast Q Cut)) in E6.
  assert (Hrw : q + ' e1 + ' d1 - (q - ' e2 - ' d2) = ' (e1 + e2) + ' (d1 + d2))
  by abstract ring_tac.ring_with_integers (NatPair.Z nat);
  rewrite Hrw in E6;clear Hrw.
  apply (irreflexivity lt (' (e1 + e2))).
  etransitivity;eauto.
  apply pos_plus_lt_compat_r;solve_propholds.
- intros q r E.
  assert (E1 : exists e : Q+, 5 * ' e < r - q).
  { exists ((Qpos_diff _ _ E) / 6).
    unfold cast;simpl.
    rewrite mult_assoc,(mult_comm 5),<-mult_assoc.
    rewrite <-(mult_1_r (r - q)).
    pose proof (snd (flip_pos_minus _ _) E) as E'.
    apply pos_mult_le_lt_compat;try split;
    [solve_propholds|reflexivity|trivial|solve_propholds|].
    apply (strictly_order_reflecting (.* (' 6))).
    rewrite mult_1_l,<-mult_assoc,(mult_comm (' _)).
    change (5 * (' (6 / 6)) < 6).
    rewrite pos_recip_r,mult_1_r. apply pos_plus_lt_compat_l. solve_propholds.
  }
  destruct E1 as [e E1].
  assert (E2 : q + ' e + ' e < r - ' e - ' e).
  { apply flip_pos_minus. apply flip_pos_minus in E1.
    assert (Hrw : r - ' e - ' e - (q + ' e + ' e) = (r - q - 5 * ' e) + ' e)
    by abstract ring_tac.ring_with_integers (NatPair.Z nat);
    rewrite Hrw;clear Hrw.
    etransitivity;eauto. apply pos_plus_lt_compat_r. solve_propholds. }
  generalize (cut_located (x e) _ _ E2). apply (Trunc_ind _);intros [E3|E3].
  + apply tr,inl,lim_lower_cut_pr,tr. exists e,e. trivial.
  + apply tr,inr,lim_upper_cut_pr,tr. exists e,e;trivial.
Qed.

Global Instance CutLim : Lim Cut
  := fun x => Build_Cut _ _ (lim_iscut x).

Global Instance Cut_cauchy_complete : CauchyComplete Cut.
Proof.
do 3 red;simpl. intros x d e.
assert (E1 : ' d / 4 < ' d / 2).
{ apply (strictly_order_preserving (_ *.)).
  change (/ 2) with (cast Q+ Q (/ 2)).
  rewrite <-(Qpos_mult_1_l (/ 2)),<-two_fourth_is_one_half.
  unfold cast;simpl. rewrite <-(mult_1_l (/ 4)).
  rewrite (mult_comm 1),(mult_comm (' 2)).
  apply pos_mult_le_lt_compat;try split;try solve_propholds.
  { reflexivity. }
  { apply pos_plus_lt_compat_r;solve_propholds. }
}
pose proof (strictly_order_preserving (cast Q Cut) _ _
  (snd (flip_lt_negate _ _) E1)) as E2.
apply (strictly_order_preserving ((x e - (' ' e)) +)) in E2.
apply Cut_archimedean in E2;revert E2;apply (Trunc_ind _);intros [q [E2 E3]].
assert (Eq : ' q < lim x).
{ apply cut_lt_lower. unfold lim;simpl. apply lim_lower_cut_pr.
  apply tr;exists e,(d/4). apply cut_lt_lower.
  apply (strictly_order_reflecting ((- ' (' e) + ' (- (' d / 4))) +)).
  assert (Hrw : - ' (' e) + ' (- (' d / 4)) + x e =
    x e - ' (' e) + ' (- (' d / 4)));[|rewrite Hrw;clear Hrw].
  { rewrite (commutativity (f:=plus)). apply simple_associativity. }
  assert (Hrw : - ' (' e) + ' (- (' d / 4)) + ' (q + ' e + ' (d / 4)) = ' q);
  [|rewrite Hrw;trivial].
  rewrite <-CutNeg_rat,<-!CutPlus_rat. apply ap.
  abstract ring_tac.ring_with_integers (NatPair.Z nat).
}
pose proof (strictly_order_preserving (cast Q Cut) _ _ E1) as E4.
apply (strictly_order_preserving ((x e + (' ' e)) +)) in E4.
apply Cut_archimedean in E4;revert E4;apply (Trunc_ind _);intros [r [E4 E5]].
assert (Er : lim x < ' r).
{ apply cut_lt_upper. unfold lim;simpl. apply lim_upper_cut_pr.
  apply tr;exists e,(d/4).
  apply cut_lt_upper.
  apply (strictly_order_reflecting ((' (' e) + ' ((' d / 4))) +)).
  assert (Hrw : ' (' e) + ' (' d / 4) + x e = x e + ' (' e) + ' (' d / 4));
  [|rewrite Hrw;clear Hrw].
  { rewrite (commutativity (f:=plus)). apply simple_associativity. }
  assert (Hrw : ' (' e) + ' (' d / 4) + ' (r - ' e - ' (d / 4)) = ' r);
  [|rewrite Hrw;trivial].
  rewrite <-!CutPlus_rat. apply ap.
  abstract ring_tac.ring_with_integers (NatPair.Z nat).
}
pose proof (between_pos (' d / 2) prop_holds) as E6.
apply (strictly_order_preserving (cast Q Cut)) in E6.
apply (strictly_order_preserving ((x e) +)) in E6.
generalize (cotransitive E6 (lim x)). apply (Trunc_ind _);intros [E7|E7].
- apply CutLt_join.
  + rewrite groups.negate_sg_op,involutive.
    change (lim x & - x e) with (lim x - x e).
    apply (strictly_order_reflecting ((x e) +)).
    assert (Hrw : x e + (lim x - x e) = lim x);[|rewrite Hrw;clear Hrw].
    { rewrite (commutativity (f:=plus) (x e)),<-simple_associativity.
      rewrite left_inverse;apply right_identity. }
    transitivity (' r);trivial.
    etransitivity;[apply E5|].
    rewrite <-(simple_associativity (f:=plus) (x e) (' (' e))).
    apply (strictly_order_preserving (_ +)).
    rewrite <-CutPlus_rat. apply (strictly_order_preserving (cast Q Cut)).
    unfold cast at 3;simpl. rewrite (plus_comm (' d)).
    set (D := ' d / 2);rewrite (pos_split2 d);unfold D;clear D.
    rewrite plus_assoc.
    apply pos_plus_lt_compat_r;solve_propholds.
  + rewrite CutNeg_rat in E7.
    apply (strictly_order_reflecting ((lim x - ( ' (' d / 2))) +)).
    assert (Hrw : lim x - ' (' d / 2) + (x e - lim x) = x e - ' (' d / 2));
    [|rewrite Hrw;clear Hrw].
    { change (@plus Cut _) with CutPlus;
      rewrite !(CutPlus_comm (x e)), CutPlus_assoc;
      change CutPlus with (@plus Cut _).
      apply (ap (+ (x e))).
      change (@plus Cut _) with CutPlus;
      rewrite CutPlus_comm,CutPlus_assoc,CutPlus_left_inverse;
      change CutPlus with (@plus Cut _).
      apply CutPlus_left_id. }
    etransitivity;[apply E7|].
    change (@plus Cut _) with CutPlus;rewrite <-CutPlus_assoc;
    change CutPlus with (@plus Cut _).
    set (L := lim x) at 2;rewrite <-(CutPlus_left_id (lim x)),CutPlus_comm;
    unfold L;clear L;change CutPlus with (@plus Cut _).
    apply (strictly_order_preserving (lim x +)).
    rewrite <-CutNeg_rat,<-CutPlus_rat.
    apply (strictly_order_preserving (cast Q Cut)).
    set (D := 'd / 2);rewrite (pos_split2 d);unfold D;clear D.
    assert (Hrw : - (' d / 2) + ' (d / 2 + d / 2 + e) = ' (d / 2 + e));
    [|rewrite Hrw;solve_propholds].
    abstract ring_tac.ring_with_integers (NatPair.Z nat).
- apply CutLt_join.
  + rewrite groups.negate_sg_op,involutive.
    change (lim x & - x e) with (lim x - x e).
    apply (strictly_order_reflecting (x e +)).
    assert (Hrw : x e + (lim x - x e) = lim x);[|rewrite Hrw;clear Hrw].
    { rewrite (commutativity (f:=plus) (x e)),<-simple_associativity.
      rewrite left_inverse;apply right_identity. }
    etransitivity;[apply E7|].
    apply (strictly_order_preserving (_ +)).
    apply (strictly_order_preserving (cast Q Cut)).
    set (D := 'd / 2);rewrite (pos_split2 d);unfold D;clear D.
    rewrite <-Qpos_plus_assoc.
    apply pos_plus_lt_compat_r. solve_propholds.
  + apply (strictly_order_reflecting (lim x +)).
    assert (Hrw : lim x + (x e - lim x) = x e);[|rewrite Hrw;clear Hrw].
    { rewrite (commutativity (f:=plus) (lim x)),<-simple_associativity.
      rewrite left_inverse;apply right_identity. }
    apply (strictly_order_reflecting ((- ' (' (d + e))) +)).
    assert (Hrw : - ' (' (d + e)) + (lim x + ' (' (d + e))) = lim x);
    [|rewrite Hrw;clear Hrw].
    { change (@plus Cut _) with CutPlus;
      rewrite CutPlus_comm,<-CutPlus_assoc,(CutPlus_comm _ (- _)),
      CutPlus_left_inverse. apply right_identity. }
    etransitivity;[|apply Eq].
    etransitivity;[|apply E2].
    change (@plus Cut _) with CutPlus;rewrite CutPlus_comm,<-CutPlus_assoc;
    change CutPlus with (@plus Cut _).
    apply (strictly_order_preserving (_ +)).
    rewrite <-!CutNeg_rat,<-CutPlus_rat.
    apply (strictly_order_preserving (cast Q Cut)).
    apply flip_lt_negate;rewrite <-negate_swap_r,!involutive.
    set (D := 'd / 2);rewrite (pos_split2 d);unfold D;clear D.
    rewrite <-Qpos_plus_assoc,(qpos_plus_comm _ (_ + _)).
    apply pos_plus_lt_compat_r. solve_propholds.
Qed.

Lemma lower_upper_meet_bot : forall a q, meet (lower a q) (upper a q) <= bottom.
Proof.
intros a q. apply imply_le.
intros E;apply top_le_meet in E;destruct E as [E1 E2].
destruct (cut_disjoint _ _ E1 E2).
Qed.

Definition compare_cut_rat : Cut -> Q -> partial bool.
Proof.
intros a q.
apply (interleave (lower a q) (upper a q)).
hnf. apply cut_disjoint.
Defined.

Lemma compare_cut_rat_pr : forall a q b, compare_cut_rat a q = eta _ b <->
  match b with
  | true => ' q < a
  | false => a < ' q
  end.
Proof.
intros a q b.
split.
- intros E. apply interleave_pr in E.
  destruct b.
  + apply cut_lt_lower;trivial.
  + apply cut_lt_upper;trivial.
- intros E.
  unfold compare_cut_rat.
  destruct b;[apply cut_lt_lower in E|apply cut_lt_upper in E].
  + apply (interleave_top_l _ _ _ E).
  + apply (interleave_top_r _ _ _ E).
Qed.

Lemma compare_cut_rat_self : forall q, compare_cut_rat (' q) q = bot _.
Proof.
intros. unfold compare_cut_rat.
apply interleave_bot;apply imply_le;intros E;
apply (@semi_decidable (_ < _) _ _) in E;
destruct (irreflexivity lt _ E).
Qed.

End contents.

