Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.naturals
  HoTT.Classes.interfaces.integers
  HoTT.Classes.interfaces.rationals
  HoTT.Classes.interfaces.orders
  HoTT.Classes.theory.rings
  HoTT.Classes.theory.integers
  HoTT.Classes.theory.dec_fields
  HoTT.Classes.orders.dec_fields
  HoTT.Classes.orders.lattices
  HoTT.Classes.implementations.natpair_integers
  HoTT.Classes.theory.additional_operations.


Local Set Universe Minimization ToSet.

Section contents.
Context `{Funext} `{Univalence}.
Universe UQ.
Context {Q : Type@{UQ} } {Qap : Apart@{UQ UQ} Q}
  {Qplus : Plus Q} {Qmult : Mult Q}
  {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
  {Qle : Le@{UQ UQ} Q} {Qlt : Lt@{UQ UQ} Q}
  {QtoField : RationalsToField@{UQ UQ UQ UQ} Q}
  {Qrats : Rationals@{UQ UQ UQ UQ UQ UQ UQ UQ UQ UQ} Q}
  {Qtrivialapart : TrivialApart Q} {Qdec : DecidablePaths Q}
  {Qmeet : Meet Q} {Qjoin : Join Q} {Qlattice : LatticeOrder Qle}
  {Qle_total : TotalRelation (@le Q _)}
  {Qabs : Abs Q}.

Global Instance rational_1_neq_0 : PropHolds (@apart Q _ 1 0).
Proof.
red. apply trivial_apart. solve_propholds.
Qed.

Record Qpos@{} : Type@{UQ} := mkQpos { pos : Q; is_pos : 0 < pos }.
Notation "Q+" := Qpos.

Global Instance Qpos_Q@{} : Cast Qpos Q := pos.
Arguments Qpos_Q /.

Lemma Qpos_plus_pr@{} : forall a b : Qpos, 0 < 'a + 'b.
Proof.
intros.
apply semirings.pos_plus_compat;apply is_pos.
Qed.

Global Instance Qpos_plus@{} : Plus Qpos := fun a b => mkQpos _ (Qpos_plus_pr a b).

Global Instance pos_is_pos@{} : forall q : Q+, PropHolds (0 < ' q)
  := is_pos.

Lemma pos_eq@{} : forall a b : Q+, @paths Q (' a) (' b) -> a = b.
Proof.
intros [a Ea] [b Eb] E.
change (a = b) in E.
destruct E;apply ap;apply path_ishprop.
Qed.

Global Instance Qpos_isset : IsHSet Q+.
Proof.
apply (@HSet.ishset_hrel_subpaths _ (fun e d => ' e = ' d)).
- intros e; reflexivity.
- apply _.
- exact pos_eq.
Qed.

Global Instance Qpos_one@{} : One Q+.
Proof.
exists 1. apply lt_0_1.
Defined.

Global Instance Qpos_mult@{} : Mult Q+.
Proof.
intros a b;exists (' a * ' b).
solve_propholds.
Defined.

Global Instance qpos_plus_comm@{} : Commutative (@plus Q+ _).
Proof.
hnf. intros.
apply pos_eq. change (' x + ' y = ' y + ' x).
apply plus_comm.
Qed.

Global Instance qpos_mult_comm@{} : Commutative (@mult Q+ _).
Proof.
hnf;intros;apply pos_eq,mult_comm.
Qed.

Global Instance pos_recip@{} : DecRecip Q+.
Proof.
intros e. exists (/ ' e).
apply pos_dec_recip_compat.
solve_propholds.
Defined.

Global Instance pos_of_nat@{} : Cast nat Q+.
Proof.
intros n. destruct n as [|k].
- exists 1;apply lt_0_1.
- exists (naturals_to_semiring nat Q (S k)).
  induction k as [|k Ik].
  + change (0 < 1). apply lt_0_1.
  + change (0 < 1 + naturals_to_semiring nat Q (S k)).
    set (K := naturals_to_semiring nat Q (S k)) in *;clearbody K.
    apply pos_plus_compat.
    * apply lt_0_1.
    * trivial.
Defined.

Lemma pos_recip_r@{} : forall e : Q+, e / e = 1.
Proof.
intros;apply pos_eq.
unfold dec_recip,cast,pos_recip;simpl.
change (' e / ' e = 1). apply dec_recip_inverse.
apply lt_ne_flip. solve_propholds.
Qed.

Lemma pos_recip_r'@{} : forall e : Q+, @paths Q (' e / ' e) 1.
Proof.
intros. change (' (e / e) = 1). rewrite pos_recip_r. reflexivity.
Qed.

Lemma pos_mult_1_r@{} : forall e : Q+, e * 1 = e.
Proof.
intros;apply pos_eq. apply mult_1_r.
Qed.

Lemma pos_split2@{} : forall e : Q+, e = e / 2 + e / 2.
Proof.
intros.
path_via (e * (2 / 2)).
- rewrite pos_recip_r,pos_mult_1_r;reflexivity.
- apply pos_eq. change (' e * (2 / 2) = ' e / 2 + ' e / 2).
  ring_tac.ring_with_nat.
Qed.

Lemma pos_split3@{} : forall e : Q+, e = e / 3 + e / 3 + e / 3.
Proof.
intros.
path_via (e * (3 / 3)).
- rewrite pos_recip_r,pos_mult_1_r;reflexivity.
- apply pos_eq. change (' e * (3 / 3) = ' e / 3 + ' e / 3 + ' e / 3).
  ring_tac.ring_with_nat.
Qed.

Global Instance Qpos_mult_assoc@{} : Associative (@mult Q+ _).
Proof.
hnf.
intros;apply pos_eq.
apply mult_assoc.
Qed.

Global Instance Qpos_plus_assoc@{} : Associative (@plus Q+ _).
Proof.
hnf.
intros;apply pos_eq.
apply plus_assoc.
Qed.

Global Instance Qpos_mult_1_l@{} : LeftIdentity (@mult Q+ _) 1.
Proof.
hnf;intros;apply pos_eq;apply mult_1_l.
Qed.

Global Instance Qpos_mult_1_r@{} : RightIdentity (@mult Q+ _) 1.
Proof.
hnf;intros;apply pos_eq;apply mult_1_r.
Qed.

Lemma pos_recip_through_plus@{} : forall a b c : Q+,
  a + b = c * (a / c + b / c).
Proof.
intros. path_via ((a + b) * (c / c)).
- rewrite pos_recip_r;apply pos_eq,symmetry,mult_1_r.
- apply pos_eq;ring_tac.ring_with_nat.
Qed.

Lemma pos_unconjugate@{} : forall a b : Q+, a * b / a = b.
Proof.
intros. path_via (a / a * b).
- apply pos_eq;ring_tac.ring_with_nat.
- rewrite pos_recip_r;apply Qpos_mult_1_l.
Qed.

Lemma Qpos_recip_1 : / 1 = 1 :> Q+.
Proof.
apply pos_eq. exact dec_recip_1.
Qed.

Lemma Qpos_plus_mult_distr_l : @LeftDistribute Q+ mult plus.
Proof.
hnf. intros;apply pos_eq,plus_mult_distr_l.
Qed.

Global Instance Qpos_meet@{} : Meet Q+.
Proof.
intros a b. exists (meet (' a) (' b)).
apply not_le_lt_flip. intros E.
destruct (total_meet_either (' a) (' b)) as [E1|E1];
rewrite E1 in E;(eapply le_iff_not_lt_flip;[exact E|]);
solve_propholds.
Defined.

Global Instance Qpos_join@{} : Join Q+.
Proof.
intros a b. exists (join (' a) (' b)).
apply not_le_lt_flip. intros E.
destruct (total_join_either (' a) (' b)) as [E1|E1];
rewrite E1 in E;(eapply le_iff_not_lt_flip;[exact E|]);
solve_propholds.
Defined.

Lemma Q_sum_eq_join_meet@{} : forall a b c d : Q, a + b = c + d ->
  a + b = join a c + meet b d.
Proof.
intros ???? E.
destruct (total le a c) as [E1|E1].
- rewrite (join_r _ _ E1). rewrite meet_r;trivial.
  apply (order_preserving (+ b)) in E1.
  rewrite E in E1. apply (order_reflecting (c +)). trivial.
- rewrite (join_l _ _ E1).
  rewrite meet_l;trivial.
  apply (order_reflecting (a +)). rewrite E. apply (order_preserving (+ d)).
  trivial.
Qed.

Lemma Qpos_sum_eq_join_meet@{} : forall a b c d : Q+, a + b = c + d ->
  a + b = join a c + meet b d.
Proof.
intros ???? E.
apply pos_eq;apply Q_sum_eq_join_meet.
change (' a + ' b) with (' (a + b)). rewrite E;reflexivity.
Qed.

Lemma Qpos_le_lt_min : forall a b : Q+, ' a <= ' b ->
  exists c ca cb, a = c + ca /\ b = c + cb.
Proof.
intros a b E. exists (a/2),(a/2).
simple refine (existT _ _ _);simpl.
- exists (' (a / 2) + (' b - ' a)).
  apply nonneg_plus_lt_compat_r.
  + apply (snd (flip_nonneg_minus _ _)). trivial.
  + solve_propholds.
- split.
  + apply pos_split2.
  + apply pos_eq. unfold cast at 2;simpl.
    unfold cast at 3;simpl.
    set (a':=a/2);rewrite (pos_split2 a);unfold a';clear a'.
    ring_tac.ring_with_integers (NatPair.Z nat).
Qed.

Lemma Qpos_lt_min@{} : forall a b : Q+, exists c ca cb : Q+,
  a = c + ca /\ b = c + cb.
Proof.
intros.
destruct (total le (' a) (' b)) as [E|E].
- apply Qpos_le_lt_min;trivial.
- apply Qpos_le_lt_min in E. destruct E as [c [cb [ca [E1 E2]]]].
  exists c,ca,cb;auto.
Qed.

Definition Qpos_diff : forall q r : Q, q < r -> Q+.
Proof.
intros q r E;exists (r-q).
apply (snd (flip_pos_minus _ _) E).
Defined.

Lemma Qpos_diff_pr@{} : forall q r E, r = q + ' (Qpos_diff q r E).
Proof.
intros q r E. change (r = q + (r - q)).
abstract ring_tac.ring_with_integers (NatPair.Z nat).
Qed.


Lemma Qmeet_plus_l : forall a b c : Q, meet (a + b) (a + c) = a + meet b c.
Proof.
intros. destruct (total le b c) as [E|E].
- rewrite (meet_l _ _ E). apply meet_l.
  apply (order_preserving (a +)),E.
- rewrite (meet_r _ _ E). apply meet_r.
  apply (order_preserving (a +)),E.
Qed.

Lemma Qabs_nonneg@{} : forall q : Q, 0 <= abs q.
Proof.
intros q;destruct (total_abs_either q) as [E|E];destruct E as [E1 E2];rewrite E2.
- trivial.
- apply flip_nonneg_negate. rewrite involutive;trivial.
Qed.

Lemma Qabs_nonpos_0@{} : forall q : Q, abs q <= 0 -> q = 0.
Proof.
intros q E. pose proof (antisymmetry le _ _ E (Qabs_nonneg _)) as E1.
destruct (total_abs_either q) as [[E2 E3]|[E2 E3]];rewrite E3 in E1.
- trivial.
- apply (injective (-)). rewrite negate_0. trivial.
Qed.

Lemma Qabs_0_or_pos : forall q : Q, q = 0 |_| 0 < abs q.
Proof.
intros q. destruct (le_or_lt (abs q) 0) as [E|E].
- left. apply Qabs_nonpos_0. trivial.
- right. trivial.
Qed.

Lemma Qabs_of_nonneg@{} : forall q : Q, 0 <= q -> abs q = q.
Proof.
intro;apply ((abs_sig _).2).
Qed.

Lemma Qabs_of_nonpos : forall q : Q, q <= 0 -> abs q = - q.
Proof.
intro;apply ((abs_sig _).2).
Qed.

Lemma Qabs_le_raw@{} : forall x : Q, x <= abs x.
Proof.
intros x;destruct (total_abs_either x) as [[E1 E2]|[E1 E2]].
- rewrite E2;reflexivity.
- transitivity (0:Q);trivial.
  rewrite E2. apply flip_nonpos_negate. trivial.
Qed.

Lemma Qabs_neg@{} : forall x : Q, abs (- x) = abs x.
Proof.
intros x. destruct (total_abs_either x) as [[E1 E2]|[E1 E2]].
- rewrite E2. path_via (- - x);[|rewrite involutive;trivial].
  apply ((abs_sig (- x)).2). apply flip_nonneg_negate;trivial.
- rewrite E2. apply ((abs_sig (- x)).2). apply flip_nonpos_negate;trivial.
Qed.

Lemma Qabs_le_neg_raw : forall x : Q, - x <= abs x.
Proof.
intros x. rewrite <-Qabs_neg. apply Qabs_le_raw.
Qed.

Lemma Q_abs_le_pr@{} : forall x y : Q, abs x <= y <-> - y <= x /\ x <= y.
Proof.
intros x y;split.
- intros E. split.
  + apply flip_le_negate. rewrite involutive. transitivity (abs x);trivial.
    apply Qabs_le_neg_raw.
  + transitivity (abs x);trivial.
    apply Qabs_le_raw.
- intros [E1 E2].
  destruct (total_abs_either x) as [[E3 E4]|[E3 E4]];rewrite E4.
  + trivial.
  + apply flip_le_negate;rewrite involutive;trivial.
Qed.

Lemma Qabs_is_join@{} : forall q : Q, abs q = join (- q) q.
Proof.
intros q. symmetry.
destruct (total_abs_either q) as [[E1 E2]|[E1 E2]];rewrite E2.
- apply join_r. transitivity (0:Q);trivial.
  apply flip_nonneg_negate;trivial.
- apply join_l. transitivity (0:Q);trivial.
  apply flip_nonpos_negate;trivial.
Qed.

Lemma Qlt_join : forall a b c : Q, a < c -> b < c ->
  join a b < c.
Proof.
intros a b c E1 E2.
destruct (total le a b) as [E3|E3];rewrite ?(join_r _ _ E3),?(join_l _ _ E3);
trivial.
Qed.

Lemma Q_average_between@{} : forall q r : Q, q < r -> q < (q + r) / 2 < r.
Proof.
intros q r E.
split.
- apply flip_pos_minus.
  assert (Hrw : (q + r) / 2 - q = (r - q) / 2);[|rewrite Hrw;clear Hrw].
  { path_via ((q + r) / 2 - 2 / 2 * q).
    { rewrite dec_recip_inverse;[|solve_propholds].
      rewrite mult_1_l;trivial.
    }
    ring_tac.ring_with_integers (NatPair.Z nat).
  }
  apply pos_mult_compat;[|apply _].
  red. apply (snd (flip_pos_minus _ _)). trivial.
- apply flip_pos_minus.
  assert (Hrw : r - (q + r) / 2 = (r - q) / 2);[|rewrite Hrw;clear Hrw].
  { path_via (2 / 2 * r - (q + r) / 2).
    { rewrite dec_recip_inverse;[|solve_propholds].
      rewrite mult_1_l;trivial.
    }
    ring_tac.ring_with_integers (NatPair.Z nat).
  }
  apply pos_mult_compat;[|apply _].
  red. apply (snd (flip_pos_minus _ _)). trivial.
Qed.

Lemma pos_gt_both : forall a b : Q, forall e, a < ' e -> b < ' e ->
  exists d d', a < ' d /\ b < ' d /\ e = d + d'.
Proof.
assert (Haux : forall a b : Q, a <= b -> forall e, a < ' e -> b < ' e ->
  exists d d', a < ' d /\ b < ' d /\ e = d + d').
{ intros a b E e E1 E2.
  pose proof (Q_average_between _ _ (Qlt_join _ 0 _ E2 prop_holds)) as [E3 E4].
  exists (mkQpos _ (le_lt_trans _ _ _ (join_ub_r _ _) E3)).
  unfold cast at 1 4;simpl.
  exists (Qpos_diff _ _ E4).
  repeat split.
  - apply le_lt_trans with b;trivial.
    apply le_lt_trans with (join b 0);trivial.
    apply join_ub_l.
  - apply le_lt_trans with (join b 0);trivial. apply join_ub_l.
  - apply pos_eq. unfold cast at 2;simpl. unfold cast at 2;simpl.
    unfold cast at 3;simpl.
    abstract ring_tac.ring_with_integers (NatPair.Z nat).
}
intros a b e E1 E2. destruct (total le a b) as [E|E];auto.
destruct (Haux _ _ E e) as [d [d' [E3 [E4 E5]]]];trivial.
eauto.
Qed.

Lemma two_fourth_is_one_half@{} : 2/4 =  1/2 :> Q+.
Proof.
assert (Hrw : 4 = 2 * 2 :> Q) by ring_tac.ring_with_nat.
apply pos_eq. repeat (unfold cast;simpl).
rewrite Hrw;clear Hrw.
rewrite dec_recip_distr.
rewrite mult_assoc. rewrite dec_recip_inverse;[|solve_propholds].
reflexivity.
Unshelve. exact (fun _ => 1). (* <- wtf *)
Qed.

Lemma Q_triangle_le : forall q r : Q, abs (q + r) <= abs q + abs r.
Proof.
intros. rewrite (Qabs_is_join (q + r)).
apply join_le.
- rewrite negate_plus_distr.
  apply plus_le_compat;apply Qabs_le_neg_raw.
- apply plus_le_compat;apply Qabs_le_raw.
Qed.

Lemma Qabs_triangle_alt_aux : forall x y : Q, abs x - abs y <= abs (x - y).
Proof.
intros q r.
apply (order_reflecting (+ (abs r))).
assert (Hrw : abs q - abs r + abs r = abs q)
  by ring_tac.ring_with_integers (NatPair.Z nat);
rewrite Hrw;clear Hrw.
etransitivity;[|apply Q_triangle_le].
assert (Hrw : q - r + r = q)
  by ring_tac.ring_with_integers (NatPair.Z nat);
rewrite Hrw;clear Hrw.
reflexivity.
Qed.

Lemma Qabs_triangle_alt : forall x y : Q, abs (abs x - abs y) <= abs (x - y).
Proof.
intros q r.
rewrite (Qabs_is_join (abs q - abs r)).
apply join_le.
- rewrite <-(Qabs_neg (q - r)),<-!negate_swap_r.
  apply Qabs_triangle_alt_aux.
- apply Qabs_triangle_alt_aux.
Qed.

Lemma Q_dense@{} : forall q r : Q, q < r -> exists s, q < s < r.
Proof.
intros q r E;econstructor;apply Q_average_between,E.
Qed.

Lemma Qabs_neg_flip@{} : forall a b : Q, abs (a - b) = abs (b - a).
Proof.
intros a b.
rewrite <-Qabs_neg. rewrite <-negate_swap_r. trivial.
Qed.

Definition pos_of_Q : Q -> Q+
  := fun q => {| pos := abs q + 1;
    is_pos := le_lt_trans _ _ _ (Qabs_nonneg q)
                (fst (pos_plus_lt_compat_r _ _) lt_0_1) |}.

Lemma Q_abs_plus_1_bounds@{} : forall q : Q,
  - ' (pos_of_Q q) ≤ q
  ≤ ' (pos_of_Q q).
Proof.
intros. change (- (abs q + 1) ≤ q ≤ (abs q + 1)). split.
- apply flip_le_negate. rewrite involutive.
  transitivity (abs q).
  + apply Qabs_le_neg_raw.
  + apply nonneg_plus_le_compat_r. solve_propholds.
- transitivity (abs q).
  + apply Qabs_le_raw.
  + apply nonneg_plus_le_compat_r. solve_propholds.
Qed.

Lemma Qabs_mult@{} : forall a b : Q, abs (a * b) = abs a * abs b.
Proof.
intros a b.
destruct (total_abs_either a) as [Ea|Ea];destruct Ea as [Ea1 Ea2];rewrite Ea2;
destruct (total_abs_either b) as [Eb|Eb];destruct Eb as [Eb1 Eb2];rewrite Eb2.
- apply ((abs_sig (a*b)).2). apply nonneg_mult_compat;trivial.
- rewrite <-negate_mult_distr_r.
  apply ((abs_sig (a*b)).2). apply nonneg_nonpos_mult;trivial.
- rewrite <-negate_mult_distr_l.
  apply ((abs_sig (a*b)).2). apply nonpos_nonneg_mult;trivial.
- rewrite negate_mult_negate. apply ((abs_sig (a*b)).2).
  apply nonpos_mult;trivial.
Qed.

Lemma Qpos_neg_le@{} : forall a : Q+, - ' a <= ' a.
Proof.
intros a;apply between_nonneg;solve_propholds.
Qed.

Definition Qpos_upper (e : Q+) := exists x : Q, ' e <= x.

Definition Qpos_upper_inject e : Q -> Qpos_upper e.
Proof.
intros x. exists (join x (' e)). apply join_ub_r.
Defined.

Global Instance QLe_dec : forall q r : Q, Decidable (q <= r).
Proof.
intros q r;destruct (le_or_lt q r).
- left;trivial.
- right;intros ?. apply (irreflexivity lt q).
  apply le_lt_trans with r;trivial.
Qed.

Global Instance QLt_dec : forall q r : Q, Decidable (q < r).
Proof.
intros q r;destruct (le_or_lt r q).
- right;intros ?. apply (irreflexivity lt q).
  apply lt_le_trans with r;trivial.
- left;trivial.
Qed.

Section enumerable.
Context `{Enumerable Q}.

Definition Qpos_enumerator : nat -> Q+.
Proof.
intros n.
destruct (le_or_lt (enumerator Q n) 0) as [E|E].
- exact 1.
- exists (enumerator Q n);trivial.
Defined.

Lemma Qpos_is_enumerator :
  TrM.RSU.IsConnMap@{Uhuge Ularge UQ UQ Ularge} (trunc_S minus_two) Qpos_enumerator.
Proof.
apply BuildIsSurjection.
unfold hfiber.
intros e;generalize (center _ (enumerator_issurj Q (' e))). apply (Trunc_ind _).
intros [n E]. apply tr;exists n.
unfold Qpos_enumerator. destruct (le_or_lt (enumerator Q n) 0) as [E1|E1].
- destruct (irreflexivity lt 0). apply lt_le_trans with (enumerator Q n);trivial.
  rewrite E;solve_propholds.
- apply pos_eq,E.
Qed.

Global Instance Qpos_enumerable `{Enumerable Q} : Enumerable Q+.
Proof.
  exists Qpos_enumerator.
  first [exact Qpos_is_enumerator@{Uhuge Ularge}|
         exact Qpos_is_enumerator@{}].
Qed.

End enumerable.

End contents.

Arguments Qpos Q {_ _}.
