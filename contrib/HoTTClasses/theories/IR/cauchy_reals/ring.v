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
  HoTTClasses.IR.cauchy_reals.order
  HoTTClasses.IR.cauchy_reals.metric.

Local Set Universe Minimization ToSet.

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

Lemma R_bounded_2@{} : forall u v,
  merely (exists d : Q+, abs u < rat (' d) /\ abs v < rat (' d)).
Proof.
intros.
apply (merely_destruct (R_Qpos_bounded u)).
intros [d Ed].
apply (merely_destruct (R_Qpos_bounded v)).
intros [n En].
apply tr;exists (join d n).
repeat split.
- apply R_lt_le_trans with (rat (' d));trivial.
  apply rat_le_preserving,join_ub_l.
- apply R_lt_le_trans with (rat (' n));trivial.
  apply rat_le_preserving,join_ub_r.
Qed.

Definition QRmult@{} : Q -> real -> real
  := fun q => lipschitz_extend _ (Compose rat (q *.)) (pos_of_Q q).

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
intros s;apply (ap rat). symmetry;apply distribute_r.
Qed.

Lemma QRmult_lipschitz_interval_aux (a:Q+)
  : forall x, abs x <= rat (' a) ->
  forall q r : Q, abs (QRmult q x - QRmult r x) <= rat (abs (q - r) * ' a).
Proof.
intros x E q r. rewrite QRmult_negate,QRmult_plus_distr.
change (rat (abs (q - r) * ' a)) with (QRmult (abs (q - r)) (rat (' a))).
rewrite <-E. clear E.
revert x;apply (unique_continuous_extension _).
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
    Lipschitz (fun q : Q => QRmult q (interval_proj _ _ v)) a.
Proof.
intros v e x y xi.
apply Qclose_alt in xi. apply metric_to_equiv.
eapply R_le_lt_trans.
+ apply (QRmult_lipschitz_interval_aux a).
  apply (snd (Rabs_le_pr _ _)).
  split;apply v.2.
+ apply rat_lt_preserving. rewrite mult_comm.
  apply pos_mult_le_lt_compat;try split;try solve_propholds.
  * reflexivity.
  * apply Qabs_nonneg.
Qed.

Definition Rbounded_mult@{} (a : Q+)
  : real -> Interval (- rat (' a)) (rat (' a)) -> real
  := fun u v => lipschitz_extend _
      (fun q => QRmult q (interval_proj _ _ v)) a u.

Instance Rbounded_mult_lipschitz : forall a v,
  Lipschitz (fun u => Rbounded_mult a u v) a
  := _.
Typeclasses Opaque Rbounded_mult.

Definition interval_back
  : sigT (fun a : Q+ => Interval (- rat (' a)) (rat (' a))) -> real
  := fun x => x.2.1.

Instance interval_proj_issurj@{}
  : TrM.RSU.IsConnMap@{Uhuge Ularge UQ UQ Ularge} (trunc_S minus_two) interval_back.
Proof.
apply BuildIsSurjection. intros x.
generalize (R_Qpos_bounded x). apply (Trunc_ind _);intros [q E].
apply tr. simple refine (existT _ _ _).
- exists q. exists x. apply Rabs_le_pr. apply R_lt_le. exact E.
- simpl. reflexivity.
Defined.

Lemma Rbounded_mult_respects : forall z x y, interval_back x = interval_back y ->
  Rbounded_mult x.1 z x.2 = Rbounded_mult y.1 z y.2.
Proof.
intros z x y E.
revert z. apply (unique_continuous_extension _ _ _).
intros q. unfold Rbounded_mult.
exact (ap _ E).
Qed.

Definition Rmult@{} : Mult real
  := fun x => jections.surjective_factor@{UQ UQ UQ Uhuge Ularge
    Ularge UQ UQ Uhuge Ularge} _ interval_back (Rbounded_mult_respects x).
Global Existing Instance Rmult.

Lemma Rmult_pr@{} x : (fun y => Rbounded_mult y.1 x y.2) =
  Compose (x *.) interval_back.
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
  Lipschitz (.* (interval_proj (rat (- ' a)) (rat (' a)) y)) a.
Proof.
intros a y. rewrite Rmult_interval_proj. apply _.
Qed.

Lemma Rmult_lipschitz_aux_alt : forall a y, abs y <= rat (' a) ->
  Lipschitz (.* y) a.
Proof.
intros a y E. apply Rabs_le_pr in E.
change y with (interval_proj (rat (- ' a)) (rat (' a)) (existT _ y E)).
apply Rmult_lipschitz_aux.
Qed.

Instance Rmult_continuous_r@{} : forall y : real, Continuous (.* y).
Proof.
intros. red. apply (merely_destruct (R_Qpos_bounded y)).
intros [a Eq]. apply R_lt_le in Eq. apply Rabs_le_pr in Eq.
change (Continuous (.* y)). eapply lipschitz_continuous.
change (.* y) with (.* (interval_proj (rat (- ' a)) (rat (' a)) (existT _ y Eq))).
apply Rmult_lipschitz_aux.
Qed.

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
  apply _.
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

Lemma Rmult_continuous@{} : Continuous (uncurry (@mult real _)).
Proof.
intros [u1 v1] e.
apply (merely_destruct (R_bounded_2 u1 v1));intros [d [Ed1 Ed2]].
pose (k := d + 1).
(* assert (Ed3 : ' d < ' k). { apply pos_plus_lt_compat_r;solve_propholds. } *)
apply tr;exists (meet 1 (e / 2 / (k + 1)));
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
    * change (' d <= ' d + 1 + 1). rewrite <-plus_assoc.
      apply nonneg_plus_le_compat_r. solve_propholds.
- apply metric_to_equiv. rewrite Rmult_abs_l.
  apply R_le_lt_trans with (abs (rat (' k)) * abs (rat (' (e / 2 / (k + 1))))).
  + apply Rmult_le_compat_abs.
    * change (abs (rat (' k))) with (rat (abs (' k))).
      unfold abs at 2. rewrite (fst (abs_sig (' _)).2);[|solve_propholds].
      unfold k.
      eapply Rle_close_rat;[|apply (non_expanding abs (x:=u1))].
      ** apply R_lt_le;trivial.
      ** eapply rounded_le;[exact xi1|]. apply meet_lb_l. 
    * change (abs (rat (' (e / 2 / (k + 1))))) with
        (rat (abs (' (e / 2 / (k + 1))))).
      unfold abs at 2. rewrite (fst (abs_sig (' _)).2);[|solve_propholds].
      apply equiv_to_metric in xi2.
      etransitivity;[apply R_lt_le,xi2|].
      apply rat_le_preserving,meet_lb_r.
  + apply rat_lt_preserving.
    rewrite <-Qabs_mult.
    change (' k * ' (e / 2 / (k + 1))) with
      (' (k * (e / 2 / (k + 1)))).
    unfold abs;rewrite (fst (abs_sig (' _)).2);[|solve_propholds].
    assert (Hrw : e / 2 = (e / 2) * 1)
      by (apply pos_eq;ring_tac.ring_with_nat);
    rewrite Hrw;clear Hrw.
    assert (Hrw : k * (e / 2 * 1 / (k + 1)) = (e / 2) * (k / (k + 1)))
      by (apply pos_eq;ring_tac.ring_with_nat);
    rewrite Hrw;clear Hrw.
    apply pos_mult_le_lt_compat;try split;try solve_propholds.
    * reflexivity.
    * apply (strictly_order_reflecting (.* (' (k + 1)))).
      unfold cast;simpl. unfold cast at 2;simpl.
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

Instance Rmult_nonneg_compat : forall x y : real, PropHolds (0 ≤ x) ->
  PropHolds (0 ≤ y) ->
  PropHolds (0 ≤ x * y).
Proof.
unfold PropHolds.
intros x y E1 E2;rewrite <-E1,<-E2;clear E1 E2.
revert x y;apply unique_continuous_binary_extension.
- change (Continuous ((join 0) ∘ uncurry (@mult real _) ∘ map2 (join 0) (join 0))).
  apply continuous_compose;[|apply _]. apply continuous_compose;[apply _|].
  apply _.
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
