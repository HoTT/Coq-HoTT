(** * Spaces of uniformly continuous functions *)

(** We work on closed intervals [[a, b]] of an Archimedean ordered field, with the distance [|x - y|]. A uniformly continuous function on [[a, b]] has a supremum, computed as the limit of its maxima at finitely many equidistant points, with an explicit modulus of Cauchy convergence. The maps [[a, b] -> [c, d]] with a modulus of uniform continuity form a pseudometric space with the supremum distance, and those which additionally lift to locators form a Cauchy complete pseudometric space, in which maps at distance zero have equal underlying maps. *)

From HoTT Require Import Basics Types.Sigma Truncations.Core.
From HoTT.Spaces Require Import Nat.Core.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.naturals
  interfaces.rationals
  interfaces.archimedean
  interfaces.cauchy
  interfaces.round
  implementations.peano_naturals
  theory.rings
  theory.dec_fields
  theory.rationals
  orders.orders
  orders.rings
  orders.naturals
  orders.lattices
  orders.dec_fields
  orders.rationals.
From HoTT.Analysis Require Import Locator.
From HoTT_Contrib.Analysis Require Import
  MetricSpace CauchyCompleteness LiftsToLocators IntermediateValue.

Section function_space.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}.
  Context (F : Type) `{Forderedfield : OrderedField F} {Fabs : Abs F}.
  Context {Farch : ArchimedeanProperty Q F} {Qroundup : RoundUpStrict Q}.

  Local Existing Instance qinc.
  Local Instance orderpreserving_qinc : OrderPreserving (qinc Q F)
    := full_pseudo_order_preserving.

  Local Notation nQ := (naturals_to_semiring nat Q).
  Local Notation dF := (fun u v : F => abs (u - v)).

  (** ** Closed intervals *)

  (** The closed interval [[a, b]] is the type of elements of [F] between [a] and [b]. *)
  Definition ClosedInterval (a b : F) := {x : F & a ≤ x ≤ b}.

  (** The distance on a closed interval is the distance of [F]. *)
  Definition interval_dist {a b : F} (x y : ClosedInterval a b) : F := abs (x.1 - y.1).

  #[export] Instance ispseudometric_interval_dist (a b : F)
    : IsPseudoMetric (@interval_dist a b)
    := ispseudometric_pullback pr1 dF.

  Local Notation closeI := (metric_close Q interval_dist).
  Local Notation closeF := (metric_close Q dF).

  Section endpoints.
    Context {a b : F} (leab : a ≤ b).

    Definition interval_left : ClosedInterval a b := (a; (reflexivity a, leab)).

    Definition interval_right : ClosedInterval a b := (b; (leab, reflexivity b)).
  End endpoints.

  (** ** Points between two points of an interval *)

  Local Lemma qinc_nonneg (t : Q) (t0 : 0 ≤ t) : 0 ≤ (' t : F).
  Proof.
    rewrite <- (preserves_0 (f:=cast Q F)); exact (order_preserving _ _ _ t0).
  Qed.

  Local Lemma qinc_le_1 (t : Q) (t1 : t ≤ 1) : (' t : F) ≤ 1.
  Proof.
    rewrite <- (preserves_1 (f:=cast Q F)); exact (order_preserving _ _ _ t1).
  Qed.

  (** Moving from [u] towards [v] by a fraction [s] is a convex combination. *)
  Local Lemma convex_combination (s u v : F) : u + s * (v - u) = (1 - s) * u + s * v.
  Proof.
    rewrite plus_mult_distr_r, mult_1_l, plus_mult_distr_l, <- plus_assoc.
    apply ap; rewrite plus_comm.
    apply (ap (+ _)).
    rewrite <- negate_mult_distr_r, negate_mult_distr_l; reflexivity.
  Qed.

  (** Convex combinations of elements of [[a, b]] lie in [[a, b]]. *)
  Local Lemma convex_combination_bounds (a b s u v : F) (s0 : 0 ≤ s) (s1 : s ≤ 1)
    (au : a ≤ u ≤ b) (av : a ≤ v ≤ b)
    : a ≤ (1 - s) * u + s * v ≤ b.
  Proof.
    assert (s1' : 0 ≤ 1 - s) by exact (snd (flip_nonneg_minus s 1) s1).
    assert (p : forall w : F, (1 - s) * w + s * w = w).
    { intro w; rewrite <- plus_mult_distr_r, <- plus_assoc, plus_negate_l, plus_0_r.
      apply mult_1_l. }
    split.
    - rewrite <- (p a); apply plus_le_compat.
      + exact (order_preserving ((1 - s) *.) _ _ (fst au)).
      + exact (order_preserving (s *.) _ _ (fst av)).
    - rewrite <- (p b); apply plus_le_compat.
      + exact (order_preserving ((1 - s) *.) _ _ (snd au)).
      + exact (order_preserving (s *.) _ _ (snd av)).
  Qed.

  Local Lemma recip_mult_lt (B W N : Q) (W0 : 0 < W) (N0 : 0 < N) (lt : B / W < N)
    : / N * B < W.
  Proof.
    assert (PropHolds (0 < W)) by exact W0.
    assert (PropHolds (0 < N)) by exact N0.
    apply (strictly_order_reflecting (N *.)).
    rewrite mult_assoc, (dec_recip_inverse N (lt_ne_flip _ _ N0)), mult_1_l.
    rewrite <- (mult_1_r B), <- (dec_recip_inverse W (lt_ne_flip _ _ W0)).
    rewrite (mult_comm W), mult_assoc.
    exact (strictly_order_preserving (.* W) _ _ lt).
  Qed.

  Section convex.
    Context {a b : F} (x y : ClosedInterval a b).

    (** The point a fraction [t] of the way from [x] to [y]. *)
    Definition interval_point (t : Q) (t0 : 0 ≤ t) (t1 : t ≤ 1) : ClosedInterval a b.
    Proof.
      exists (x.1 + ' t * (y.1 - x.1)).
      rewrite convex_combination.
      exact (convex_combination_bounds a b _ _ _ (qinc_nonneg t t0) (qinc_le_1 t t1) x.2 y.2).
    Defined.

    (** ** Equidistant points *)

    Local Lemma nQ_succ_pos (n : nat) : 0 < nQ (S n).
    Proof.
      apply nat_to_semiring_succ_pos.
    Qed.

    (** The fractions [k / (n + 1)], with [k] capped at [n + 1]. *)
    Definition grid_weight (n k : nat) : Q := nQ (nat_min k (S n)) / nQ (S n).

    Local Lemma grid_weight_nonneg (n k : nat) : 0 ≤ grid_weight n k.
    Proof.
      unfold grid_weight; apply nonneg_mult_compat; [apply nat_to_semiring_nonneg|].
      apply lt_le, pos_dec_recip_compat, nQ_succ_pos.
    Qed.

    Local Lemma recip_nQ_succ (n : nat) : nQ (S n) / nQ (S n) = 1.
    Proof.
      apply dec_recip_inverse, lt_ne_flip, nQ_succ_pos.
    Qed.

    Local Lemma grid_weight_le_1 (n k : nat) : grid_weight n k ≤ 1.
    Proof.
      unfold grid_weight; rewrite <- (recip_nQ_succ n).
      assert (PropHolds (0 < / nQ (S n))) by apply pos_dec_recip_compat, nQ_succ_pos.
      apply (order_preserving (.* / nQ (S n))), nat_to_semiring_le, leq_nat_min_r.
    Qed.

    (** The [k]th of [n + 2] equidistant points from [x] to [y]; the points with [k > n + 1] are all [y]. *)
    Definition grid_point (n k : nat) : ClosedInterval a b
      := interval_point (grid_weight n k) (grid_weight_nonneg n k) (grid_weight_le_1 n k).

    (** The distance between consecutive points, which may be negative. *)
    Definition grid_step (n : nat) : F := ' (/ nQ (S n)) * (y.1 - x.1).

    Lemma grid_step_nonneg (n : nat) (lexy : x.1 ≤ y.1) : 0 ≤ grid_step n.
    Proof.
      apply nonneg_mult_compat.
      - apply qinc_nonneg, lt_le, pos_dec_recip_compat, nQ_succ_pos.
      - exact (snd (flip_nonneg_minus _ _) lexy).
    Qed.

    Lemma grid_point_succ (n k : nat) (lekn : (k <= n)%nat)
      : (grid_point n (S k)).1 = (grid_point n k).1 + grid_step n.
    Proof.
      change (x.1 + ' (grid_weight n (S k)) * (y.1 - x.1)
              = x.1 + ' (grid_weight n k) * (y.1 - x.1) + grid_step n).
      unfold grid_step, grid_weight.
      rewrite (nat_min_l (leq_succ lekn)), (nat_min_l (leq_succ_r lekn)).
      rewrite nat_to_semiring_succ, plus_mult_distr_r, mult_1_l.
      rewrite (preserves_plus (f:=cast Q F)), plus_mult_distr_r.
      rewrite (plus_comm (' (/ nQ (S n)) * _)), plus_assoc.
      reflexivity.
    Qed.

    Lemma grid_point_0 (n : nat) : grid_point n 0 = x.
    Proof.
      apply path_sigma_hprop.
      change (x.1 + ' (grid_weight n 0) * (y.1 - x.1) = x.1); unfold grid_weight.
      rewrite nat_min_zero_l, (preserves_0 (f:=nQ)), mult_0_l, (preserves_0 (f:=cast Q F)), mult_0_l.
      apply plus_0_r.
    Qed.

    Lemma grid_point_last (n : nat) : grid_point n (S n) = y.
    Proof.
      apply path_sigma_hprop.
      change (x.1 + ' (grid_weight n (S n)) * (y.1 - x.1) = y.1); unfold grid_weight.
      rewrite nat_min_idem, recip_nQ_succ, (preserves_1 (f:=cast Q F)), mult_1_l.
      rewrite plus_comm, <- plus_assoc, plus_negate_l; apply plus_0_r.
    Qed.

    (** For a rational bound [B] on the distance from [x] to [y] and a modulus [w], an [n] with [B / w e < n], so that from [n] on the points are closer together than [w e]. *)
    Definition grid_modulus (B : Q) (w : Qpos Q -> Qpos Q) (e : Qpos Q) : nat
      := (round_up_strict Q (B / ' (w e))).1.

    (** In particular [grid_step n < w e] when [y - x ≤ B]. *)
    Lemma lt_grid_modulus (D : F) (B : Q) (leB : D ≤ ' B) (w : Qpos Q -> Qpos Q)
      (e : Qpos Q) (n : nat) (len : (grid_modulus B w e <= n)%nat)
      : ' (/ nQ (S n)) * D < ' (' (w e)).
    Proof.
      assert (lt : B / ' (w e) < nQ (S n)).
      { refine (lt_le_trans _ _ _ (round_up_strict Q (B / ' (w e))).2 _).
        exact (nat_to_semiring_le _ _ (leq_succ_r len)). }
      apply (recip_mult_lt _ _ _ (pos_is_pos (w e)) (nQ_succ_pos n)) in lt.
      assert (PropHolds (0 ≤ (' (/ nQ (S n)) : F))).
      { apply qinc_nonneg, lt_le, pos_dec_recip_compat, nQ_succ_pos. }
      refine (le_lt_trans _ _ _ (order_preserving (' (/ nQ (S n)) *.) _ _ leB) _).
      rewrite <- (preserves_mult (f:=cast Q F)).
      exact (strictly_order_preserving _ _ _ lt).
    Qed.

  End convex.

  (** ** Finding a nearby point *)

  (** If consecutive points [p k] are less than [d] apart, then any [z] between [p 0] and [p N] merely lies within [d] above one of them. Comparing [z] with each point in turn uses cotransitivity, so we only get mere existence. *)
  Lemma merely_near_point (p : nat -> F) (N : nat) (d z : F)
    (step : forall k, (k < N)%nat -> p (S k) < p k + d) (d0 : 0 < d)
    (lo : p 0 ≤ z) (hi : z ≤ p N)
    : merely {k : nat & prod (prod (k <= N)%nat (p k ≤ z)) (z < p k + d)}.
  Proof.
    assert (scan : forall j, (j <= N)%nat
                   -> merely ({k : nat & prod (prod (k <= N)%nat (p k ≤ z)) (z < p k + d)}
                              + (p j ≤ z))).
    { intro j; induction j as [|j IH]; intro lejN.
      - exact (tr (inr lo)).
      - assert (h := IH (leq_succ_l lejN)); strip_truncations.
        destruct h as [found|lez]; [exact (tr (inl found))|].
        assert (c := cotransitive (step j lejN) z); strip_truncations; apply tr.
        destruct c as [lt|lt].
        + exact (inr (lt_le _ _ lt)).
        + exact (inl (j; (leq_succ_l lejN, lez, lt))). }
    assert (h := scan N (leq_refl N)); strip_truncations; apply tr.
    destruct h as [found|lez]; [exact found|].
    exists N; refine (leq_refl N, lez, _).
    exact (le_lt_trans _ _ _ hi (fst (pos_plus_lt_compat_r _ _) d0)).
  Qed.

  (** ** Finite maxima *)

  (** The maximum of the values [g 0], ..., [g n]. *)
  Fixpoint max_upto (g : nat -> F) (n : nat) : F
    := match n with
       | O => g O
       | S n => join (max_upto g n) (g (S n))
       end.

  Lemma le_max_upto (g : nat -> F) (n k : nat) (lekn : (k <= n)%nat) : g k ≤ max_upto g n.
  Proof.
    induction n as [|n IH].
    - rewrite (path_zero_leq_zero_r k lekn); reflexivity.
    - destruct (leq_succ_dichotomy lekn) as [p|lekn'].
      + rewrite p; exact (join_ub_r (max_upto g n) _).
      + exact (transitivity (IH lekn') (join_ub_l _ (g (S n)))).
  Qed.

  Lemma max_upto_lt (g : nat -> F) (n : nat) (c : F)
    (lt : forall k, (k <= n)%nat -> g k < c)
    : max_upto g n < c.
  Proof.
    induction n as [|n IH].
    - exact (lt 0 (leq_refl 0)).
    - change (join (max_upto g n) (g (S n)) < c); apply join_lt_r.
      + exact (IH (fun k lekn => lt k (leq_succ_r lekn))).
      + exact (lt (S n) (leq_refl _)).
  Qed.

  Lemma max_upto_le (g : nat -> F) (n : nat) (c : F)
    (le : forall k, (k <= n)%nat -> g k ≤ c)
    : max_upto g n ≤ c.
  Proof.
    induction n as [|n IH].
    - exact (le 0 (leq_refl 0)).
    - change (join (max_upto g n) (g (S n)) ≤ c); apply join_le.
      + exact (IH (fun k lekn => le k (leq_succ_r lekn))).
      + exact (le (S n) (leq_refl _)).
  Qed.

  (** ** Suprema *)

  (** An element [s] is the supremum of [g] if it is a least upper bound of its values. *)
  Definition IsSupremum {X : Type} (g : X -> F) (s : F)
    := ((forall x, g x ≤ s) * (forall u, (forall x, g x ≤ u) -> s ≤ u))%type.

  (** Suprema are monotone. *)
  Definition supremum_le {X : Type} (g h : X -> F) (s t : F) (gs : IsSupremum g s)
    (ht : IsSupremum h t) (le : forall x, g x ≤ h x)
    : s ≤ t
    := snd gs t (fun x => transitivity (le x) (fst ht x)).

  Section supremum.
    Context {a b : F} (leab : a ≤ b) (f : ClosedInterval a b -> F).

    (** The maximum of [f] at [n + 2] equidistant points. *)
    Definition sample_max (n : nat) : F
      := max_upto (fun k => f (grid_point (interval_left leab) (interval_right leab) n k)) (S n).

    (** If the points are closer together than a modulus of [f] for [e], then the values of [f] are less than the maximum plus [e]. *)
    Lemma lt_sample_max (w : Qpos Q -> Qpos Q) (fw : IsUniformModulus Q closeI closeF f w)
      (e : Qpos Q) (n : nat)
      (ltstep : grid_step (interval_left leab) (interval_right leab) n < ' (' (w e)))
      (z : ClosedInterval a b)
      : f z < sample_max n + ' (' e).
    Proof.
      set (p := fun k => grid_point (interval_left leab) (interval_right leab) n k).
      assert (step : forall k, (k < S n)%nat -> (p (S k)).1 < (p k).1 + ' (' (w e))).
      { intros k ltk; unfold p; rewrite (grid_point_succ _ _ n k (leq_pred' ltk)).
        exact (strictly_order_preserving (_ +) _ _ ltstep). }
      assert (lo : (p 0%nat).1 ≤ z.1) by (unfold p; rewrite grid_point_0; exact (fst z.2)).
      assert (hi : z.1 ≤ (p (S n)).1) by (unfold p; rewrite grid_point_last; exact (snd z.2)).
      assert (c := merely_near_point (fun k => (p k).1) (S n) _ z.1 step
                     (pos_rationals_to_field_qpos Q (w e)) lo hi).
      strip_truncations; destruct c as [k [[lekn lez] ltz]].
      assert (cz : closeI (w e) z (p k)).
      { unfold metric_close, interval_dist.
        rewrite (abs_of_nonneg _ (snd (flip_nonneg_minus _ _) lez)).
        exact (snd (flip_lt_minus_l _ _ _) (lt_eq_trans _ _ _ ltz (plus_comm _ _))). }
      assert (ltf := le_lt_trans _ _ _ (le_abs _) (fw e z (p k) cz)).
      apply (fst (flip_lt_minus_l _ _ _)) in ltf.
      refine (lt_le_trans _ _ _ ltf _); rewrite (plus_comm (' (' e))).
      apply (order_preserving (+ _)).
      exact (le_max_upto (fun k => f (p k)) (S n) k lekn).
    Qed.

    (** The maxima form a sequence with a modulus of Cauchy convergence. *)
    Lemma cauchymodulus_sample_max (B : Q) (leB : b - a ≤ ' B) (w : Qpos Q -> Qpos Q)
      (fw : IsUniformModulus Q closeI closeF f w)
      : CauchyModulus Q F sample_max (grid_modulus B w).
    Proof.
      intros e m n lem len.
      assert (lt : forall m' n', (grid_modulus B w e <= n')%nat
                     -> sample_max m' < sample_max n' + ' (' e)).
      { intros m' n' len'; apply max_upto_lt; intros k _.
        exact (lt_sample_max w fw e n' (lt_grid_modulus _ B leB w e n' len') _). }
      split.
      - apply flip_lt_minus_r; rewrite plus_comm.
        apply flip_lt_minus_l; exact (lt n m lem).
      - apply flip_lt_minus_l; rewrite plus_comm; exact (lt m n len).
    Qed.

    (* [merely_bound] in IntermediateValue.v is a variant of this lemma that uses [a ≤ b] to give a positive bound; sharing it would mean stating it outside its section there and passing [' B] for [B] below. *)
    Local Lemma merely_rational_bound : merely {B : Q & b - a ≤ ' B}.
    Proof.
      assert (c := archimedean_property Q F (b - a) (b - a + 1)
                     (fst (pos_plus_lt_compat_r _ _) lt_0_1)).
      strip_truncations; destruct c as [B [ltB _]].
      exact (tr (B; lt_le _ _ ltB)).
    Qed.

    (** A limit of the maxima is a supremum of [f]. *)
    Lemma issupremum_limit_sample_max (fu : IsUniformlyContinuous Q closeI closeF f) (l : F)
      (islim : IsLimit Q F sample_max l)
      : IsSupremum f l.
    Proof.
      split.
      - intro z.
        apply (fst (flip_nonpos_minus _ _)), (nonpos_lt_qpos Q); intro e.
        assert (c := merely_rational_bound).
        strip_truncations; destruct fu as [w fw], c as [B leB].
        assert (le : f z - ' (' (e / 2)) ≤ l).
        { apply (le_limit Q F sample_max l _ (grid_modulus B w (e / 2)) islim).
          intros n len; apply lt_le, flip_lt_minus_l.
          exact (lt_sample_max w fw (e / 2) n (lt_grid_modulus _ B leB w _ n len) z). }
        apply (fst (flip_le_minus_l _ _ _)) in le.
        rewrite plus_comm in le; apply (snd (flip_le_minus_l _ _ _)) in le.
        refine (le_lt_trans _ _ _ le _).
        exact (strictly_order_preserving (cast Q F) _ _ (qpos_half_lt e)).
      - intros u ub.
        apply (limit_le Q F sample_max l u 0 islim); intros n _.
        apply max_upto_le; intros k _; apply ub.
    Qed.

    Lemma merely_cauchymodulus_sample_max (fu : IsUniformlyContinuous Q closeI closeF f)
      : hexists (CauchyModulus Q F sample_max).
    Proof.
      assert (c := merely_rational_bound).
      strip_truncations; destruct fu as [w fw], c as [B leB].
      exact (tr (_; cauchymodulus_sample_max B leB w fw)).
    Qed.

    Context `{Funext} `{!IsComplete Q F}.

    (** The supremum of a uniformly continuous function on a closed interval, as the limit of the maxima. *)
    Definition supremum (fu : IsUniformlyContinuous Q closeI closeF f) : F
      := (limit_complete Q sample_max (merely_cauchymodulus_sample_max fu)).1.

    Definition issupremum_supremum (fu : IsUniformlyContinuous Q closeI closeF f)
      : IsSupremum f (supremum fu)
      := issupremum_limit_sample_max fu _
           (limit_complete Q sample_max (merely_cauchymodulus_sample_max fu)).2.

  End supremum.

  (** ** The distance between two maps at a point *)

  (** If [f] and [g] are uniformly continuous with moduli [wf] and [wg], then so is their pointwise distance, with the minimum of the moduli at [e / 2] as modulus. *)
  Lemma isuniformmodulus_pointwise_dist {X Y : Type} (dX : X -> X -> F) (dY : Y -> Y -> F)
    `{!IsPseudoMetric dY} (f g : X -> Y) (wf wg : Qpos Q -> Qpos Q)
    (fw : IsUniformModulus Q (metric_close Q dX) (metric_close Q dY) f wf)
    (gw : IsUniformModulus Q (metric_close Q dX) (metric_close Q dY) g wg)
    : IsUniformModulus Q (metric_close Q dX) closeF (fun x => dY (f x) (g x))
        (fun e => qpos_min Q (wf (e / 2)) (wg (e / 2))).
  Proof.
    intros e x y c; unfold metric_close in *.
    assert (cf : dY (f x) (f y) < ' (' (e / 2))).
    { apply fw; refine (lt_le_trans _ _ _ c _).
      apply (order_preserving (cast Q F)), qpos_min_le_l. }
    assert (cg : dY (g x) (g y) < ' (' (e / 2))).
    { apply gw; refine (lt_le_trans _ _ _ c _).
      apply (order_preserving (cast Q F)), qpos_min_le_r. }
    (* Each distance is at most the other plus the two distances between the points. *)
    assert (le : forall u v u' v', dY u v ≤ dY u u' + dY u' v' + dY v' v).
    { intros u v u' v'.
      lhs' exact (pseudometric_triangle (d:=dY) u u' v).
      rewrite <- plus_assoc; apply (order_preserving (_ +)).
      apply (pseudometric_triangle (d:=dY)). }
    assert (lt : forall u v u' v', dY u u' < ' (' (e / 2)) -> dY v v' < ' (' (e / 2))
                   -> dY u v - dY u' v' < ' (' e)).
    { intros u v u' v' cu cv; apply flip_lt_minus_l.
      refine (le_lt_trans _ _ _ (le u v u' v') _).
      rewrite <- plus_assoc, (plus_comm (dY u' v')), plus_assoc.
      apply (strictly_order_preserving (+ _)).
      rewrite (pos_split2 e), (preserves_plus (f:=cast Q F)).
      rewrite (pseudometric_symmetric (d:=dY) v' v).
      exact (plus_lt_compat _ _ _ _ cu cv). }
    apply abs_lt.
    - apply flip_lt_negate_l; rewrite <- negate_swap_r.
      apply lt; rewrite (pseudometric_symmetric (d:=dY)); assumption.
    - exact (lt _ _ _ _ cf cg).
  Qed.

  (** ** Uniformly continuous maps between closed intervals *)

  (** A map [f : [a, b] -> F] lifts to locators if it comes with a way to compute a locator for [f x] from a locator for [x]. *)
  Definition IntervalLiftsToLocators {a b : F} (f : ClosedInterval a b -> F)
    := forall x : ClosedInterval a b, locator Q F x.1 -> locator Q F (f x).

  (** A map [g : [a, b] * [c, d] -> F] lifts to locators if it comes with a way to compute a locator for [g (x, y)] from locators for [x] and [y]. *)
  Definition ProductLiftsToLocators {a b c d : F}
    (g : ClosedInterval a b * ClosedInterval c d -> F)
    := forall x y, locator Q F x.1 -> locator Q F y.1 -> locator Q F (g (x, y)).

  Section uniform_maps.
    Context (a b c d : F).

    (** The maps from [[a, b]] to [[c, d]] with a modulus of uniform continuity. *)
    Record UniformMap := {
      umap :> ClosedInterval a b -> ClosedInterval c d;
      umap_modulus : Qpos Q -> Qpos Q;
      isuniformmodulus_umap : IsUniformModulus Q closeI closeI umap umap_modulus
    }.

    (** The uniformly continuous maps which additionally lift to locators. *)
    Record UniformLocatorMap := {
      ulmap :> UniformMap;
      ulmap_lifts : IntervalLiftsToLocators (fun x => (ulmap x).1)
    }.

    Definition isuniformlycontinuous_pointwise_dist (f g : UniformMap)
      : IsUniformlyContinuous Q closeI closeF (fun x => interval_dist (f x) (g x))
      := tr (_; isuniformmodulus_pointwise_dist _ _ f g _ _
                   (isuniformmodulus_umap f) (isuniformmodulus_umap g)).

    Context (leab : a ≤ b) `{Funext} `{!IsComplete Q F}.

    (** The distance between two maps is the supremum of their pointwise distance. *)
    Definition uniform_dist (f g : UniformMap) : F
      := supremum leab (fun x => interval_dist (f x) (g x))
           (isuniformlycontinuous_pointwise_dist f g).

    Definition le_uniform_dist (f g : UniformMap) (x : ClosedInterval a b)
      : interval_dist (f x) (g x) ≤ uniform_dist f g
      := fst (issupremum_supremum leab _ _) x.

    Definition uniform_dist_le (f g : UniformMap) (u : F)
      (le : forall x, interval_dist (f x) (g x) ≤ u)
      : uniform_dist f g ≤ u
      := snd (issupremum_supremum leab _ _) u le.

    #[export] Instance ispseudometric_uniform_dist : IsPseudoMetric uniform_dist.
    Proof.
      snapply Build_IsPseudoMetric.
      - intros f g.
        exact (transitivity (pseudometric_nonneg (d:=interval_dist) _ _) (le_uniform_dist f g (interval_left leab))).
      - intro f; apply (antisymmetry (≤)).
        + apply uniform_dist_le; intro x; apply eq_le, (pseudometric_diag (d:=interval_dist)).
        + exact (transitivity (pseudometric_nonneg (d:=interval_dist) _ _) (le_uniform_dist f f (interval_left leab))).
      - intros f g; apply (antisymmetry (≤)); apply uniform_dist_le; intro x;
          rewrite (pseudometric_symmetric (d:=interval_dist)); apply le_uniform_dist.
      - intros f g h; apply uniform_dist_le; intro x.
        lhs' exact (pseudometric_triangle (d:=interval_dist) _ (g x) _).
        apply plus_le_compat; apply le_uniform_dist.
    Defined.

    (** Maps at distance zero have equal underlying maps. *)
    Lemma path_uniform_dist_zero (f g : UniformMap) (p : uniform_dist f g = 0)
      : (f : ClosedInterval a b -> ClosedInterval c d) = g.
    Proof.
      apply path_forall; intro x; apply path_sigma_hprop.
      apply equal_by_zero_sum, abs_eq_0, (antisymmetry (≤)).
      - rewrite <- p; apply le_uniform_dist.
      - apply abs_nonneg.
    Qed.

    (** The distance between maps which lift to locators is the distance of the underlying maps. *)
    Definition ulmap_dist (f g : UniformLocatorMap) : F := uniform_dist f g.

    #[export] Instance ispseudometric_ulmap_dist : IsPseudoMetric ulmap_dist
      := ispseudometric_pullback ulmap uniform_dist.

    (** ** Completeness *)

    Section completeness.
      Context (fs : nat -> UniformLocatorMap) (M : Qpos Q -> nat)
        (Mmod : MetricCauchyModulus Q (metric_close Q ulmap_dist) fs M).

      (** At each point, the values form a sequence with modulus [M]. *)
      Local Lemma cauchymodulus_values (x : ClosedInterval a b)
        : CauchyModulus Q F (fun n => (fs n x).1) M.
      Proof.
        intros e m n lem len; apply (field_close_iff_abs Q).
        exact (le_lt_trans _ _ _ (le_uniform_dist _ _ x) (Mmod e m n lem len)).
      Qed.

      Local Definition limit_value (x : ClosedInterval a b)
        : {l : F & IsLimit Q F (fun n => (fs n x).1) l}
        := is_complete Q F _ M (cauchymodulus_values x).

      (** From [M e] on, the values are within [e] of the limit. *)
      Local Lemma limit_value_close (x : ClosedInterval a b) (e : Qpos Q) (n : nat)
        (len : (M e <= n)%nat)
        : abs ((limit_value x).1 - (fs n x).1) ≤ ' (' e).
      Proof.
        set (l := limit_value x).
        assert (close : forall k, (M e <= k)%nat
                        -> - ' (' e) < (fs k x).1 - (fs n x).1 < ' (' e)).
        { intros k lek; exact (cauchymodulus_values x e k n lek len). }
        assert (lo : (fs n x).1 - ' (' e) ≤ l.1).
        { apply (le_limit Q F _ l.1 _ (M e) l.2); intros k lek; apply lt_le.
          rewrite plus_comm; exact (fst (flip_lt_minus_r _ _ _) (fst (close k lek))). }
        assert (hi : l.1 ≤ (fs n x).1 + ' (' e)).
        { apply (limit_le Q F _ l.1 _ (M e) l.2); intros k lek; apply lt_le.
          rewrite plus_comm; exact (fst (flip_lt_minus_l _ _ _) (snd (close k lek))). }
        apply abs_le.
        - apply (snd (flip_le_minus_r _ _ _)); rewrite plus_comm; exact lo.
        - apply (snd (flip_le_minus_l _ _ _)); rewrite plus_comm; exact hi.
      Qed.

      (** The pointwise limit, which lies in [[c, d]]. *)
      Definition limit_map (x : ClosedInterval a b) : ClosedInterval c d.
      Proof.
        exists (limit_value x).1; split.
        - exact (le_limit Q F _ _ c 0 (limit_value x).2 (fun k _ => fst (fs k x).2)).
        - exact (limit_le Q F _ _ d 0 (limit_value x).2 (fun k _ => snd (fs k x).2)).
      Defined.

      Local Lemma qinc_split3 (e : Qpos Q)
        : ' (' e) = ' (' (e / 3)) + ' (' (e / 3)) + ' (' (e / 3)) :> F.
      Proof.
        rewrite <- 2 (preserves_plus (f:=cast Q F)).
        exact (ap (fun d : Qpos Q => ' (' d)) (pos_split3 e)).
      Qed.

      (** The limit is uniformly continuous: a modulus of [fs (M (e / 3))] for [e / 3] is a modulus for [e]. *)
      Lemma isuniformmodulus_limit_map
        : IsUniformModulus Q closeI closeI limit_map
            (fun e => umap_modulus (fs (M (e / 3))) (e / 3)).
      Proof.
        intros e x y cxy; set (N := M (e / 3)).
        unfold metric_close, interval_dist.
        change (abs ((limit_value x).1 - (limit_value y).1) < ' (' e)).
        refine (le_lt_trans _ _ _ (pseudometric_triangle (d:=dF) _ (fs N x).1 _) _).
        refine (le_lt_trans _ _ _ (plus_le_compat _ _ _ _ (reflexivity _)
                  (pseudometric_triangle (d:=dF) _ (fs N y).1 _)) _).
        cbn beta; rewrite (qinc_split3 e), <- (plus_assoc (' (' (e / 3)))).
        apply plus_le_lt_compat; [exact (limit_value_close x _ N (leq_refl _))|].
        apply plus_lt_le_compat.
        - exact (isuniformmodulus_umap (fs N) (e / 3) x y cxy).
        - rewrite abs_minus_swap; exact (limit_value_close y _ N (leq_refl _)).
      Qed.

      (** The limit lifts to locators, since each of the values does. *)
      Definition ulmap_limit : UniformLocatorMap
        := {| ulmap := {| umap := limit_map; isuniformmodulus_umap := isuniformmodulus_limit_map |};
              ulmap_lifts := fun x lx => locator_limit Q F (M_ismod := cauchymodulus_values x)
                                (fun n => ulmap_lifts (fs n) x lx) (limit_value x).2 |}.

      Lemma ismetriclimit_ulmap_limit : IsMetricLimit Q (metric_close Q ulmap_dist) fs ulmap_limit.
      Proof.
        intro e; apply tr; exists (M (e / 2)); intros n len.
        unfold metric_close, ulmap_dist.
        refine (le_lt_trans _ _ _ (uniform_dist_le _ _ (' (' (e / 2))) _) _);
          [|exact (strictly_order_preserving (cast Q F) _ _ (qpos_half_lt e))].
        intro x; unfold interval_dist.
        change (abs ((fs n x).1 - (limit_value x).1) ≤ ' (' (e / 2))).
        rewrite abs_minus_swap; exact (limit_value_close x _ n len).
      Qed.

    End completeness.

    (** The space of uniformly continuous maps which lift to locators is Cauchy complete. *)
    #[export] Instance metriccauchycomplete_ulmap_dist
      : MetricCauchyComplete Q (metric_close Q ulmap_dist)
      := {| metric_limit := ulmap_limit; ismetriclimit_metric_limit := ismetriclimit_ulmap_limit |}.

  End uniform_maps.

End function_space.
