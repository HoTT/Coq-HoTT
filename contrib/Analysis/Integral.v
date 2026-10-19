(** * Integration *)

(** We do not construct an integral. Instead, an integration operator is an operation assigning to each uniformly continuous function [f] on a closed interval, and points [x] and [y] of the interval, an oriented integral of [f] from [x] to [y], such that integrals are additive over intervals and in the integrand, constants integrate to their value times the length, and integration is monotone. The Riemann integral is such an operator, and we show that these properties determine the operator: any two agree. From them we derive that integrals are limits of Riemann sums with an explicit modulus of Cauchy convergence, so that the integral of a function that lifts to locators, between endpoints with locators, has a locator. *)

From HoTT Require Import Basics Types.Sigma Types.Forall Truncations.Core.
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
  MetricSpace CauchyCompleteness LiftsToLocators IntermediateValue FunctionSpace.

Section integration.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}.
  Context (F : Type) `{Forderedfield : OrderedField F} {Fabs : Abs F}.

  Local Existing Instance qinc.
  Local Instance orderpreserving_qinc : OrderPreserving (qinc Q F)
    := full_pseudo_order_preserving.

  Local Notation dF := (fun u v : F => abs (u - v)).
  Local Notation closeI := (metric_close Q (interval_dist F)).
  Local Notation closeF := (metric_close Q dF).
  Local Notation I := (ClosedInterval F).

  (** ** Uniformly continuous functions on closed intervals *)

  Section uniform.
    Context {X : Type} (dX : X -> X -> F).

    Definition isuniformlycontinuous_const (k : F)
      : IsUniformlyContinuous Q (metric_close Q dX) closeF (fun _ => k).
    Proof.
      apply tr; exists idmap; intros e x y _; unfold metric_close.
      rewrite plus_negate_r, abs_0; exact (pos_rationals_to_field_qpos Q e).
    Defined.

    Lemma isuniformmodulus_plus (f g : X -> F) (wf wg : Qpos Q -> Qpos Q)
      (fw : IsUniformModulus Q (metric_close Q dX) closeF f wf)
      (gw : IsUniformModulus Q (metric_close Q dX) closeF g wg)
      : IsUniformModulus Q (metric_close Q dX) closeF (fun x => f x + g x)
          (fun e => qpos_min Q (wf (e / 2)) (wg (e / 2))).
    Proof.
      intros e x y c; unfold metric_close in *.
      assert (p : f x + g x - (f y + g y) = (f x - f y) + (g x - g y)).
      { rewrite negate_plus_distr, <- 2 plus_assoc; apply ap.
        rewrite 2 plus_assoc; apply (ap (+ _)), plus_comm. }
      rewrite p; refine (le_lt_trans _ _ _ (abs_triangle _ _) _).
      rewrite (pos_split2 e), (preserves_plus (f:=cast Q F)).
      apply plus_lt_compat.
      - apply fw; refine (lt_le_trans _ _ _ c _).
        apply (order_preserving (cast Q F)), qpos_min_le_l.
      - apply gw; refine (lt_le_trans _ _ _ c _).
        apply (order_preserving (cast Q F)), qpos_min_le_r.
    Qed.

    Definition isuniformlycontinuous_plus (f g : X -> F)
      (fu : IsUniformlyContinuous Q (metric_close Q dX) closeF f)
      (gu : IsUniformlyContinuous Q (metric_close Q dX) closeF g)
      : IsUniformlyContinuous Q (metric_close Q dX) closeF (fun x => f x + g x).
    Proof.
      strip_truncations; destruct fu as [wf fw], gu as [wg gw].
      exact (tr (_; isuniformmodulus_plus f g wf wg fw gw)).
    Defined.

    Definition isuniformlycontinuous_negate (f : X -> F)
      (fu : IsUniformlyContinuous Q (metric_close Q dX) closeF f)
      : IsUniformlyContinuous Q (metric_close Q dX) closeF (fun x => - f x).
    Proof.
      refine (Trunc_functor (-1) _ fu); intros [w fw]; exists w.
      intros e x y c; unfold metric_close.
      rewrite <- negate_plus_distr, abs_negate; exact (fw e x y c).
    Defined.

  End uniform.

  (** ** Integration operators *)

  (** An integration operator assigns to every function [f] on a closed interval which is uniformly continuous, and any two points [x] and [y] of the interval, the oriented integral of [f] from [x] to [y]. It is additive over intervals and in the integrand, integrates constants and is monotone. The Riemann integral is such an operator, and these properties determine it: see [integral_unique]. *)
  Class Integration := {
    integral : forall {a b : F} (f : I a b -> F),
      IsUniformlyContinuous Q closeI closeF f -> I a b -> I a b -> F;
    integral_additive : forall {a b : F} (f : I a b -> F) fu (x y z : I a b),
      integral f fu x y + integral f fu y z = integral f fu x z;
    integral_const : forall {a b : F} (k : F) (x y : I a b),
      integral (fun _ => k) (isuniformlycontinuous_const _ k) x y = k * (y.1 - x.1);
    integral_plus : forall {a b : F} (f g : I a b -> F) fu gu (x y : I a b),
      integral (fun t => f t + g t) (isuniformlycontinuous_plus _ f g fu gu) x y
      = integral f fu x y + integral g gu x y;
    integral_le : forall {a b : F} (f g : I a b -> F) fu gu (x y : I a b),
      x.1 ≤ y.1 -> (forall t : I a b, x.1 ≤ t.1 -> t.1 ≤ y.1 -> f t ≤ g t)
      -> integral f fu x y ≤ integral g gu x y
  }.

  Section properties.
    Context `{Integration} {a b : F}.

    Lemma integral_diag (f : I a b -> F) fu (x : I a b) : integral f fu x x = 0.
    Proof.
      apply (left_cancellation (+) (integral f fu x x)).
      rewrite integral_additive, plus_0_r; reflexivity.
    Qed.

    Lemma integral_swap (f : I a b -> F) fu (x y : I a b)
      : integral f fu y x = - integral f fu x y.
    Proof.
      apply (left_cancellation (+) (integral f fu x y)).
      rewrite integral_additive, integral_diag, plus_negate_r; reflexivity.
    Qed.

    (** The minimum of two points of an interval. *)
    Definition interval_min (x y : I a b) : I a b
      := (meet x.1 y.1; (meet_le _ _ _ (fst x.2) (fst y.2),
                         transitivity (meet_lb_l _ _) (snd x.2))).

    (** An integral is a difference of integrals from the minimum of its endpoints, where the endpoints are in order. *)
    Lemma integral_interval_min (f : I a b -> F) fu (x y : I a b)
      : integral f fu (interval_min x y) y - integral f fu (interval_min x y) x
        = integral f fu x y.
    Proof.
      rewrite <- (integral_additive f fu (interval_min x y) x y).
      rewrite (plus_comm (integral f fu _ x)), <- plus_assoc, plus_negate_r.
      apply plus_0_r.
    Qed.

    Context `{Funext}.

    (** The integral only depends on the values of the function. *)
    Lemma integral_homotopic (f g : I a b -> F) fu gu (p : f == g) (x y : I a b)
      : integral f fu x y = integral g gu x y.
    Proof.
      destruct (path_forall _ _ p).
      exact (ap (fun fu' => integral f fu' x y) (path_ishprop fu gu)).
    Qed.

    Lemma integral_negate (f : I a b -> F) fu fu' (x y : I a b)
      : integral (fun t => - f t) fu' x y = - integral f fu x y.
    Proof.
      apply (left_cancellation (+) (integral f fu x y)).
      rewrite <- integral_plus, plus_negate_r.
      refine (integral_homotopic _ (fun _ => 0) _ (isuniformlycontinuous_const _ 0) _ x y
                @ integral_const _ _ _ @ mult_0_l _).
      intro t; apply plus_negate_r.
    Qed.

    Lemma integral_minus (f g : I a b -> F) fu gu fgu (x y : I a b)
      : integral (fun t => f t - g t) fgu x y = integral f fu x y - integral g gu x y.
    Proof.
      rewrite (path_ishprop fgu
                 (isuniformlycontinuous_plus _ f _ fu (isuniformlycontinuous_negate _ g gu))).
      rewrite integral_plus; apply ap, integral_negate.
    Qed.

    (** A bound on the integrand bounds the integral over an interval [[x, y]]. *)
    Lemma integral_abs_le_bound (f : I a b -> F) fu (x y : I a b) (lexy : x.1 ≤ y.1) (K : F)
      (fK : forall t : I a b, x.1 ≤ t.1 -> t.1 ≤ y.1 -> abs (f t) ≤ K)
      : abs (integral f fu x y) ≤ K * (y.1 - x.1).
    Proof.
      apply abs_le.
      - rewrite negate_mult_distr_l, <- (integral_const (- K)).
        apply integral_le; [exact lexy|]; intros t xt ty.
        apply flip_le_negate; rewrite negate_involutive.
        exact (transitivity (negate_le_abs _) (fK t xt ty)).
      - rewrite <- (integral_const K).
        apply integral_le; [exact lexy|]; intros t xt ty.
        exact (transitivity (le_abs _) (fK t xt ty)).
    Qed.

    (** For a bound on the whole interval, the endpoints may be in either order. Since the inequality is stable under double negation, we may decide their order. *)
    Lemma integral_abs_le (f : I a b -> F) fu (x y : I a b) (K : F)
      (fK : forall t : I a b, abs (f t) ≤ K)
      : abs (integral f fu x y) ≤ K * abs (y.1 - x.1).
    Proof.
      apply not_lt_le_flip; intro lt.
      assert (nn : ~~ ((y.1 < x.1) + ~ (y.1 < x.1))).
      { intro n; apply n, inr; intro l; exact (n (inl l)). }
      apply nn; intros [ltyx|nltyx]; refine (le_not_lt_flip _ _ _ lt).
      - rewrite integral_swap, abs_negate, abs_minus_swap.
        rewrite (abs_of_nonneg _ (snd (flip_nonneg_minus _ _) (lt_le _ _ ltyx))).
        exact (integral_abs_le_bound f fu y x (lt_le _ _ ltyx) K (fun t _ _ => fK t)).
      - assert (lexy := not_lt_le_flip _ _ nltyx).
        rewrite (abs_of_nonneg _ (snd (flip_nonneg_minus _ _) lexy)).
        exact (integral_abs_le_bound f fu x y lexy K (fun t _ _ => fK t)).
    Qed.

    (** ** Riemann sums *)

    (** The sum of [g 0], ..., [g (n - 1)]. *)
    Fixpoint sum_upto (g : nat -> F) (n : nat) : F
      := match n with
         | O => 0
         | S n => sum_upto g n + g n
         end.

    Section partition.
      Context (f : I a b -> F) (fu : IsUniformlyContinuous Q closeI closeF f)
        (w : Qpos Q -> Qpos Q) (fw : IsUniformModulus Q closeI closeF f w) (e : Qpos Q)
        (q : nat -> I a b) (h : F) (h0 : 0 ≤ h) (hw : h < ' (' (w e))) (N : nat)
        (step : forall k, (k < N)%nat -> (q (S k)).1 = (q k).1 + h).

      Local Lemma sum_upto_const_step (c : F) (n : nat) (len : (n <= N)%nat)
        : sum_upto (fun _ => c * h) n = c * ((q n).1 - (q 0%nat).1).
      Proof.
        induction n as [|n IH]; cbn.
        - rewrite plus_negate_r, mult_0_r; reflexivity.
        - rewrite (IH (leq_succ_l len)), (step n len), <- plus_mult_distr_l.
          apply ap.
          rewrite <- plus_assoc, (plus_comm (- _) h), plus_assoc; reflexivity.
      Qed.

      (** On each piece of the partition, the integral is within [e h] of [h f (q k)]. *)
      Local Lemma integral_piece_bounds (k : nat) (ltk : (k < N)%nat)
        : ((f (q k) - ' (' e)) * h ≤ integral f fu (q k) (q (S k)))
          * (integral f fu (q k) (q (S k)) ≤ (f (q k) + ' (' e)) * h).
      Proof.
        assert (p : forall c, c * h = integral (fun _ => c) (isuniformlycontinuous_const _ c)
                                         (q k) (q (S k))).
        { intro c; rewrite integral_const, (step k ltk); apply ap.
          rewrite (plus_comm (q k).1 h), <- plus_assoc, plus_negate_r, plus_0_r.
          reflexivity. }
        assert (le : (q k).1 ≤ (q (S k)).1).
        { rewrite (step k ltk); apply nonneg_plus_le_compat_r.
          exact h0. }
        assert (close : forall t : I a b, (q k).1 ≤ t.1 -> t.1 ≤ (q (S k)).1
                        -> abs (f t - f (q k)) < ' (' e)).
        { intros t kt tk; apply fw; unfold metric_close, interval_dist.
          rewrite (abs_of_nonneg _ (snd (flip_nonneg_minus _ _) kt)).
          refine (le_lt_trans _ _ _ _ hw).
          apply flip_le_minus_l; rewrite plus_comm, <- (step k ltk); exact tk. }
        rewrite 2 p; split; apply integral_le; try exact le; intros t kt tk.
        - assert (c := close t kt tk); rewrite abs_minus_swap in c.
          apply lt_le, (snd (flip_lt_minus_l _ _ _)); rewrite plus_comm.
          exact (fst (flip_lt_minus_l _ _ _) (le_lt_trans _ _ _ (le_abs _) c)).
        - apply lt_le; rewrite plus_comm.
          exact (fst (flip_lt_minus_l _ _ _) (le_lt_trans _ _ _ (le_abs _) (close t kt tk))).
      Qed.

      Local Lemma sum_upto_plus_const (c : F) (n : nat)
        : sum_upto (fun k => (f (q k) + c) * h) n
          = sum_upto (fun k => h * f (q k)) n + sum_upto (fun _ => c * h) n.
      Proof.
        induction n as [|n IH]; cbn.
        - symmetry; apply plus_0_l.
        - rewrite IH, plus_mult_distr_r, (mult_comm (f (q n)) h).
          rewrite <- 2 plus_assoc; apply ap.
          rewrite 2 plus_assoc; apply (ap (+ _)), plus_comm.
      Qed.

      Local Lemma integral_partition_bounds (n : nat) (len : (n <= N)%nat)
        : (sum_upto (fun k => (f (q k) - ' (' e)) * h) n ≤ integral f fu (q 0%nat) (q n))
          * (integral f fu (q 0%nat) (q n) ≤ sum_upto (fun k => (f (q k) + ' (' e)) * h) n).
      Proof.
        induction n as [|n IH]; cbn.
        - rewrite integral_diag; split; reflexivity.
        - destruct (IH (leq_succ_l len)) as [lo hi].
          destruct (integral_piece_bounds n len) as [lo' hi'].
          rewrite <- (integral_additive f fu _ (q n)).
          split; apply plus_le_compat; assumption.
      Qed.

      (** The integral over a partition with steps [h] less than [w e] is within [e] times the length of the Riemann sum. *)
      Lemma integral_partition
        : abs (integral f fu (q 0%nat) (q N) - sum_upto (fun k => h * f (q k)) N)
          ≤ ' (' e) * ((q N).1 - (q 0%nat).1).
      Proof.
        destruct (integral_partition_bounds N (leq_refl N)) as [lo hi].
        rewrite sum_upto_plus_const, sum_upto_const_step in lo, hi; try exact (leq_refl N).
        rewrite <- negate_mult_distr_l in lo.
        apply abs_le.
        - apply (snd (flip_le_minus_r _ _ _)); rewrite plus_comm; exact lo.
        - apply (snd (flip_le_minus_l _ _ _)); rewrite plus_comm; exact hi.
      Qed.

    End partition.

    (** The Riemann sum of [f] for [n + 1] equal steps from [x] to [y], evaluating at the left end of each step. *)
    Definition riemann_sum (f : I a b -> F) (x y : I a b) (n : nat) : F
      := sum_upto (fun k => grid_step Q F x y n * f (grid_point Q F x y n k)) (S n).

    Section riemann.
      Context (f : I a b -> F) (fu : IsUniformlyContinuous Q closeI closeF f)
        (w : Qpos Q -> Qpos Q) (fw : IsUniformModulus Q closeI closeF f w)
        (x y : I a b) (lexy : x.1 ≤ y.1).

      (** If the steps are less than [w e], then the integral is within [e (y - x)] of the Riemann sum. *)
      Lemma integral_riemann_sum (e : Qpos Q) (n : nat)
        (lt : grid_step Q F x y n < ' (' (w e)))
        : abs (integral f fu x y - riemann_sum f x y n) ≤ ' (' e) * (y.1 - x.1).
      Proof.
        pose proof (integral_partition f fu w fw e (grid_point Q F x y n)
                      (grid_step Q F x y n) (grid_step_nonneg Q F x y n lexy) lt (S n)
                      (fun k ltk => grid_point_succ Q F x y n k (leq_pred' ltk))) as c.
        rewrite grid_point_0, grid_point_last in c; exact c.
      Qed.

      Context {Qroundup : RoundUpStrict Q} (B : Qpos Q) (ltB : y.1 - x.1 < ' (' B)).

      (** The modulus of Cauchy convergence of the Riemann sums: from [riemann_modulus e] on, the integral is within [e / 2] of the Riemann sums. *)
      Definition riemann_modulus (e : Qpos Q) : nat := grid_modulus Q (' B) w (e / 2 / B).

      Local Lemma integral_riemann_sum_lt (e : Qpos Q) (n : nat)
        (len : (riemann_modulus e <= n)%nat)
        : abs (integral f fu x y - riemann_sum f x y n) < ' (' (e / 2)).
      Proof.
        refine (le_lt_trans _ _ _ (integral_riemann_sum (e / 2 / B) n
                  (lt_grid_modulus Q F _ (' B) (lt_le _ _ ltB) w _ n len)) _).
        assert (p : ' (' (e / 2)) = ' (' (e / 2 / B)) * (' (' B) : F)).
        { rewrite <- (preserves_mult (f:=cast Q F)); apply ap.
          change (' (e / 2) = ' (e / 2) * ' (/ B) * ' B).
          rewrite <- mult_assoc, (mult_comm (' (/ B))).
          change (' B * ' (/ B)) with (' (B / B)); rewrite pos_recip_r.
          symmetry; apply mult_1_r. }
        rewrite p.
        assert (PropHolds (0 < (' (' (e / 2 / B)) : F)))
          by exact (pos_rationals_to_field_qpos Q _).
        exact (strictly_order_preserving _ _ _ ltB).
      Qed.

      Lemma cauchymodulus_riemann_sum
        : CauchyModulus Q F (riemann_sum f x y) riemann_modulus.
      Proof.
        intros e m n lem len; apply (field_close_iff_abs Q).
        refine (le_lt_trans _ _ _ (pseudometric_triangle (d:=dF) _ (integral f fu x y) _) _).
        cbn beta; rewrite (abs_minus_swap _ (integral f fu x y)).
        rewrite (pos_split2 e), (preserves_plus (f:=cast Q F)).
        exact (plus_lt_compat _ _ _ _ (integral_riemann_sum_lt e m lem)
                 (integral_riemann_sum_lt e n len)).
      Qed.

      (** The integral is the limit of the Riemann sums. *)
      Lemma islimit_riemann_sum : IsLimit Q F (riemann_sum f x y) (integral f fu x y).
      Proof.
        intro e; apply tr; exists (riemann_modulus e); intros n len.
        apply (field_close_iff_abs Q).
        exact (transitivity (integral_riemann_sum_lt e n len)
                 (strictly_order_preserving (cast Q F) _ _ (qpos_half_lt e))).
      Qed.

    End riemann.

  End properties.

  (** ** Locators for integrals *)

  Section locators.
    Context `{Integration} `{Funext} {Qtrich : Trichotomy (<)}
      {Farch : ArchimedeanProperty Q F} {Qroundup : RoundUpStrict Q} {a b : F}.

    Local Definition locator_sum_upto (g : nat -> F) (lg : forall k, locator Q F (g k))
      : forall n, locator Q F (sum_upto g n).
    Proof.
      intro n; induction n as [|n IH].
      - exact (locator_0 Q F).
      - exact (locator_plus Q F IH (lg n)).
    Defined.

    Section points.
      Context (x y : I a b) (lx : locator Q F x.1) (ly : locator Q F y.1).

      Local Definition locator_diff : locator Q F (y.1 - x.1)
        := locator_plus Q F ly (locator_minus Q F lx).

      Local Definition locator_grid_step (n : nat) : locator Q F (grid_step Q F x y n)
        := locator_times Q F (locator_left Q F _) locator_diff.

      Local Definition locator_grid_point (n k : nat) : locator Q F (grid_point Q F x y n k).1
        := locator_plus Q F lx (locator_times Q F (locator_left Q F _) locator_diff).

      (** If [f] lifts to locators, then its Riemann sums have locators. *)
      Definition locator_riemann_sum (f : I a b -> F) (lf : IntervalLiftsToLocators Q F f)
        (n : nat)
        : locator Q F (riemann_sum f x y n)
        := locator_sum_upto _ (fun k => locator_times Q F (locator_grid_step n)
                                          (lf _ (locator_grid_point n k))) (S n).

      (** For [x ≤ y] with locators, the integral of a function with a modulus of uniform continuity that lifts to locators has a locator, as the limit of the Riemann sums. *)
      Definition locator_integral_le (f : I a b -> F) fu (w : Qpos Q -> Qpos Q)
        (fw : IsUniformModulus Q closeI closeF f w) (lf : IntervalLiftsToLocators Q F f)
        (lexy : x.1 ≤ y.1)
        : locator Q F (integral f fu x y).
      Proof.
        destruct (qpos_upper_bound Q F locator_diff) as [r ltr].
        exact (locator_limit Q F
                 (M_ismod := cauchymodulus_riemann_sum f fu w fw x y lexy r ltr)
                 (locator_riemann_sum f lf) (islimit_riemann_sum f fu w fw x y lexy r ltr)).
      Defined.
    End points.

    (** The same holds for endpoints in either order: the integral from [x] to [y] is the difference of the integrals from [min x y]. *)
    Definition locator_integral (f : I a b -> F) fu (w : Qpos Q -> Qpos Q)
      (fw : IsUniformModulus Q closeI closeF f w) (lf : IntervalLiftsToLocators Q F f)
      (x y : I a b) (lx : locator Q F x.1) (ly : locator Q F y.1)
      : locator Q F (integral f fu x y).
    Proof.
      refine (transport (locator Q F) (integral_interval_min f fu x y)
                (locator_plus Q F
                   (locator_integral_le (interval_min x y) y (locator_meet Q F lx ly) ly f fu w fw lf _)
                   (locator_minus Q F
                      (locator_integral_le (interval_min x y) x (locator_meet Q F lx ly) lx f fu w fw lf _)))).
      - rapply meet_lb_r.
      - rapply meet_lb_l.
    Defined.

    (** The integral over [[a, b]] of a function [F -> F] with a modulus of uniform continuity on [[a, b]] that lifts to locators has a locator, if [a] and [b] do. *)
    Definition locator_integral_lifts (f : F -> F) (leab : a ≤ b)
      (fw : UniformModulusOn Q F a b f) (lf : LiftsToLocators Q F f)
      (la : locator Q F a) (lb : locator Q F b) fu
      : locator Q F (integral (fun t : I a b => f t.1) fu
                       (interval_left F leab) (interval_right F leab)).
    Proof.
      refine (locator_integral_le (interval_left F leab) (interval_right F leab) la lb _ fu fw.1 _
                (fun t lt => lf t.1 lt) leab).
      intros e s t c; apply (field_close_iff_abs Q), fw.2, (field_close_iff_abs Q), c.
    Defined.

  End locators.

  (** ** Uniqueness *)

  Section uniqueness.
    Context `{Funext} {Farch : ArchimedeanProperty Q F} {Qroundup : RoundUpStrict Q}
      {a b : F}.

    (** An element bounded by every positive rational multiple of a nonnegative [D] is nonpositive. *)
    Local Lemma nonpos_le_qpos_mult (u D : F) (D0 : 0 ≤ D)
      (le : forall e : Qpos Q, u ≤ ' (' e) * D)
      : u ≤ 0.
    Proof.
      apply not_lt_le_flip; intro u0.
      assert (r := merely_qpos_lt Q u u0).
      assert (c := archimedean_property Q F D (D + 1) (fst (pos_plus_lt_compat_r _ _) lt_0_1)).
      strip_truncations; destruct r as [r ltr], c as [B [ltB _]].
      assert (B0 : 0 < B).
      { apply (strictly_order_reflecting (cast Q F)).
        rewrite (preserves_0 (f:=cast Q F)); exact (le_lt_trans _ _ _ D0 ltB). }
      set (e := r / mkQpos B B0).
      apply (irreflexivity (<) u).
      refine (le_lt_trans _ _ _ (le e) (transitivity _ ltr)).
      assert (p : ' (' e) * ' B = (' (' r) : F)).
      { rewrite <- (preserves_mult (f:=cast Q F)); apply ap.
        change (' r * / B * B = ' r).
        rewrite <- mult_assoc, (mult_comm (/ B)).
        rewrite (dec_recip_inverse B (lt_ne_flip _ _ B0)); apply mult_1_r. }
      rewrite <- p.
      assert (PropHolds (0 < (' (' e) : F))) by exact (pos_rationals_to_field_qpos Q e).
      exact (strictly_order_preserving _ _ _ ltB).
    Qed.

    Context (I1 I2 : Integration).

    Local Lemma integral_unique_le (f : I a b -> F) fu (x y : I a b) (lexy : x.1 ≤ y.1)
      : integral (Integration:=I1) f fu x y = integral (Integration:=I2) f fu x y.
    Proof.
      apply equal_by_zero_sum, abs_eq_0, (antisymmetry (≤)); [|apply abs_nonneg].
      apply (nonpos_le_qpos_mult _ _ (snd (flip_nonneg_minus _ _) lexy)); intro e.
      (* We keep [fu], which the goal mentions, and use a modulus and a bound from copies. *)
      assert (c := fu); revert c; apply Trunc_rec; intros [w fw].
      generalize (archimedean_property Q F (y.1 - x.1) (y.1 - x.1 + 1)
                    (fst (pos_plus_lt_compat_r _ _) lt_0_1)).
      apply Trunc_rec; intros [B [ltB _]].
      set (n := grid_modulus Q B w (e / 2)).
      assert (lt := lt_grid_modulus Q F _ B (lt_le _ _ ltB) w (e / 2) n (leq_refl _)).
      lhs' exact (pseudometric_triangle (d:=dF) _ (riemann_sum f x y n) _).
      cbn beta; rewrite (abs_minus_swap (riemann_sum f x y n)).
      rewrite (pos_split2 e), (preserves_plus (f:=cast Q F)), plus_mult_distr_r.
      exact (plus_le_compat _ _ _ _ (integral_riemann_sum (H:=I1) f fu w fw x y lexy _ n lt)
               (integral_riemann_sum (H:=I2) f fu w fw x y lexy _ n lt)).
    Qed.

    (** The properties of an integration operator determine it uniquely. *)
    Lemma integral_unique (f : I a b -> F) fu (x y : I a b)
      : integral (Integration:=I1) f fu x y = integral (Integration:=I2) f fu x y.
    Proof.
      rewrite <- (integral_interval_min (H:=I1)), <- (integral_interval_min (H:=I2)).
      rewrite 2 integral_unique_le; try reflexivity.
      - rapply meet_lb_l.
      - rapply meet_lb_r.
    Qed.

  End uniqueness.

End integration.
