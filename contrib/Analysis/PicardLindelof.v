(** * The Picard–Lindelöf theorem *)

(** For [g] on [[x0 - a, x0 + a] * [y0 - b, y0 + b]] with a modulus of uniform continuity, which lifts to locators and is Lipschitz in its second argument, and an integration operator, we compute [l] with a locator and a solution [f] of [f x = y0 + ∫_{x0}^x g (t, f t) dt] on [[x0 - l, x0 + l]], which is uniformly continuous and lifts to locators. As usual, [f] is the fixed point of the Picard iteration, found by Banach's fixed point theorem in the Cauchy complete space of uniformly continuous maps that lift to locators. *)

From HoTT Require Import Basics Types.Sigma Types.Prod Types.Forall Truncations.Core.
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
  MetricSpace CauchyCompleteness BanachFixedPoint LiftsToLocators FunctionSpace Integral.

Section picard_lindelof.
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
  Local Notation dI := (interval_dist F).
  Local Notation closeF := (metric_close Q dF).
  Local Notation I := (ClosedInterval F).

  (** ** Bounds from moduli of uniform continuity *)

  (** Along a chain of points whose consecutive points are closer than [w 1], a function with modulus [w] changes by at most the number of steps. *)
  Lemma abs_chain_le {X : Type} (dX : X -> X -> F) (h : X -> F) (w : Qpos Q -> Qpos Q)
    (hw : IsUniformModulus Q (metric_close Q dX) closeF h w) (z : nat -> X) (N : nat)
    (close : forall k, (k < N)%nat -> metric_close Q dX (w 1) (z (S k)) (z k))
    : abs (h (z N) - h (z 0%nat)) ≤ ' (nQ N).
  Proof.
    induction N as [|N IH].
    - rewrite plus_negate_r, abs_0, (preserves_0 (f:=nQ)), (preserves_0 (f:=cast Q F)).
      reflexivity.
    - lhs' exact (pseudometric_triangle (d:=dF) _ (h (z N)) _); cbn beta.
      rewrite nat_to_semiring_succ, (preserves_plus (f:=cast Q F)).
      apply plus_le_compat.
      + apply lt_le; exact (hw 1 _ _ (close N (leq_refl _))).
      + exact (IH (fun k ltk => close k (leq_succ_r ltk))).
  Qed.

  (** Two points of [[a, b]] are at most [b - a] apart. *)
  Lemma interval_dist_le {a b : F} (s t : I a b) : dI s t ≤ b - a.
  Proof.
    apply abs_le.
    - rewrite (negate_swap_r s.1 t.1).
      exact (snd (flip_le_negate _ _) (interval_minus_le a b _ _ t.2 s.2)).
    - exact (interval_minus_le a b _ _ s.2 t.2).
  Qed.

  Local Lemma abs_mult_nonneg_le (s u : F) (s0 : 0 ≤ s) : abs (s * u) ≤ s * abs u.
  Proof.
    apply abs_le.
    - rewrite negate_mult_distr_r; apply (order_preserving (s *.)).
      apply flip_le_negate; rewrite negate_involutive; apply negate_le_abs.
    - apply (order_preserving (s *.)), le_abs.
  Qed.

  Section bound.
    Context {a b c d : F} (g : I a b * I c d -> F) (v : Qpos Q -> Qpos Q)
      (gv : IsUniformModulus Q (metric_close Q (prod_dist dI dI)) closeF g v)
      (B : Q) (leB : (b - a) + (d - c) ≤ ' B).

    (** A function with a modulus of uniform continuity on a product of closed intervals is bounded: along the segment from a point [z] to any point [p], we find a chain of a fixed number of steps of length less than [v 1]. *)
    Lemma abs_le_uniform (z p : I a b * I c d)
      : abs (g p) ≤ abs (g z) + ' (nQ (S (grid_modulus Q B v 1))).
    Proof.
      set (N := grid_modulus Q B v 1).
      set (q := fun k => (grid_point Q F (fst z) (fst p) N k, grid_point Q F (snd z) (snd p) N k)).
      assert (q0 : q 0%nat = z).
      { unfold q; rewrite 2 grid_point_0; apply eta_prod. }
      assert (qN : q (S N) = p).
      { unfold q; rewrite 2 grid_point_last; apply eta_prod. }
      assert (close : forall k, (k < S N)%nat -> metric_close Q (prod_dist dI dI) (v 1) (q (S k)) (q k)).
      { intros k ltk.
        change (dI (grid_point Q F (fst z) (fst p) N (S k)) (grid_point Q F (fst z) (fst p) N k)
                + dI (grid_point Q F (snd z) (snd p) N (S k)) (grid_point Q F (snd z) (snd p) N k)
                < ' (' (v 1))).
        unfold interval_dist.
        rewrite 2 (grid_point_succ Q F _ _ N k (leq_pred' ltk)).
        rewrite 2 (plus_comm _ (grid_step Q F _ _ N)), <- 2 plus_assoc, 2 plus_negate_r.
        rewrite 2 plus_0_r.
        assert (s0 : 0 ≤ (' (/ nQ (S N)) : F)).
        { rewrite <- (preserves_0 (f:=cast Q F)); apply (order_preserving _), lt_le.
          apply pos_dec_recip_compat, nat_to_semiring_succ_pos. }
        refine (le_lt_trans _ _ _ (plus_le_compat _ _ _ _ (abs_mult_nonneg_le _ _ s0)
                  (abs_mult_nonneg_le _ _ s0)) _).
        rewrite <- plus_mult_distr_l.
        refine (lt_grid_modulus Q F _ B _ v 1 N (leq_refl _)).
        refine (transitivity (plus_le_compat _ _ _ _ _ _) leB).
        - rewrite abs_minus_swap; exact (interval_dist_le (fst z) (fst p)).
        - rewrite abs_minus_swap; exact (interval_dist_le (snd z) (snd p)). }
      assert (ch := abs_chain_le _ g v gv q (S N) close).
      rewrite q0, qN in ch.
      rhs_V' exact (plus_le_compat _ _ _ _ (reflexivity (abs (g z))) ch).
      rewrite plus_comm.
      rhs_V' exact (abs_triangle _ _).
      apply eq_le; apply ap.
      rewrite <- plus_assoc, plus_negate_l; symmetry; apply plus_0_r.
    Qed.

  End bound.

  (** ** The Picard iteration *)

  Local Lemma center_bounds (u r : F) (r0 : 0 ≤ r) : u - r ≤ u ≤ u + r.
  Proof.
    split.
    - apply flip_le_minus_l, nonneg_plus_le_compat_r, r0.
    - apply nonneg_plus_le_compat_r, r0.
  Qed.

  (** The center of an interval [[u - r, u + r]]. *)
  Definition interval_center (u r : F) (r0 : 0 ≤ r) : I (u - r) (u + r)
    := (u; center_bounds u r r0).

  (** The inclusion of [[u - l, u + l]] in [[u - r, u + r]] for [l ≤ r]. *)
  Definition interval_incl (u l r : F) (lr : l ≤ r) (t : I (u - l) (u + l)) : I (u - r) (u + r).
  Proof.
    exists t.1; split.
    - rhs_V' exact (fst t.2).
      apply (order_preserving (u +)), (snd (flip_le_negate _ _)), lr.
    - lhs' exact (snd t.2).
      apply (order_preserving (u +)), lr.
  Defined.

  Context `{Funext} {Fcomplete : IsComplete Q F} {Qtrich : Trichotomy (<)}
    `{!Integration Q F}.

  Context (x0 y0 a b : F) (a0 : 0 < a) (b0 : 0 < b)
    (g : I (x0 - a) (x0 + a) * I (y0 - b) (y0 + b) -> F) (v : Qpos Q -> Qpos Q)
    (gv : IsUniformModulus Q (metric_close Q (prod_dist dI dI)) closeF g v)
    (lg : ProductLiftsToLocators Q F g)
    (L : F) (L0 : 0 < L) (gL : forall x y y', abs (g (x, y) - g (x, y')) ≤ L * dI y y')
    (ly0 : locator Q F y0) (lx0 : locator Q F x0) (lb : locator Q F b).

  Section iteration.
    (** We iterate on [[x0 - l, x0 + l]], where [K] bounds [g] and [l K ≤ b] and [l L ≤ 1/2]. *)
    Context (K : Qpos Q) (gK : forall p, abs (g p) ≤ ' (' K)) (l : F)
      (l0 : 0 ≤ l) (la : l ≤ a) (lKb : ' (' K) * l ≤ b) (lLc : L * l ≤ ' (/ 2 : Q)).

    Local Notation UL := (UniformLocatorMap Q F (x0 - l) (x0 + l) (y0 - b) (y0 + b)).
    Local Notation incl := (interval_incl x0 l a la).
    Local Notation c := (interval_center x0 l l0).

    Local Definition leab : x0 - l ≤ x0 + l := transitivity (fst c.2) (snd c.2).

    (** The integrand [t ↦ g (t, f t)]. *)
    Definition picard_integrand (f : UL) (t : I (x0 - l) (x0 + l)) : F := g (incl t, f t).

    Local Definition picard_integrand_modulus (f : UL)
      : IsUniformModulus Q (metric_close Q dI) closeF (picard_integrand f) _
      := isuniformmodulus_graph Q dI dI dF f (fun p => g (incl (fst p), snd p))
           (umap_modulus Q F _ _ _ _ f) v (isuniformmodulus_umap Q F _ _ _ _ f)
           (fun e p q close => gv e (incl (fst p), snd p) (incl (fst q), snd q) close).

    Local Definition picard_integrand_uc (f : UL)
      : IsUniformlyContinuous Q (metric_close Q dI) closeF (picard_integrand f)
      := tr (_; picard_integrand_modulus f).

    (** The value [y0 + ∫_{x0}^x g (t, f t) dt]. *)
    Definition picard_value (f : UL) (x : I (x0 - l) (x0 + l)) : F
      := y0 + integral Q F (picard_integrand f) (picard_integrand_uc f) c x.

    Local Lemma abs_center_le (x : I (x0 - l) (x0 + l)) : abs (x.1 - x0) ≤ l.
    Proof.
      apply abs_le.
      - apply flip_le_minus_r; rewrite plus_comm; exact (fst x.2).
      - apply flip_le_minus_l; rewrite plus_comm; exact (snd x.2).
    Qed.

    Local Lemma abs_picard_integral_le (f : UL) (x : I (x0 - l) (x0 + l))
      : abs (picard_value f x - y0) ≤ b.
    Proof.
      unfold picard_value; rewrite (plus_comm y0), <- plus_assoc, plus_negate_r, plus_0_r.
      lhs' exact (integral_abs_le Q F _ _ c x _ (fun t => gK _)).
      rhs_V' exact lKb.
      apply (order_preserving (_ *.)), abs_center_le.
    Qed.

    Local Lemma abs_le_bounds (u w r : F) (le : abs (w - u) ≤ r) : u - r ≤ w ≤ u + r.
    Proof.
      split.
      - assert (h : u - w ≤ r).
        { rewrite negate_swap_r; exact (transitivity (negate_le_abs _) le). }
        apply (fst (flip_le_minus_l _ _ _)) in h; rewrite plus_comm in h.
        exact (snd (flip_le_minus_l _ _ _) h).
      - rewrite plus_comm; apply flip_le_minus_l.
        exact (transitivity (le_abs _) le).
    Qed.

    Definition picard_point (f : UL) (x : I (x0 - l) (x0 + l)) : I (y0 - b) (y0 + b)
      := (picard_value f x; abs_le_bounds _ _ _ (abs_picard_integral_le f x)).

    (** The new map is Lipschitz with constant [K]. *)
    Local Lemma islipschitz_picard_point (f : UL)
      : IsLipschitz dI dI (picard_point f) (' (' K)).
    Proof.
      intros x x'.
      change (abs (picard_value f x - picard_value f x') ≤ ' (' K) * abs (x.1 - x'.1)).
      assert (p : picard_value f x - picard_value f x'
                  = integral Q F (picard_integrand f) (picard_integrand_uc f) x' x).
      { unfold picard_value; rewrite <- (integral_additive Q F _ _ c x' x).
        rewrite (plus_assoc y0), (plus_comm (y0 + _)), <- plus_assoc, plus_negate_r.
        apply plus_0_r. }
      rewrite p; exact (integral_abs_le Q F _ _ x' x _ (fun t => gK _)).
    Qed.

    Local Definition isuniformmodulus_picard_point (f : UL)
      : IsUniformModulus Q (metric_close Q dI) (metric_close Q dI) (picard_point f)
          (fun e => e / K)
      := isuniformmodulus_lipschitz Q dI dI (picard_point f) K (islipschitz_picard_point f).

    (** The Picard iteration: [T f x = y0 + ∫_{x0}^x g (t, f t) dt]. *)
    Definition picard_map (f : UL) : UL
      := {| ulmap := {| umap := picard_point f;
                        isuniformmodulus_umap := isuniformmodulus_picard_point f |};
            ulmap_lifts := fun x lx => locator_plus Q F ly0
                             (locator_integral Q F (picard_integrand f) _ _
                                (picard_integrand_modulus f)
                                (fun t lt => lg (incl t) (f t) lt (ulmap_lifts Q F _ _ _ _ f t lt))
                                c x lx0 lx) |}.

    Local Notation dUL := (ulmap_dist Q F (x0 - l) (x0 + l) (y0 - b) (y0 + b) leab).

    Local Lemma ulmap_dist_nonneg (f f' : UL) : 0 ≤ dUL f f'.
    Proof.
      exact (transitivity (abs_nonneg _) (le_uniform_dist Q F _ _ _ _ leab f f' c)).
    Qed.

    (** The Picard iteration has Lipschitz constant [1/2]. *)
    Lemma islipschitz_picard_map : IsLipschitz dUL dUL picard_map (' (/ 2 : Q)).
    Proof.
      intros f f'.
      assert (D0 := ulmap_dist_nonneg f f').
      apply (uniform_dist_le Q F _ _ _ _ leab); intro x.
      change (abs (picard_value f x - picard_value f' x) ≤ ' (/ 2 : Q) * dUL f f').
      set (fgu := isuniformlycontinuous_plus Q F _ _ _ (picard_integrand_uc f)
                    (isuniformlycontinuous_negate Q F _ _ (picard_integrand_uc f'))).
      assert (p : picard_value f x - picard_value f' x
                  = integral Q F (fun t => picard_integrand f t - picard_integrand f' t) fgu c x).
      { rewrite (integral_minus Q F _ _ (picard_integrand_uc f) (picard_integrand_uc f')).
        unfold picard_value.
        rewrite negate_plus_distr, (plus_comm y0), <- plus_assoc, (plus_assoc y0 (- y0)).
        rewrite plus_negate_r, plus_0_l; reflexivity. }
      rewrite p.
      lhs' refine (integral_abs_le Q F _ _ c x (L * dUL f f') _).
      - intro t; lhs' exact (gL _ _ _).
        assert (PropHolds (0 ≤ L)) by exact (lt_le _ _ L0).
        apply (order_preserving (L *.)), (le_uniform_dist Q F _ _ _ _ leab).
      - assert (LD0 : PropHolds (0 ≤ L * dUL f f')) by exact (nonneg_mult_compat _ _ (lt_le _ _ L0) D0).
        lhs' exact (order_preserving (_ *.) _ _ (abs_center_le x)).
        rewrite (mult_comm L), <- mult_assoc, (mult_comm (dUL f f')).
        exact (order_preserving (.* dUL f f') _ _ lLc).
    Qed.

    (** The constant map [y0]. *)
    Local Definition const_ulmap : UL.
    Proof.
      pose (b0' := lt_le _ _ b0).
      snrefine {| ulmap := {| umap := fun _ => interval_center y0 b b0'; umap_modulus := idmap |};
                  ulmap_lifts := fun _ _ => ly0 |}.
      intros e x y _; unfold metric_close, interval_dist; cbn.
      rewrite plus_negate_r, abs_0; exact (pos_rationals_to_field_qpos Q e).
    Defined.

    (* [half_pos] and [half_lt_1] in IntermediateValue.v state the same for [' (1 / 2 : Qpos Q)], with positivity in [F]; sharing them would mean using one representation of one half in both files. *)
    Local Lemma half_pos : 0 < (/ 2 : Q).
    Proof.
      apply pos_dec_recip_compat, lt_0_2.
    Qed.

    Local Lemma half_lt_1 : (/ 2 : Q) < 1.
    Proof.
      exact (lt_eq_trans _ _ _ (flip_lt_dec_recip 2 1 lt_0_1 lt_1_2) dec_recip_1).
    Qed.

    Context (C : Qpos Q) (leC : (y0 + b) - (y0 - b) ≤ ' (' C)).

    (** By Banach's fixed point theorem, the Picard iteration has a pseudo-fixed point, whose underlying map is a fixed point. *)
    Definition picard_solution : {f : UL & forall x, (f x).1 = picard_value f x}.
    Proof.
      destruct (banach_fixed_point Q dUL (IsPseudoMetric0 := ispseudometric_ulmap_dist Q F _ _ _ _ leab)
                  picard_map (/ 2) half_pos half_lt_1 islipschitz_picard_map
                  (MetricCauchyComplete0 := metriccauchycomplete_ulmap_dist Q F _ _ _ _ leab)
                  C const_ulmap
                  (uniform_dist_le Q F _ _ _ _ leab _ _ _
                     (fun x => transitivity (interval_dist_le _ _) leC)))
        as [f [p _]].
      exists f; intro x.
      exact (ap (fun h => (h x).1) (path_uniform_dist_zero Q F _ _ _ _ leab _ _ p))^.
    Defined.

  End iteration.

  (** ** Picard–Lindelöf *)

  Context (la : locator Q F a) (lL : locator Q F L).

  Local Definition locator_width (u r : F) (lu : locator Q F u) (lr : locator Q F r)
    : locator Q F (u + r - (u - r))
    := locator_plus Q F (locator_plus Q F lu lr)
         (locator_minus Q F (locator_plus Q F lu (locator_minus Q F lr))).

  Local Lemma qinc_pos (r : Q) (r0 : 0 < r) : 0 < (' r : F).
  Proof.
    rewrite <- (preserves_0 (f:=cast Q F)); exact (strictly_order_preserving _ _ _ r0).
  Qed.

  (** A rational bound on [g], from its value at the center and its modulus. *)
  Local Definition picard_bound : {K : Qpos Q & forall p, abs (g p) ≤ ' (' K)}.
  Proof.
    set (z := (interval_center x0 a (lt_le _ _ a0), interval_center y0 b (lt_le _ _ b0))).
    destruct (upper_bound Q F (locator_plus Q F (locator_width x0 a lx0 la)
                                      (locator_width y0 b ly0 lb))) as [B ltB].
    set (lgz := lg (fst z) (snd z) lx0 ly0).
    destruct (qpos_upper_bound Q F (locator_join Q F lgz (locator_minus Q F lgz))) as [r ltr].
    set (N := ' S (grid_modulus Q B v 1) : Qpos Q).
    assert (absz : abs (g z) ≤ join (g z) (- g z)).
    { apply abs_le; [|apply join_ub_l].
      apply flip_le_negate; rewrite negate_involutive; apply join_ub_r. }
    assert (lt : forall p, abs (g p) < ' (' (r + N))).
    { intro p; refine (le_lt_trans _ _ _ (abs_le_uniform g v gv B (lt_le _ _ ltB) z p) _).
      rewrite (preserves_plus (f:=cast Q F)).
      apply (strictly_order_preserving (+ _)).
      exact (le_lt_trans _ _ _ absz ltr). }
    exact (r + N; fun p => lt_le _ _ (lt p)).
  Defined.

  (** Picard–Lindelöf: we compute [l] with a locator and [0 < l ≤ a], and a uniformly continuous map [f : [x0 - l, x0 + l] -> [y0 - b, y0 + b]] that lifts to locators, with [f x = y0 + ∫_{x0}^x g (t, f t) dt]. *)
  Definition picard_lindelof
    : {l : F & {ll : locator Q F l & {bounds : (0 < l) * (l ≤ a) &
        {f : UniformLocatorMap Q F (x0 - l) (x0 + l) (y0 - b) (y0 + b) &
         forall x fu, (f x).1 = y0 + integral Q F
                                  (fun t => g (interval_incl x0 l a (snd bounds) t, f t)) fu
                                  (interval_center x0 l (lt_le _ _ (fst bounds))) x}}}}.
  Proof.
    destruct picard_bound as [K gK].
    destruct (qpos_upper_bound Q F lL) as [[rL rL0] ltL].
    assert (K0 := pos_is_pos K).
    set (u := b * ' (/ ' K)); set (w := ' (/ rL / 2) : F).
    assert (u0 : 0 < u).
    { apply pos_mult_compat; [exact b0|apply qinc_pos, pos_dec_recip_compat, K0]. }
    assert (w0 : 0 < w).
    { apply qinc_pos, pos_mult_compat; [apply pos_dec_recip_compat, rL0|exact half_pos]. }
    set (l := meet a (meet u w)).
    exists l.
    exists (locator_meet Q F la (locator_meet Q F (locator_times Q F lb (locator_left Q F _))
                                   (locator_left Q F _))).
    exists (meet_lt_l _ _ _ a0 (meet_lt_l _ _ _ u0 w0), meet_lb_l _ _).
    assert (lu : l ≤ u) by exact (transitivity (meet_lb_r _ _) (meet_lb_l _ _)).
    assert (lw : l ≤ w) by exact (transitivity (meet_lb_r _ _) (meet_lb_r _ _)).
    pose (l0 := lt_le _ _ (meet_lt_l _ _ _ a0 (meet_lt_l _ _ _ u0 w0)) : 0 ≤ l).
    assert (lKb : ' (' K) * l ≤ b).
    { refine (transitivity (order_preserving (' (' K) *.) _ _ lu) (eq_le _ _ _)).
      unfold u; rewrite mult_assoc, (mult_comm (' (' K))), <- mult_assoc.
      rewrite <- (preserves_mult (f:=cast Q F)), (dec_recip_inverse _ (lt_ne_flip _ _ K0)).
      rewrite (preserves_1 (f:=cast Q F)); apply mult_1_r. }
    assert (rLw : ' rL * w = ' (/ 2 : Q)).
    { unfold w; rewrite <- (preserves_mult (f:=cast Q F)); apply ap.
      rewrite mult_assoc, (dec_recip_inverse _ (lt_ne_flip _ _ rL0)); apply mult_1_l. }
    assert (lLc : L * l ≤ ' (/ 2 : Q)).
    { assert (PropHolds (0 ≤ L)) by exact (lt_le _ _ L0).
      assert (PropHolds (0 ≤ w)) by exact (lt_le _ _ w0).
      lhs' exact (order_preserving (L *.) _ _ lw).
      exact (transitivity (order_preserving (.* w) _ _ (lt_le _ _ ltL)) (eq_le _ _ rLw)). }
    destruct (qpos_upper_bound Q F (locator_width y0 b ly0 lb)) as [C ltC].
    destruct (picard_solution K gK l l0 (meet_lb_l _ _) lKb lLc C (lt_le _ _ ltC))
      as [f p].
    exists f; intros x fu; rewrite p; unfold picard_value; apply ap.
    exact (ap (fun fu' => integral Q F _ fu' _ x) (path_ishprop _ _)).
  Defined.

End picard_lindelof.
