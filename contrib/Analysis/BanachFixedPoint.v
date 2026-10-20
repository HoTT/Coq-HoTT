(** * The Banach fixed point theorem *)

(** For a map [T] on a pseudometric space with a rational Lipschitz constant [0 < c < 1], the iterates of [T] at any point have an explicit modulus of Cauchy convergence, so that a limit operator gives a point [x] with [d (T x) x = 0], unique up to distance zero. We first develop the powers of an element of an ordered ring and a logarithm-like function on the rationals that the modulus uses. *)

From HoTT Require Import Basics Types.Sigma Truncations.Core.
From HoTT.Spaces Require Import Nat.Core.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.naturals
  interfaces.rationals
  interfaces.round
  interfaces.archimedean
  theory.rationals
  implementations.peano_naturals
  theory.rings
  orders.orders
  orders.semirings
  orders.rings
  orders.naturals
  orders.rationals.
From HoTT_Contrib.Analysis Require Import MetricSpace.

Generalizable Variables A B Q R Rle Rlt.

(** ** Powers *)

(** We write [nat_iter n (mult c) 1] for the [n]th power of [c]. *)

Section powers.
  Context `{IsCRing R} `{Apart R} `{!FullPseudoSemiRingOrder Rle Rlt}.

  Local Notation nR := (naturals_to_semiring nat R).

  Lemma power_nonneg (c : R) (n : nat) : 0 ≤ c -> 0 ≤ nat_iter n (mult c) 1.
  Proof.
    intro c0; induction n as [|n IH].
    - exact le_0_1.
    - apply nonneg_mult_compat; [exact c0|exact IH].
  Qed.

  (** Powers of an element of [[0, 1]] decrease. *)
  Lemma power_antitone (c : R) (k n : nat) : 0 ≤ c -> c ≤ 1 -> (k <= n)%nat
    -> nat_iter n (mult c) 1 ≤ nat_iter k (mult c) 1.
  Proof.
    intros c0 c1 lekn; induction lekn as [|n lekn IH].
    - reflexivity.
    - rhs_V' exact IH; cbn.
      pose proof (power_nonneg c n c0).
      lhs' exact (order_preserving (.* nat_iter n (mult c) 1) c 1 c1).
      cbn; rewrite mult_1_l; reflexivity.
  Qed.

  (** A form of Bernoulli's inequality: [c^n (1 + n (1 - c)) ≤ 1] for [c] in [[0, 1]]. By induction, since [c (1 + X) + (1 - c) X = 1 + n (1 - c)] for [X = (n + 1) (1 - c) ≥ 0]. *)
  Lemma power_bernoulli (c : R) (n : nat) : 0 ≤ c -> c ≤ 1
    -> nat_iter n (mult c) 1 * (1 + nR n * (1 - c)) ≤ 1.
  Proof.
    intros c0 c1.
    assert (b0 : 0 ≤ 1 - c) by exact (snd (flip_nonneg_minus c 1) c1).
    induction n as [|n IH].
    - apply eq_le.
      exact (mult_1_l _ @ ap (plus one) (mult_0_l _) @ plus_0_r one).
    - rhs_V' exact IH.
      change (nat_iter (S n) (mult c) 1) with (c * nat_iter n (mult c) 1).
      rewrite nat_to_semiring_succ, (plus_mult_distr_r 1 (nR n) (1 - c)), (mult_1_l (1 - c)).
      set (P := nat_iter n (mult c) 1); set (X := 1 - c + nR n * (1 - c)).
      rewrite (mult_comm c P), <- (mult_assoc P c).
      pose proof (power_nonneg c n c0).
      apply (order_preserving (P *.)).
      assert (p : c * (1 + X) + (1 - c) * X = 1 + nR n * (1 - c)).
      { rewrite plus_mult_distr_l, mult_1_r, <- plus_assoc, <- plus_mult_distr_r.
        rewrite <- (plus_conjugate_alt 1 c), mult_1_l; unfold X.
        rewrite plus_assoc, <- (plus_conjugate_alt 1 c); reflexivity. }
      rewrite <- p.
      apply nonneg_plus_le_compat_r, nonneg_mult_compat; [exact b0|].
      apply nonneg_plus_compat; [exact b0|].
      apply nonneg_mult_compat; [apply nat_to_semiring_nonneg|exact b0].
  Qed.

End powers.

Section preserves_powers.
  Context `{IsSemiCRing A} `{IsSemiCRing B} (f : A -> B) `{!IsSemiRingPreserving f}.

  Lemma preserves_power (c : A) (n : nat)
    : f (nat_iter n (mult c) 1) = nat_iter n (mult (f c)) 1.
  Proof.
    induction n as [|n IH].
    - exact preserves_1.
    - exact (preserves_mult (f:=f) c _ @ ap (mult (f c)) IH).
  Qed.

End preserves_powers.

(** ** A logarithm-like function on the rationals *)

Section rational_log.
  Context `{Rationals Q} `{!RoundUpStrict Q}.

  Local Notation nQ := (naturals_to_semiring nat Q).

  (** A logarithm-like function: for a rational [0 < c < 1] and a positive rational [q], an exponent [n] with [c^n < q]. With [b = 1 - c] and [1 / (q b) < n], Bernoulli's inequality gives [c^n (1 + n b) ≤ 1 < q n b < q (1 + n b)]. *)
  Definition rational_log (c : Q) (c0 : 0 < c) (c1 : c < 1) (q : Qpos Q)
    : {n : nat & nat_iter n (mult c) 1 < ' q}.
  Proof.
    assert (lt01 : 0 < 1) by exact (transitivity c0 c1).
    set (b := 1 - c).
    assert (b0 : 0 < b) by exact (snd (flip_pos_minus c 1) c1).
    assert (qb0 : PropHolds (0 < ' q * b)).
    { apply pos_mult_compat; [apply pos_is_pos|exact b0]. }
    destruct (round_up_strict Q (/ (' q * b))) as [n ltn].
    exists n.
    set (B := 1 + nQ n * b).
    assert (B0 : PropHolds (0 < B)).
    { apply (lt_le_trans 0 1 B lt01).
      apply nonneg_plus_le_compat_r, nonneg_mult_compat.
      - apply nat_to_semiring_nonneg.
      - apply lt_le, b0. }
    assert (ltqnb : 1 < ' q * (nQ n * b)).
    { apply (strictly_order_preserving ((' q * b) *.)) in ltn.
      rewrite dec_recip_inverse, <- (mult_assoc (' q) b), (mult_comm b) in ltn;
        [exact ltn|apply lt_ne_flip, qb0]. }
    apply (strictly_order_reflecting (.* B)).
    rapply le_lt_trans; [exact (power_bernoulli c n (lt_le _ _ c0) (lt_le _ _ c1))|].
    lhs' exact ltqnb.
    pose proof (pos_is_pos q).
    apply (strictly_order_preserving (' q *.)), pos_plus_lt_compat_l, lt01.
  Defined.
End rational_log.

(** ** Lipschitz maps *)

Section lipschitz.
  Context {F : Type} `{OrderedField F}.

  (** A Lipschitz constant for a map between spaces with distances. *)
  Class IsLipschitz {X Y : Type} (dX : X -> X -> F) (dY : Y -> Y -> F) (f : X -> Y) (c : F)
    := is_lipschitz : forall x y, dY (f x) (f y) ≤ c * dX x y.

  Context {X : Type} (d : X -> X -> F) `{!IsPseudoMetric d}.

  (** For [c < 1], a pseudo-fixed point of a map with Lipschitz constant [c] is unique up to distance zero. *)
  Lemma pseudo_fixed_point_unique (T : X -> X) (c : F) (c1 : c < 1)
    (Tc : IsLipschitz d d T c) (x y : X) (px : d (T x) x = 0) (py : d (T y) y = 0)
    : d x y = 0.
  Proof.
    apply (antisymmetry (≤)); [|apply pseudometric_nonneg].
    apply not_lt_le_flip; intro dpos.
    apply (irreflexivity (<) (d x y)).
    rapply (le_lt_trans _ (c * d x y)).
    - lhs' exact (pseudometric_triangle x (T x) y).
      rewrite (pseudometric_symmetric x (T x)), px, plus_0_l.
      lhs' exact (pseudometric_triangle (T x) (T y) y).
      rewrite py, plus_0_r.
      apply Tc.
    - pose proof dpos.
      rapply lt_eq_trans; [apply (strictly_order_preserving (.* d x y)), c1|].
      apply mult_1_l.
  Qed.

End lipschitz.

Section fixed_points.
  Context {F : Type} `{OrderedField F}.
  Context {X : Type} (d : X -> X -> F) `{!IsMetric d}.

  (** In a metric space, a map with a Lipschitz constant [c < 1] has at most one fixed point. *)
  Lemma ishprop_fixed_point (T : X -> X) (c : F) (c1 : c < 1) (Tc : IsLipschitz d d T c)
    : IsHProp {x : X & T x = x}.
  Proof.
    pose proof (ishset_metric d).
    apply hprop_allpath; intros [x p] [y q].
    apply path_sigma_hprop; cbn.
    apply (metric_separated x y).
    apply (pseudo_fixed_point_unique d T c c1 Tc);
      [rewrite p | rewrite q]; apply pseudometric_diag.
  Qed.

  (** Since this is a proposition, it suffices that such a Lipschitz constant merely exists. *)
  Lemma ishprop_fixed_point_merely `{Funext} (T : X -> X)
    (Tc : hexists (fun c : F => c < 1 /\ IsLipschitz d d T c))
    : IsHProp {x : X & T x = x}.
  Proof.
    strip_truncations; destruct Tc as [c [c1 Tc]].
    exact (ishprop_fixed_point T c c1 Tc).
  Qed.

End fixed_points.

(** ** Lipschitz maps are uniformly continuous *)

Section lipschitz_uniform.
  Context (Q : Type) `{Rationals Q} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}.
  Context {F : Type} `{OrderedField F}.
  Let qinc : Cast Q F := rationals_to_field Q F.
  Existing Instance qinc.

  Context {X Y : Type} (dX : X -> X -> F) (dY : Y -> Y -> F).

  (** A positive rational Lipschitz constant [c] gives the modulus of uniform continuity [e / c]. *)
  Lemma isuniformmodulus_lipschitz (f : X -> Y) (c : Qpos Q)
    (fc : IsLipschitz dX dY f (' (' c)))
    : IsUniformModulus Q (metric_close Q dX) (metric_close Q dY) f (fun e => e / c).
  Proof.
    intros e x y close; unfold metric_close in *.
    rapply le_lt_trans; [exact (fc x y)|].
    assert (p : ' (' c) * ' (' (e / c)) = ' (' e)).
    { rewrite <- (preserves_mult (f:=cast Q F)).
      apply (ap (cast Q F)); change (' (c * (e / c)) = ' e); apply ap.
      rewrite (associativity c e (/ c)); apply pos_unconjugate. }
    rewrite <- p.
    assert (PropHolds (0 < (' (' c) : F))) by exact (pos_rationals_to_field_qpos Q c).
    apply (strictly_order_preserving _), close.
  Qed.

  Context {Farch : ArchimedeanProperty Q F} `{!IsPseudoMetric dX}.

  (** A positive Lipschitz constant in [F] merely gives a modulus of uniform continuity. *)
  Lemma merely_isuniformmodulus_lipschitz (f : X -> Y) (c : F) (c0 : 0 < c)
    (fc : IsLipschitz dX dY f c)
    : hexists (IsUniformModulus Q (metric_close Q dX) (metric_close Q dY) f).
  Proof.
    assert (r := archimedean_property Q F c (c + 1)
                   (fst (pos_plus_lt_compat_r c 1) lt_0_1)).
    strip_truncations; destruct r as [r [ltcr _]].
    assert (r0 : 0 < r).
    { apply rationals_to_field_pos_iff; exact (transitivity c0 ltcr). }
    apply tr; exists (fun e => e / mkQpos r r0).
    apply isuniformmodulus_lipschitz.
    intros x y; lhs' exact (fc x y).
    pose proof (pseudometric_nonneg (d:=dX) x y).
    apply (order_preserving (.* dX x y)), lt_le, ltcr.
  Qed.

End lipschitz_uniform.

(** ** Banach's fixed point theorem *)

Section banach.
  Context (Q : Type) `{Rationals Q} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}
    `{!RoundUpStrict Q}.
  Context {F : Type} `{OrderedField F}.
  Let qinc : Cast Q F := rationals_to_field Q F.
  Existing Instance qinc.

  Context {X : Type} (d : X -> X -> F) `{!IsPseudoMetric d}.
  Context (T : X -> X) (c : Q) (c0 : 0 < c) (c1 : c < 1) (Tc : IsLipschitz d d T (' c)).

  Local Lemma c_nonneg : PropHolds (0 ≤ (' c : F)).
  Proof.
    apply lt_le, rationals_to_field_pos_iff, c0.
  Qed.

  Local Lemma c_lt_1 : (' c : F) < 1.
  Proof.
    rewrite <- (preserves_1 (f:=cast Q F)).
    apply (strictly_order_preserving _), c1.
  Qed.

  Local Lemma one_minus_c_pos : PropHolds (0 < 1 - (' c : F)).
  Proof.
    exact (snd (flip_pos_minus _ _) c_lt_1).
  Qed.

  Local Existing Instances c_nonneg one_minus_c_pos.

  (** The distance between consecutive iterates decreases geometrically. *)
  Lemma iterate_step_le (y : X) (j : nat)
    : d (nat_iter (S j) T y) (nat_iter j T y) ≤ nat_iter j (mult (' c)) 1 * d (T y) y.
  Proof.
    induction j as [|j IH].
    - apply eq_le; symmetry; apply mult_1_l.
    - lhs' apply Tc.
      change (nat_iter (S j) (mult (' c)) 1) with (' c * nat_iter j (mult (' c)) 1).
      rewrite <- mult_assoc.
      apply (order_preserving (' c *.)), IH.
  Qed.

  Local Lemma iterate_dist_le_power (y : X) (j : nat)
    : (1 - ' c) * d (nat_iter j T y) y ≤ (1 - nat_iter j (mult (' c)) 1) * d (T y) y.
  Proof.
    induction j as [|j IH].
    - apply eq_le; cbn.
      rewrite (pseudometric_diag (d:=d)), mult_0_r, plus_negate_r, mult_0_l.
      reflexivity.
    - set (P := nat_iter j (mult (' c)) 1).
      change (nat_iter (S j) (mult (' c)) 1) with (' c * P).
      lhs' apply (order_preserving ((1 - ' c) *.)), (pseudometric_triangle _ (nat_iter j T y) _).
      rewrite plus_mult_distr_l.
      lhs' (apply plus_le_compat; [apply (order_preserving ((1 - ' c) *.)), iterate_step_le|exact IH]).
      apply eq_le.
      rewrite mult_assoc, <- plus_mult_distr_r.
      apply (ap (.* d (T y) y)).
      rewrite plus_mult_distr_r, mult_1_l, <- negate_mult_distr_l.
      rewrite plus_comm, plus_assoc, minus_plus_cancel; reflexivity.
  Qed.

  (** The distance from a point to its iterates is bounded in terms of its distance to its image. *)
  Lemma iterate_dist_le (y : X) (j : nat)
    : (1 - ' c) * d (nat_iter j T y) y ≤ d (T y) y.
  Proof.
    lhs' exact (iterate_dist_le_power y j).
    pose proof (pseudometric_nonneg (d:=d) (T y) y).
    lhs' refine (order_preserving (.* d (T y) y) _ 1 _).
    - apply nonneg_minus_compat; [|reflexivity].
      exact (power_nonneg _ j c_nonneg).
    - apply eq_le, mult_1_l.
  Qed.

  (** The modulus [log_c (e (1 - c) / C)]. *)
  Definition iterates_modulus (C : Qpos Q) (e : Qpos Q) : nat
    := (rational_log c c0 c1 (e * Qpos_diff c 1 c1 / C)).1.

  (** The defining property of the modulus: [c^M C < (1 - c) e]. *)
  Local Lemma iterates_modulus_spec (C e : Qpos Q)
    : nat_iter (iterates_modulus C e) (mult (' c)) 1 * ' (' C) < (1 - ' c) * ' (' e).
  Proof.
    set (b := Qpos_diff c 1 c1).
    assert (Cpos : PropHolds (0 < (' (' C) : F)))
      by exact (pos_rationals_to_field_qpos Q C).
    assert (spec : nat_iter (iterates_modulus C e) (mult c) 1 < ' (e * b / C))
      by exact (rational_log c c0 c1 (e * b / C)).2.
    apply (strictly_order_preserving (cast Q F)) in spec.
    rewrite (preserves_power (cast Q F)) in spec.
    rapply lt_eq_trans; [apply (strictly_order_preserving (.* ' (' C))), spec|].
    cbn beta; rewrite <- (preserves_mult (f:=cast Q F)).
    rewrite (mult_comm (1 - ' c)), <- (preserves_1 (f:=cast Q F)).
    rewrite <- (preserves_negate (f:=cast Q F)), <- (preserves_plus (f:=cast Q F)).
    rewrite <- (preserves_mult (f:=cast Q F)).
    apply (ap (cast Q F)).
    (* The positive rational [b] is [1 - c] by definition. *)
    change (' (e * b / C * C) = ' (e * b)); apply ap.
    rewrite (commutativity _ C), (associativity C _ (/ C)).
    apply pos_unconjugate.
  Qed.

  (** If [d (T x0) x0 ≤ C], then from the modulus for [e] on, the iterates of [T] at [x0] are [e]-close to the later ones. *)
  Lemma iterate_dist_lt (C : Qpos Q) (x0 : X) (C0 : d (T x0) x0 ≤ ' (' C)) (e : Qpos Q)
    (n k : nat) (leMn : (iterates_modulus C e <= n)%nat)
    : d (nat_iter (k + n) T x0) (nat_iter n T x0) < ' (' e).
  Proof.
    set (M := iterates_modulus C e) in *.
    rewrite nat_iter_add.
    apply (strictly_order_reflecting ((1 - ' c) *.)).
    rapply le_lt_trans; [exact (iterate_dist_le _ k)|].
    rapply le_lt_trans; [exact (iterate_step_le x0 n)|].
    pose proof (power_nonneg (' c : F) n c_nonneg).
    assert (PropHolds (0 < (' (' C) : F))) by exact (pos_rationals_to_field_qpos Q C).
    rapply le_lt_trans; [apply (order_preserving (_ *.)), C0|].
    rapply le_lt_trans.
    1: { apply (order_preserving (.* ' (' C))), (power_antitone _ M n).
         - exact c_nonneg.
         - apply lt_le, c_lt_1.
         - exact leMn. }
    exact (iterates_modulus_spec C e).
  Qed.

  (** Hence the iterates of [T] at [x0] form a sequence with a modulus of Cauchy convergence. *)
  Lemma metriccauchymodulus_iterates (C : Qpos Q) (x0 : X) (C0 : d (T x0) x0 ≤ ' (' C))
    : MetricCauchyModulus Q (metric_close Q d) (fun n => nat_iter n T x0) (iterates_modulus C).
  Proof.
    intros e m n lem len.
    destruct (leq_dichotomy n m) as [lenm|ltmn].
    - destruct (equiv_leq_add n m lenm) as [k p].
      unfold metric_close; rewrite <- p.
      exact (iterate_dist_lt C x0 C0 e n k len).
    - destruct (equiv_leq_add m n (leq_succ_l ltmn)) as [k p].
      unfold metric_close; rewrite (pseudometric_symmetric (d:=d)), <- p.
      exact (iterate_dist_lt C x0 C0 e m k lem).
  Qed.

  Context {Farch : ArchimedeanProperty Q F} `{!MetricCauchyComplete Q (metric_close Q d)}.

  (** Banach's fixed point theorem: in a Cauchy complete pseudometric space, a map with a rational Lipschitz constant [0 < c < 1] has a pseudo-fixed point, which is unique up to distance zero. The point [x0] with [d (T x0) x0 ≤ C] can be any point when the space is bounded by [C]. *)
  Definition banach_fixed_point (C : Qpos Q) (x0 : X) (C0 : d (T x0) x0 ≤ ' (' C))
    : {x : X & d (T x) x = 0 /\ forall y, d (T y) y = 0 -> d x y = 0}.
  Proof.
    set (xs := fun n => nat_iter n T x0).
    set (l := metric_limit Q (metric_close Q d) xs (iterates_modulus C)
                (metriccauchymodulus_iterates C x0 C0)).
    assert (islim : IsMetricLimit Q (metric_close Q d) xs l)
      by apply ismetriclimit_metric_limit.
    assert (p : d (T l) l = 0).
    { apply (metric_limit_distance_zero Q d (fun n => xs (S n))).
      - exact (preservesmetriclimits_uniform Q (metric_close Q d) (metric_close Q d) T _
                 (isuniformmodulus_lipschitz Q d d T (mkQpos c c0) Tc) xs l islim).
      - exact (ismetriclimit_tail Q (metric_close Q d) xs l islim). }
    exists l; split; [exact p|].
    intros y py.
    exact (pseudo_fixed_point_unique d T (' c) c_lt_1 Tc l y p py).
  Defined.

End banach.
