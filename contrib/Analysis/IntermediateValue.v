(** * Intermediate value theorems *)

(** We prove an approximate intermediate value theorem for pointwise continuous functions, following M. Frank, _Interpolating between choices for the approximate intermediate value theorem_ (LMCS 2020): instead of choosing the left or the right half of the interval at each step of the bisection, the next interval interpolates continuously between the two, so that no choice is needed to define the bisection. A function which takes a negative and a positive value merely takes values arbitrarily close to [0], and if it lifts to locators and the endpoints have locators, then we can find such a point, with a locator.

As Frank points out, the point is not always the limit of the bisection: interpolation can move an endpoint to a point where [f] was never evaluated. Following his proof, an invariant of the bisection shows that either the limit or one of the midpoints works.

We then prove an exact intermediate value theorem for functions which are locally nonconstant, continuous and lift to locators, without any choice principles: locators let us find a rational point at which the function is apart from [0], which we use to shrink an interval around a root. *)

From HoTT Require Import Basics Truncations.Core DProp Misc.BoundedSearch.
From HoTT.Spaces Require Import Nat.Core.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.rationals
  interfaces.archimedean
  interfaces.cauchy
  interfaces.round
  implementations.peano_naturals
  theory.rings
  theory.rationals
  orders.orders
  orders.rings
  orders.lattices
  orders.rationals.
From HoTT.Analysis Require Import Locator.
From HoTT_Contrib.Analysis Require Import
  MetricSpace CauchyCompleteness BanachFixedPoint LiftsToLocators.

Section ivt.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}
    {Qtrich : Trichotomy (<)}.
  Context (F : Type) `{Forderedfield : OrderedField F}.
  Context {Farch : ArchimedeanProperty Q F} {Qroundup : RoundUpStrict Q}.

  Local Existing Instance qinc.
  Local Instance orderpreserving_qinc : OrderPreserving (qinc Q F)
    := full_pseudo_order_preserving.

  Local Notation power r n := (nat_iter n (mult r) 1).

  (** ** Nested intervals *)

  (** Bounds on the tail of a sequence are bounds on its limit. *)
  Lemma le_limit (y : nat -> F) (l c : F) (N : nat) (islim : IsLimit Q F y l)
    (le : forall n, (N <= n)%nat -> c ≤ y n)
    : c ≤ l.
  Proof.
    apply not_lt_le_flip; intro ltlc.
    assert (e := merely_qpos_lt Q (c - l) (snd (flip_pos_minus _ _) ltlc)).
    strip_truncations; destruct e as [e ltec].
    assert (c' := islim e); strip_truncations; destruct c' as [M close].
    set (n := Nat.Core.nat_max N M).
    assert (lt := fst (close n (le_nat_max_r N M))).
    apply (irreflexivity (<) c).
    refine (le_lt_trans _ _ _ (le n (le_nat_max_l N M)) _).
    apply (fst (flip_lt_minus_r _ _ _)) in lt, ltec.
    rewrite plus_comm in lt, ltec.
    exact (transitivity (fst (flip_lt_minus_l _ _ _) lt) ltec).
  Qed.

  Lemma limit_le (y : nat -> F) (l c : F) (N : nat) (islim : IsLimit Q F y l)
    (le : forall n, (N <= n)%nat -> y n ≤ c)
    : l ≤ c.
  Proof.
    apply flip_le_negate.
    refine (le_limit _ _ _ N (islimit_negate Q _ _ islim) _).
    intros n len; exact (snd (flip_le_negate _ _) (le n len)).
  Qed.

  (** Nested intervals [[z n, w n]] whose widths are bounded by [B r^n] for rationals [B > 0] and [0 < r < 1]. Every sequence in the intervals has a modulus of Cauchy convergence, and converges to every point which lies in all the intervals. *)
  Section nested.
    Context (z w : nat -> F) (zinc : forall n, z n ≤ z (S n)) (wdec : forall n, w (S n) ≤ w n)
      (zw : forall n, z n ≤ w n)
      (B : Qpos Q) (r : Q) (r0 : 0 < r) (r1 : r < 1)
      (width : forall n, w n - z n ≤ ' (' B * power r n)).

    Lemma nested_le (n m : nat) (lenm : (n <= m)%nat) : z n ≤ z m /\ w m ≤ w n.
    Proof.
      induction lenm as [|m lenm IH].
      - split; reflexivity.
      - split.
        + exact (transitivity (fst IH) (zinc m)).
        + exact (transitivity (wdec m) (snd IH)).
    Qed.

    (** A modulus of convergence for the nested intervals. *)
    Definition nested_modulus (e : Qpos Q) : nat := (rational_log r r0 r1 (e / B)).1.

    Lemma nested_width_lt (e : Qpos Q) (n : nat) (len : (nested_modulus e <= n)%nat)
      : w n - z n < ' (' e).
    Proof.
      refine (le_lt_trans _ _ _ (width n) _).
      rapply strictly_order_preserving.
      rapply (le_lt_trans _ (' B * power r (nested_modulus e))).
      - apply (order_preserving (' B *.)).
        exact (power_antitone r _ _ (lt_le _ _ r0) (lt_le _ _ r1) len).
      - assert (p : ' B * ' (e / B) = ' e).
        { change (' (B * (e / B)) = ' e).
          rewrite (associativity B e (/ B)).
          exact (ap (cast (Qpos Q) Q) (pos_unconjugate B e)). }
        rewrite <- p.
        apply (strictly_order_preserving (' B *.)).
        exact (rational_log r r0 r1 (e / B)).2.
    Qed.

    (** A sequence [y] in the nested intervals has a modulus of Cauchy convergence. *)
    Lemma cauchymodulus_nested (y : nat -> F) (zyw : forall n, z n ≤ y n ≤ w n)
      : CauchyModulus Q F y nested_modulus.
    Proof.
      intros e m n lem len.
      set (M := nested_modulus e) in *.
      destruct (nested_le M m lem) as [zm wm], (nested_le M n len) as [zn wn].
      apply (interval_minus_lt (z M) (w M)).
      - exact (transitivity zm (fst (zyw m)), transitivity (snd (zyw m)) wm).
      - exact (transitivity zn (fst (zyw n)), transitivity (snd (zyw n)) wn).
      - exact (nested_width_lt e M (leq_refl M)).
    Qed.

    (** A limit of the lower endpoints lies in all the intervals. *)
    Lemma nested_limit_between (l : F) (islim : IsLimit Q F z l) (n : nat)
      : z n ≤ l ≤ w n.
    Proof.
      split.
      - exact (le_limit z l (z n) n islim (fun m lenm => fst (nested_le n m lenm))).
      - refine (limit_le z l (w n) n islim _).
        intros m lenm; exact (transitivity (zw m) (snd (nested_le n m lenm))).
    Qed.

    (** An element of all the intervals is the limit of every sequence in the intervals. *)
    Lemma islimit_nested (y : nat -> F) (zyw : forall n, z n ≤ y n ≤ w n)
      (l : F) (zlw : forall n, z n ≤ l ≤ w n)
      : IsLimit Q F y l.
    Proof.
      intro e; apply tr; exists (nested_modulus e); intros n len.
      exact (interval_minus_lt (z n) (w n) l (y n) _ (zlw n) (zyw n) (nested_width_lt e n len)).
    Qed.

  End nested.

  (** ** The approximate intermediate value theorem *)

  Definition locator_0 : locator Q F 0
    := transport (locator Q F) (preserves_0 (f:=cast Q F)) (locator_left Q F 0).

  Local Definition locator_1 : locator Q F 1
    := transport (locator Q F) (preserves_1 (f:=cast Q F)) (locator_left Q F 1).

  (** A rational strict upper bound of a nonnegative element is positive. *)
  Lemma qpos_of_upper_bound (u : F) (r : Q) (u0 : 0 ≤ u) (ltr : u < ' r) : 0 < r.
  Proof.
    apply (strictly_order_reflecting (cast Q F)).
    rewrite (preserves_0 (f:=cast Q F)); exact (le_lt_trans _ _ _ u0 ltr).
  Qed.

  (** *** Interpolating bisection *)

  Local Notation half := (' (1 / 2 : Qpos Q) : Q).

  (** Arithmetic with [1 / 2]. *)
  Lemma half_plus_half (u : F) : u * ' half + u * ' half = u.
  Proof.
    rewrite <- plus_mult_distr_l, <- (preserves_plus (f:=cast Q F)).
    change (half + half) with (' (1 / 2 + 1 / 2 : Qpos Q)).
    rewrite <- (pos_split2 1).
    rewrite (preserves_1 (f:=cast Q F)); apply mult_1_r.
  Qed.

  Definition half_lt_1 : half < 1 := qpos_half_lt 1.

  Lemma half_pos : (0 : F) < ' half.
  Proof.
    exact (pos_rationals_to_field_qpos Q (1 / 2)).
  Qed.

  Lemma half_double (u v : F) : u + (v - u) * ' half + (v - u) * ' half = v.
  Proof.
    rewrite <- plus_assoc, half_plus_half.
    rewrite plus_comm, <- plus_assoc, (plus_negate_l u); apply plus_0_r.
  Qed.

  (** Clamping to the unit interval. *)
  Definition clamp (u : F) : F := join 0 (meet u 1).

  Lemma clamp_between (u : F) : 0 ≤ clamp u ≤ 1.
  Proof.
    split.
    - apply join_ub_l.
    - apply join_le; [exact le_0_1|apply meet_lb_r].
  Qed.

  Lemma clamp_1 (u : F) (le1u : 1 ≤ u) : clamp u = 1.
  Proof.
    unfold clamp; rewrite (meet_r u 1 le1u); exact (join_r 0 1 le_0_1).
  Qed.

  Lemma clamp_0 (u : F) (leu0 : u ≤ 0) : clamp u = 0.
  Proof.
    unfold clamp; rewrite (meet_l u 1 (transitivity leu0 le_0_1)); exact (join_l 0 u leu0).
  Qed.

  (** A step of the bisection. Given an interval [[z, w]] with midpoint [c = z + h] and a weight [d] in [[0, 1]], the next interval is [[z + (1 - d) h, c + (1 - d) h]]: for [d = 1] this is the left half, for [d = 0] the right half, and in general it interpolates between the two. *)
  Definition bisect_step (dec : F -> F) (zw : F * F) : F * F
    := let h := (snd zw - fst zw) * ' half in
       let c := fst zw + h in
       let d := dec c in
       (fst zw + (1 - d) * h, c + (1 - d) * h).

  (** The interpolated interval lies in the left half extended by its right neighbour. *)
  Lemma interpolate_ordered (u v dd : F) (leuv : u ≤ v) (dd01 : 0 ≤ dd ≤ 1)
    : let h := (v - u) * ' half in
      u ≤ u + (1 - dd) * h /\ u + (1 - dd) * h ≤ u + h
      /\ u + h ≤ u + h + (1 - dd) * h /\ u + h + (1 - dd) * h ≤ v.
  Proof.
    intro h.
    assert (h0 : 0 ≤ h).
    { apply nonneg_mult_compat; [exact (snd (flip_nonneg_minus _ _) leuv)|].
      exact (lt_le _ _ half_pos). }
    assert (D0 : 0 ≤ (1 - dd) * h).
    { exact (nonneg_mult_compat _ _ (snd (flip_nonneg_minus _ _) (snd dd01)) h0). }
    assert (Dh : (1 - dd) * h ≤ h).
    { assert (le1 : 1 - dd ≤ 1).
      { apply (snd (flip_le_minus_l _ _ _)).
        exact (fst (nonneg_plus_le_compat_r _ _) (fst dd01)). }
      lhs' exact (order_preserving (.* h) _ _ le1).
      rewrite mult_1_l; reflexivity. }
    refine (_, (_, (_, _))).
    - exact (fst (nonneg_plus_le_compat_r _ _) D0).
    - exact (order_preserving (u +) _ _ Dh).
    - exact (fst (nonneg_plus_le_compat_r _ _) D0).
    - rewrite <- (half_double u v).
      exact (order_preserving (u + h +) _ _ Dh).
  Qed.

  Section bisect.
    Context (dec : F -> F) (decbetween : forall y, 0 ≤ dec y ≤ 1) (a b : F) (leab : a ≤ b).

    (** The intervals of the bisection, their endpoints and midpoints. *)
    Definition bisect (n : nat) : F * F := nat_iter n (bisect_step dec) (a, b).
    Definition bisect_lower (n : nat) : F := fst (bisect n).
    Definition bisect_upper (n : nat) : F := snd (bisect n).
    Definition bisect_mid (n : nat) : F
      := bisect_lower n + (bisect_upper n - bisect_lower n) * ' half.

    Local Notation z := bisect_lower.
    Local Notation w := bisect_upper.
    Local Notation c := bisect_mid.
    Local Notation h n := ((w n - z n) * ' half).
    Local Notation d n := (dec (c n)).

    Lemma bisect_lower_succ (n : nat) : z (S n) = z n + (1 - d n) * h n.
    Proof. reflexivity. Qed.

    Lemma bisect_upper_succ (n : nat) : w (S n) = c n + (1 - d n) * h n.
    Proof. reflexivity. Qed.

    Lemma bisect_width (n : nat) : w (S n) - z (S n) = h n.
    Proof.
      rewrite bisect_lower_succ, bisect_upper_succ; unfold bisect_mid.
      rewrite negate_plus_distr, (plus_comm (- z n)).
      rewrite <- (plus_assoc (z n + h n)), (plus_assoc ((1 - d n) * h n)).
      rewrite (plus_negate_r ((1 - d n) * h n)), (plus_0_l (- z n)).
      rewrite (plus_comm (z n)), <- plus_assoc, (plus_negate_r (z n)); apply plus_0_r.
    Qed.

    (** For the weights [1] and [0] the bisection takes the left and the right half. *)
    Lemma bisect_lower_1 (n : nat) (d1 : d n = 1) : z (S n) = z n.
    Proof.
      rewrite bisect_lower_succ, d1, (plus_negate_r 1), (mult_0_l (h n)); apply plus_0_r.
    Qed.

    Lemma bisect_lower_0 (n : nat) (d0 : d n = 0) : z (S n) = c n.
    Proof.
      rewrite bisect_lower_succ, d0, negate_0, (plus_0_r 1), (mult_1_l (h n)); reflexivity.
    Qed.

    Lemma bisect_upper_1 (n : nat) (d1 : d n = 1) : w (S n) = c n.
    Proof.
      rewrite bisect_upper_succ, d1, (plus_negate_r 1), (mult_0_l (h n)); apply plus_0_r.
    Qed.

    Lemma bisect_upper_0 (n : nat) (d0 : d n = 0) : w (S n) = w n.
    Proof.
      rewrite bisect_upper_succ, d0, negate_0, (plus_0_r 1), (mult_1_l (h n)).
      exact (half_double (z n) (w n)).
    Qed.

    (** The width halves at each step. *)
    Lemma bisect_width_power (n : nat)
      : w n - z n = (b - a) * ' (nat_iter n (mult half) 1).
    Proof.
      induction n as [|n IH].
      - rewrite (preserves_1 (f:=cast Q F)), mult_1_r; reflexivity.
      - rewrite bisect_width, IH, <- mult_assoc, <- (preserves_mult (f:=cast Q F)).
        rewrite (mult_comm _ half); reflexivity.
    Qed.

    (** The intervals are nested, and each contains the previous midpoint. *)
    Lemma bisect_le (n : nat) : z n ≤ w n.
    Proof.
      induction n as [|n IH].
      - exact leab.
      - destruct (interpolate_ordered (z n) (w n) (d n) IH (decbetween _))
          as [_ [lezc [lecw _]]].
        exact (transitivity lezc lecw).
    Qed.

    Lemma bisect_ordered (n : nat)
      : z n ≤ z (S n) /\ z (S n) ≤ c n /\ c n ≤ w (S n) /\ w (S n) ≤ w n.
    Proof.
      exact (interpolate_ordered (z n) (w n) (d n) (bisect_le n) (decbetween _)).
    Qed.

    (** The widths are bounded by [B / 2^n] for a rational bound [B] on [b - a]. *)
    Lemma bisect_width_le (B : Qpos Q) (leB : b - a ≤ ' (' B)) (n : nat)
      : w n - z n ≤ ' (' B * nat_iter n (mult half) 1).
    Proof.
      rewrite bisect_width_power, (preserves_mult (f:=cast Q F)).
      assert (P0 : (0 : F) ≤ ' (nat_iter n (mult half) 1)).
      { rewrite (preserves_power (cast Q F)).
        apply power_nonneg, lt_le, half_pos. }
      exact (order_preserving (.* ' (nat_iter n (mult half) 1)) _ _ leB).
    Qed.

    Lemma bisect_mid_between (n : nat) : z n ≤ c n ≤ w n.
    Proof.
      destruct (bisect_ordered n) as [zz [zc [cw ww]]].
      exact (transitivity zz zc, transitivity cw ww).
    Qed.

  End bisect.

  (** For a function [f] and a positive rational [t], the weight [d] in the bisection is [1] when [f] is above [t] at the midpoint, [0] when it is below [- t], and interpolates linearly in between. *)
  Definition bisect_weight (f : F -> F) (t : Qpos Q) (y : F) : F
    := clamp ((f y + ' (' t)) * ' (' (/ (t + t)))).

  Section weight.
    Context (f : F -> F) (t : Qpos Q).

    Local Lemma weight_factor : (' (' (t + t)) * ' (' (/ (t + t))) : F) = 1.
    Proof.
      rewrite <- (preserves_mult (f:=cast Q F)).
      change ((' (' ((t + t) / (t + t))) : F) = 1).
      rewrite pos_recip_r; apply (preserves_1 (f:=cast Q F)).
    Qed.

    Lemma bisect_weight_between (y : F) : 0 ≤ bisect_weight f t y ≤ 1.
    Proof.
      apply clamp_between.
    Qed.

    Lemma bisect_weight_1 (y : F) (lt : ' (' t) < f y) : bisect_weight f t y = 1.
    Proof.
      apply clamp_1.
      pose proof (lt_le _ _ (pos_rationals_to_field_qpos Q (/ (t + t)))).
      rewrite <- weight_factor.
      apply (order_preserving (.* _)).
      change (' (' t + ' t) ≤ f y + ' (' t)).
      rewrite (preserves_plus (f:=cast Q F)).
      exact (order_preserving (+ _) _ _ (lt_le _ _ lt)).
    Qed.

    Lemma bisect_weight_0 (y : F) (lt : f y < - ' (' t)) : bisect_weight f t y = 0.
    Proof.
      apply clamp_0.
      pose proof (lt_le _ _ (pos_rationals_to_field_qpos Q (/ (t + t)))).
      rewrite <- (mult_0_l (' (' (/ (t + t))))).
      apply (order_preserving (.* _)).
      rewrite <- (plus_negate_l (' (' t))).
      exact (order_preserving (+ _) _ _ (lt_le _ _ lt)).
    Qed.
  End weight.

  Section approximate.
    Context `{Funext} {Fcomplete : IsComplete Q F}.
    Context (f : F -> F) (a b : F) (leab : a ≤ b) (fa : f a < 0) (fb : 0 < f b) (e : Qpos Q).

    Local Notation dec := (bisect_weight f (e / 2)).
    Local Notation z := (bisect_lower dec a b).
    Local Notation w := (bisect_upper dec a b).
    Local Notation c := (bisect_mid dec a b).

    Local Lemma merely_bound : hexists (fun B : Qpos Q => b - a ≤ ' (' B)).
    Proof.
      assert (lt := fst (pos_plus_lt_compat_r (b - a) 1) lt_0_1).
      assert (q := archimedean_property Q F _ _ lt); strip_truncations.
      destruct q as [q [ltq _]].
      assert (qpos := qpos_of_upper_bound _ q (snd (flip_nonneg_minus _ _) leab) ltq).
      exact (tr (mkQpos q qpos; lt_le _ _ ltq)).
    Qed.

    Local Definition ordered := bisect_ordered dec (bisect_weight_between f _) a b leab.
    Local Definition zinc n := fst (ordered n).
    Local Definition wdec n := snd (snd (snd (ordered n))).
    Local Definition zw := bisect_le dec (bisect_weight_between f _) a b leab.

    Local Lemma cauchymodulus_bisect (B : Qpos Q) (leB : b - a ≤ ' (' B))
      : CauchyModulus Q F z (nested_modulus B half (pos_is_pos _) half_lt_1).
    Proof.
      exact (cauchymodulus_nested z w zinc wdec B half (pos_is_pos _) half_lt_1
               (bisect_width_le dec a b B leB) z (fun n => (reflexivity _, zw n))).
    Qed.

    (** The common limit of the endpoints and midpoints of the bisection. *)
    Definition approximate_root_islimit : {x : F & IsLimit Q F z x}.
    Proof.
      refine (limit_complete Q z _).
      assert (B := merely_bound); strip_truncations; destruct B as [B leB].
      exact (tr (_; cauchymodulus_bisect B leB)).
    Defined.

    Definition approximate_root : F := approximate_root_islimit.1.

    (** The candidates for a point where [f] is close to [0]: the limit and the midpoints. *)
    Definition approximate_candidate (n : nat) : F
      := match n with
         | O => approximate_root
         | S n => c n
         end.

    (** The limit lies in all the intervals, and is also the limit of the upper endpoints and of the midpoints. *)
    Local Definition approximate_root_between
      := nested_limit_between z w zinc wdec zw _ approximate_root_islimit.2.

    Local Lemma islimit_bisect_upper : IsLimit Q F w approximate_root.
    Proof.
      assert (B := merely_bound); strip_truncations; destruct B as [B leB].
      exact (islimit_nested z w B half (pos_is_pos _) half_lt_1
               (bisect_width_le dec a b B leB) w (fun n => (zw n, reflexivity _)) _
               approximate_root_between).
    Qed.

    Local Lemma islimit_bisect_mid : IsLimit Q F c approximate_root.
    Proof.
      assert (B := merely_bound); strip_truncations; destruct B as [B leB].
      exact (islimit_nested z w B half (pos_is_pos _) half_lt_1
               (bisect_width_le dec a b B leB) c
               (bisect_mid_between dec (bisect_weight_between f _) a b leab) _
               approximate_root_between).
    Qed.

    (** The invariant of the bisection: at every stage, either [f] is close to [0] at one of the midpoints so far, or [f] is still negative at the lower endpoint and positive at the upper endpoint. *)
    Lemma bisect_invariant (m : nat)
      : hor {j : nat & prod (j < m)%nat (- ' (' e) < f (c j) < ' (' e))}
          (prod (f (z m) < 0) (0 < f (w m))).
    Proof.
      assert (halfpos := pos_rationals_to_field_qpos Q (F:=F) (e / 2)).
      induction m as [|m IH].
      1: exact (tr (inr (fa, fb))).
      strip_truncations; destruct IH as [[j [ltj close]]|[neg pos]].
      1: exact (tr (inl (j; (leq_succ_r ltj, close)))).
      (* Compare [f (c m)] with [e / 2] and [e], and with [- e] and [- e / 2]. *)
      assert (ltte : (' (' (e / 2)) : F) < ' (' e))
        by exact (strictly_order_preserving _ _ _ (qpos_half_lt e)).
      assert (h := cotransitive ltte (f (c m))); strip_truncations.
      destruct h as [lt|lte].
      - (* The next interval is the left half, whose upper endpoint is [c m]. *)
        apply tr, inr.
        assert (d1 := bisect_weight_1 f _ _ lt).
        rewrite (bisect_lower_1 dec a b m d1), (bisect_upper_1 dec a b m d1).
        exact (neg, transitivity halfpos lt).
      - assert (h := cotransitive (snd (flip_lt_negate _ _) ltte) (f (c m))).
        strip_truncations; destruct h as [lte'|lt].
        + exact (tr (inl (m; (leq_refl _, (lte', lte))))).
        + (* The next interval is the right half, whose lower endpoint is [c m]. *)
          apply tr, inr.
          assert (d0 := bisect_weight_0 f _ _ lt).
          rewrite (bisect_lower_0 dec a b m d0), (bisect_upper_0 dec a b m d0).
          exact (transitivity lt (fst (flip_pos_negate _) halfpos), pos).
    Qed.

    Context (cont : forall y, a ≤ y ≤ b -> IsContinuousAt Q F f y).

    Local Definition cont_root := cont approximate_root (approximate_root_between 0).

    (** The approximate intermediate value theorem: [f] is less than [e] in absolute value at one of the candidates. Take [m] so large that [z m] and [w m] are close to the limit [x]. If [f] is close to [0] at some [c j], we are done. Otherwise [f (z m) < 0 < f (w m)], and [f x] is within [e] of both, so [f x] is close to [0]. *)
    Lemma approximate_ivt_candidates
      : hexists (fun n => - ' (' e) < f (approximate_candidate n) < ' (' e)).
    Proof.
      assert (d := cont_root e); strip_truncations; destruct d as [d close].
      assert (N := approximate_root_islimit.2 d); assert (M := islimit_bisect_upper d).
      strip_truncations; destruct N as [N zN], M as [M wM].
      set (m := Nat.Core.nat_max N M).
      assert (inv := bisect_invariant m); strip_truncations.
      destruct inv as [[j [_ cj]]|[neg pos]].
      1: exact (tr (S j; cj)).
      apply tr; exists 0%nat; split.
      - lhs' exact (fst (close (w m) (wM m (le_nat_max_r N M)))).
        exact (fst (pos_minus_lt_compat_r _ _) pos).
      - rhs_V' exact (snd (close (z m) (zN m (le_nat_max_l N M)))).
        exact (fst (pos_plus_lt_compat_r _ _) (fst (flip_neg_negate _) neg)).
    Qed.

    (** Hence [f] merely takes values arbitrarily close to [0]. *)
    Definition approximate_ivt
      : hexists (fun y => - ' (' e) < f y < ' (' e))
      := Trunc_functor (-1) (fun nc : {n : nat & - ' (' e) < f (approximate_candidate n) < ' (' e)}
                               => (approximate_candidate nc.1; nc.2))
           approximate_ivt_candidates.

    (** *** Locators *)

    Context (lift : LiftsToLocators Q F f)
      (la : locator Q F a) (lb : locator Q F b).

    Local Notation plus := (locator_plus Q F).
    Local Notation times := (locator_times Q F).
    Local Notation minus := (locator_minus Q F).
    Local Notation rat := (locator_left Q F).

    (** If the endpoints of an interval have locators, then so does its midpoint, and hence so do all the endpoints of the bisection. *)
    Local Definition locator_mid {u v : F} (lu : locator Q F u) (lv : locator Q F v)
      : locator Q F (u + (v - u) * ' half)
      := plus lu (times (plus lv (minus lu)) (rat half)).

    Definition bisect_locators (n : nat) : locator Q F (z n) * locator Q F (w n).
    Proof.
      induction n as [|n [lz lw]].
      - exact (la, lb).
      - set (lc := locator_mid lz lw).
        assert (ld : locator Q F (dec (c n))).
        { refine (locator_join Q F locator_0 (locator_meet Q F _ locator_1)).
          exact (times (plus (lift _ lc) (rat _)) (rat _)). }
        assert (lD := times (plus locator_1 (minus ld)) (times (plus lw (minus lz)) (rat half))).
        exact (plus lz lD, plus lc lD).
    Defined.

    Definition bisect_mid_locator (n : nat) : locator Q F (c n)
      := locator_mid (fst (bisect_locators n)) (snd (bisect_locators n)).

    (** The limit of the bisection has a locator, as a limit of midpoints with locators. *)
    Definition approximate_root_locator : locator Q F approximate_root.
    Proof.
      destruct (qpos_upper_bound Q F (plus lb (minus la))) as [B ltB].
      refine (locator_limit Q F (xs:=c) (M:=nested_modulus B half (pos_is_pos _) half_lt_1)
                bisect_mid_locator islimit_bisect_mid).
      exact (cauchymodulus_nested z w zinc wdec B half (pos_is_pos _) half_lt_1
               (bisect_width_le dec a b B (lt_le _ _ ltB)) c
               (bisect_mid_between dec (bisect_weight_between f _) a b leab)).
    Defined.

    Definition approximate_candidate_locator (n : nat)
      : locator Q F (approximate_candidate n)
      := match n with
         | O => approximate_root_locator
         | S n => bisect_mid_locator n
         end.

  End approximate.

  (** If [f] lifts to locators and [a] and [b] have locators, we can find a point with a locator at which [f] is close to [0]. We search for one among the candidates for [e / 2], deciding approximately with locators for their values. *)
  Definition approximate_ivt_locator `{Funext} {Fcomplete : IsComplete Q F}
    (f : F -> F) (a b : F) (leab : a ≤ b) (fa : f a < 0) (fb : 0 < f b) (e : Qpos Q)
    (cont : forall y, a ≤ y ≤ b -> IsContinuousAt Q F f y)
    (lift : LiftsToLocators Q F f) (la : locator Q F a) (lb : locator Q F b)
    : {y : F & (locator Q F y * (- ' (' e) < f y < ' (' e)))%type}.
  Proof.
    set (y := approximate_candidate f a b leab (e / 2)).
    set (ly := approximate_candidate_locator f a b leab (e / 2) lift la lb).
    set (l n := lift (y n) (ly n)).
    assert (lt1 : - ' e < - ' (e / 2)) by exact (snd (flip_lt_negate _ _) (qpos_half_lt e)).
    set (P n := (locates_right Q F _ (l n) _ _ lt1 * locates_left Q F (l n) (qpos_half_lt e))%type).
    assert (Pdec : forall n, Decidable (P n)) by exact _.
    assert (inh : hexists P).
    { refine (Trunc_functor (-1) _ (approximate_ivt_candidates f a b leab fa fb (e / 2) cont)).
      intros [n [lo hi]]; exists n; split.
      - apply ltrx_locates_right.
        rewrite (preserves_negate (f:=cast Q F)); exact lo.
      - exact (ltxq_locates_left Q F (l n) _ hi). }
    destruct (minimal_n P Pdec inh) as [n [Pr Pl]].
    exists (y n); split; [exact (ly n)|split].
    - rewrite <- (preserves_negate (f:=cast Q F)).
      exact (locates_right_true Q F _ (l n) _ _ lt1 Pr).
    - exact (locates_right_false Q F _ (l n) _ _ _ Pl).
  Defined.

  (** ** The exact intermediate value theorem *)

  (** A function is locally nonconstant if on every nontrivial interval it takes a value apart from any given [t]. This is a property. *)
  Definition IsLocallyNonconstant (f : F -> F)
    := forall x y t : F, x < y -> hexists (fun z => ((x < z < y) * (f z ≶ t))%type).

  (** If [x < y], a rational number lies between [x] and [y] and within [d] of [z], provided [z] lies between [x] and [y]. *)
  Local Lemma rational_between_close (x y z : F) (d : Qpos Q) (xzy : x < z < y)
    : hexists (fun r : Q => ((x < ' r < y) * field_close Q d z (' r))%type).
  Proof.
    assert (dpos := pos_rationals_to_field_qpos Q (F:=F) d).
    assert (lt : join x (z - ' (' d)) < meet y (z + ' (' d))).
    { assert (lt1 : z - ' (' d) < z) by exact (fst (pos_minus_lt_compat_r _ _) dpos).
      assert (lt2 : z < z + ' (' d)) by exact (fst (pos_plus_lt_compat_r _ _) dpos).
      apply join_lt_r; apply meet_lt_l.
      - exact (transitivity (fst xzy) (snd xzy)).
      - exact (transitivity (fst xzy) lt2).
      - exact (transitivity lt1 (snd xzy)).
      - exact (transitivity lt1 lt2). }
    refine (Trunc_functor (-1) _ (archimedean_property Q F _ _ lt)).
    intros [r [ltr rlt]]; exists r; split; [split|split].
    - exact (le_lt_trans _ _ _ (join_ub_l _ _) ltr).
    - exact (lt_le_trans _ _ _ rlt (meet_lb_l _ _)).
    - apply (snd (flip_lt_minus_r _ _ _)); rewrite plus_comm.
      apply (snd (flip_lt_minus_l _ _ _)).
      exact (lt_le_trans _ _ _ rlt (meet_lb_r _ _)).
    - apply (snd (flip_lt_minus_l _ _ _)); rewrite plus_comm.
      apply (fst (flip_lt_minus_l _ _ _)).
      exact (le_lt_trans _ _ _ (join_ub_r _ _) ltr).
  Qed.

  (** Locators let us turn local nonconstancy into structure, and find roots. *)
  Section search.
    Context `{Funext} (QQpos_eq : nat <~> Q * Qpos Q).
    Context (f : F -> F) (cont : IsPointwiseContinuous Q F f) (lnc : IsLocallyNonconstant f)
      (lift : LiftsToLocators Q F f).

    (** A locally nonconstant continuous function merely takes a value apart from [t] at a rational point between [x] and [y]. *)
    Local Lemma merely_rational_apart (x y t : F) (ltxy : x < y)
      : hexists (fun r : Q => ((x < ' r < y) * ((t < f (' r)) + (f (' r) < t)))%type).
    Proof.
      assert (h := lnc x y t ltxy); strip_truncations; destruct h as [z [xzy ap]].
      destruct (fst (apart_iff_total_lt _ _) ap) as [ltzt|lttz].
      - assert (d := iscontinuousat_lt Q F (fun u => - f u) z
                       (iscontinuousat_negate Q F f z (cont z)) _ (snd (flip_lt_negate _ _) ltzt)).
        strip_truncations; destruct d as [d below].
        refine (Trunc_functor (-1) _ (rational_between_close x y z d xzy)).
        intros [r [xry c]]; exists r; split; [exact xry|right].
        exact (fst (flip_lt_negate _ _) (below _ c)).
      - assert (d := iscontinuousat_lt Q F f z (cont z) _ lttz).
        strip_truncations; destruct d as [d above].
        refine (Trunc_functor (-1) _ (rational_between_close x y z d xzy)).
        intros [r [xry c]]; exists r; split; [exact xry|left].
        exact (above _ c).
    Qed.

    (** Using locators, we can find such a rational. This turns the property of being locally nonconstant into structure. *)
    Section rational_apart.
      Context {x y t : F} (lx : locator Q F x) (ly : locator Q F y) (lt : locator Q F t).

      (** [f r - t] has a locator. *)
      Local Definition locator_value_minus (r : Q) : locator Q F (f (' r) - t)
        := locator_plus Q F (lift _ (locator_left Q F r)) (locator_minus Q F lt).

      (** For a rational [r] and a positive rational [n], we decide approximately whether [r] is [n]-far from [x] and [y], and whether [f r] is [n]-far from [t]. *)
      Local Definition RationalFar (rn : Q * Qpos Q) : Type
        := let (r, n) := rn in
           (locates_left Q F (lx : locator' Q F x)
              (fst (pos_minus_lt_compat_r r (' n)) (pos_is_pos n))
            * locates_right Q F _ (ly : locator' Q F y) _ _
                (fst (pos_plus_lt_compat_r r (' n)) (pos_is_pos n))
            * (locates_right Q F _ (locator_value_minus r : locator' Q F _) _ _ (qpos_half_lt n)
               + locates_left Q F (locator_value_minus r : locator' Q F _)
                   (snd (flip_lt_negate _ _) (qpos_half_lt n))))%type.

      Local Instance decidable_rationalfar (rn : Q * Qpos Q) : Decidable (RationalFar rn).
      Proof.
        destruct rn as [r n]; exact _.
      Defined.

      (** A rational [r] which is [n]-far from [x], [y] and, in its value, from [t] satisfies [RationalFar]. *)
      Local Lemma rationalfar_lt (r : Q) (n : Qpos Q)
        (ltr : ' (' n) < ' r - x) (rlt : ' (' n) < y - ' r)
        (ap : (' (' n) < f (' r) - t) + (' (' n) < t - f (' r)))
        : RationalFar (r, n).
      Proof.
        refine ((_, _), _).
        - apply ltxq_locates_left.
          rewrite (preserves_minus (f:=cast Q F)).
          apply flip_lt_minus_r; rewrite plus_comm; apply flip_lt_minus_r; exact ltr.
        - apply ltrx_locates_right.
          rewrite (preserves_plus (f:=cast Q F)).
          rewrite plus_comm; apply flip_lt_minus_r; exact rlt.
        - destruct ap as [ltD|ltD].
          + left; apply ltrx_locates_right; exact ltD.
          + right.
            assert (lt' : f (' r) - t < ' (- ' n)).
            { rewrite (preserves_negate (f:=cast Q F)).
              apply flip_lt_negate_r; rewrite <- (negate_swap_r t (f (' r))); exact ltD. }
            exact (ltxq_locates_left Q F _ _ lt').
      Qed.

      Local Lemma merely_rationalfar (ltxy : x < y) : hexists RationalFar.
      Proof.
        assert (h := merely_rational_apart x y t ltxy); strip_truncations.
        destruct h as [r [[xr ry] ap]].
        set (D := match ap with inl _ => f (' r) - t | inr _ => t - f (' r) end).
        assert (Dpos : 0 < D).
        { unfold D; destruct ap as [l|l]; exact (snd (flip_pos_minus _ _) l). }
        assert (lt0 : 0 < meet (meet (' r - x) (y - ' r)) D).
        { apply meet_lt_l; [apply meet_lt_l|exact Dpos];
            apply (snd (flip_pos_minus _ _)); assumption. }
        refine (Trunc_functor (-1) _ (merely_qpos_lt Q _ lt0)); intros [n ltn].
        exists (r, n).
        assert (lt1 := lt_le_trans _ _ _ ltn (meet_lb_l _ _)).
        assert (ltD := lt_le_trans _ _ _ ltn (meet_lb_r _ _)).
        apply rationalfar_lt.
        - exact (lt_le_trans _ _ _ lt1 (meet_lb_l _ _)).
        - exact (lt_le_trans _ _ _ lt1 (meet_lb_r _ _)).
        - unfold D in ltD; destruct ap; [left|right]; exact ltD.
      Qed.

      (** A rational satisfying [RationalFar] is as required. *)
      Local Lemma rationalfar_spec (r : Q) (n : Qpos Q) (far : RationalFar (r, n))
        : (x < ' r < y) * (f (' r) ≶ t).
      Proof.
        destruct far as [[pl pr] pt].
        split; [split|].
        - exact (locates_right_false Q F _ lx _ _ _ pl).
        - exact (locates_right_true Q F _ ly _ _ _ pr).
        - apply (snd (apart_iff_total_lt _ _)).
          destruct pt as [p|p].
          + right.
            assert (lt' := locates_right_true Q F _ (locator_value_minus r) _ _ _ p).
            apply (fst (flip_pos_minus _ _)).
            exact (transitivity (pos_rationals_to_field_qpos Q _) lt').
          + left.
            assert (lt' := locates_right_false Q F _ (locator_value_minus r) _ _ _ p).
            apply (fst (flip_neg_minus _ _)).
            assert (neg : (' (- ' (n / 2)) : F) < 0).
            { rewrite (preserves_negate (f:=cast Q F)).
              exact (fst (flip_pos_negate _) (pos_rationals_to_field_qpos Q _)). }
            exact (transitivity lt' neg).
      Defined.

      Definition locally_nonconstant_rational (ltxy : x < y)
        : {r : Q & ((x < ' r < y) * (f (' r) ≶ t))%type}.
      Proof.
        destruct (minimal_n_alt_type _ QQpos_eq RationalFar _ (merely_rationalfar ltxy))
          as [[r n] far].
        exact (r; rationalfar_spec r n far).
      Defined.
    End rational_apart.

    (** *** Finding a root *)

    (** If [g] is continuous at the limit [x] of [s] and positive at [x], then it is positive at some [s n]. *)
    Local Lemma pos_limit (g : F -> F) (x : F) (gcont : IsContinuousAt Q F g x)
      (s : nat -> F) (islim : IsLimit Q F s x) (pos : 0 < g x)
      : hexists (fun n => 0 < g (s n)).
    Proof.
      assert (d := iscontinuousat_lt Q F g x gcont 0 pos).
      strip_truncations; destruct d as [d above].
      refine (Trunc_functor (-1) _ (islim d)); intros [N sN]; exists N.
      exact (above _ (sN N (Nat.Core.leq_refl N))).
    Qed.

    Local Notation quarter := (' (1 / 2 / 2 : Qpos Q) : Q).

    Local Lemma quarter_double (u : F) : u * ' quarter + u * ' quarter = u * ' half.
    Proof.
      rewrite <- plus_mult_distr_l, <- (preserves_plus (f:=cast Q F)).
      change (quarter + quarter) with (' (1 / 2 / 2 + 1 / 2 / 2 : Qpos Q)).
      rewrite <- (pos_split2 (1 / 2)); reflexivity.
    Qed.

    Local Lemma quarter_lt_1 : quarter < 1.
    Proof.
      exact (transitivity (qpos_half_lt (1 / 2)) half_lt_1).
    Qed.

    (** The factor by which the width shrinks at each step. *)
    Local Definition shrink : Q := 1 - quarter.

    Local Lemma shrink_pos : 0 < shrink.
    Proof.
      exact (snd (flip_pos_minus _ _) quarter_lt_1).
    Qed.

    Local Lemma shrink_lt_1 : shrink < 1.
    Proof.
      exact (fst (pos_minus_lt_compat_r _ _) (pos_is_pos _)).
    Qed.

    Local Lemma minus_quarter (u : F) : u - u * ' quarter = u * ' shrink.
    Proof.
      unfold shrink.
      rewrite (preserves_minus (f:=cast Q F)), (preserves_1 (f:=cast Q F)).
      rewrite (plus_mult_distr_l u 1 (- ' quarter)), (mult_1_r u), <- (negate_mult_distr_r u (' quarter)); reflexivity.
    Qed.

    (** The points [u] and [v] a quarter of the way into an interval [[a, b]] satisfy [a < u < v < b], and [[a, v]] and [[u, b]] are shorter than [[a, b]] by the factor [shrink]. *)
    Section quarters.
      Context {a b : F} (ltab : a < b).

      Local Notation u := (a + (b - a) * ' quarter).
      Local Notation v := (b - (b - a) * ' quarter).

      Local Lemma quarter_width_pos : 0 < (b - a) * ' quarter.
      Proof.
        exact (pos_mult _ _ (snd (flip_pos_minus _ _) ltab) (pos_rationals_to_field_qpos Q _)).
      Qed.

      Local Lemma lt_lower_quarter : a < u.
      Proof.
        exact (fst (pos_plus_lt_compat_r _ _) quarter_width_pos).
      Qed.

      Local Lemma upper_quarter_lt : v < b.
      Proof.
        exact (fst (pos_minus_lt_compat_r _ _) quarter_width_pos).
      Qed.

      Local Lemma lt_quarters : u < v.
      Proof.
        pose proof (snd (flip_pos_minus _ _) ltab).
        set (D := b - a).
        apply (snd (flip_lt_minus_r _ _ _)).
        rewrite <- plus_assoc, quarter_double.
        assert (p : a + D = b).
        { unfold D; rewrite plus_comm, <- plus_assoc, (plus_negate_l a); apply plus_0_r. }
        rewrite <- p.
        apply (strictly_order_preserving (a +)).
        refine (lt_le_trans _ (D * 1) _ _ (eq_le _ _ (mult_1_r _))).
        apply (strictly_order_preserving (D *.)).
        rewrite <- (preserves_1 (f:=cast Q F)).
        exact (strictly_order_preserving _ _ _ half_lt_1).
      Qed.

      Local Lemma upper_minus_lower_quarter : b - u = (b - a) * ' shrink.
      Proof.
        rewrite negate_plus_distr, plus_assoc; apply minus_quarter.
      Qed.

      Local Lemma upper_quarter_minus_lower : v - a = (b - a) * ' shrink.
      Proof.
        rewrite <- plus_assoc, (plus_comm (- _)), plus_assoc; apply minus_quarter.
      Qed.
    End quarters.

    (** An interval with locators for its endpoints, at which [f] has opposite signs. *)
    Record SignInterval := {
      sign_lower : F;
      sign_upper : F;
      sign_lower_locator : locator Q F sign_lower;
      sign_upper_locator : locator Q F sign_upper;
      sign_lt : sign_lower < sign_upper;
      sign_lower_nonpos : f sign_lower ≤ 0;
      sign_upper_nonneg : 0 ≤ f sign_upper
    }.

    (** A step: we find a rational [r] in the middle half of the interval with [f r] apart from [0], and replace one endpoint by [r]. *)
    Definition sign_interval_step (I : SignInterval)
      : {J : SignInterval & prod (prod (sign_lower I ≤ sign_lower J) (sign_upper J ≤ sign_upper I))
           (sign_upper J - sign_lower J ≤ (sign_upper I - sign_lower I) * ' shrink)}.
    Proof.
      destruct I as [a b la lb ltab fa fb]; cbn.
      (* A locator for a quarter of the width, and hence for the quarter points. *)
      set (lD := locator_times Q F (locator_plus Q F lb (locator_minus Q F la))
                   (locator_left Q F quarter)).
      destruct (locally_nonconstant_rational (locator_plus Q F la lD)
                  (locator_plus Q F lb (locator_minus Q F lD)) locator_0 (lt_quarters ltab))
        as [r [[ur rv] ap]].
      destruct (fst (apart_iff_total_lt _ _) ap) as [neg|pos].
      - (* The root is to the right of [r]. *)
        refine (Build_SignInterval (' r) b (locator_left Q F r) lb
                  (transitivity rv (upper_quarter_lt ltab)) (lt_le _ _ neg) fb;
                ((lt_le _ _ (transitivity (lt_lower_quarter ltab) ur), reflexivity _), _)).
        cbn; rewrite <- upper_minus_lower_quarter.
        apply lt_le, (strictly_order_preserving (b +)), (snd (flip_lt_negate _ _)), ur.
      - (* The root is to the left of [r]. *)
        refine (Build_SignInterval a (' r) la (locator_left Q F r)
                  (transitivity (lt_lower_quarter ltab) ur) fa (lt_le _ _ pos);
                ((reflexivity _, lt_le _ _ (transitivity rv (upper_quarter_lt ltab))), _)).
        cbn; rewrite <- upper_quarter_minus_lower.
        apply lt_le, (strictly_order_preserving (+ - a)), rv.
    Defined.

    (** Repeating the step from an interval [I0] gives nested intervals, whose lower endpoints converge to a root. *)
    Section exact.
      Context {Fcomplete : IsComplete Q F} (I0 : SignInterval).

      Definition sign_intervals (n : nat) : SignInterval
        := nat_iter n (fun I => (sign_interval_step I).1) I0.

      Local Notation z n := (sign_lower (sign_intervals n)).
      Local Notation w n := (sign_upper (sign_intervals n)).

      Local Definition step_props n := (sign_interval_step (sign_intervals n)).2.

      Local Definition sign_width_bound
        : {B : Qpos Q & sign_upper I0 - sign_lower I0 < ' (' B)}
        := qpos_upper_bound Q F (locator_plus Q F (sign_upper_locator I0)
                                   (locator_minus Q F (sign_lower_locator I0))).

      Local Notation B := sign_width_bound.1.

      Local Lemma sign_width (n : nat)
        : w n - z n ≤ ' (' B * nat_iter n (mult shrink) 1).
      Proof.
        induction n as [|n IH].
        - rewrite mult_1_r; exact (lt_le _ _ sign_width_bound.2).
        - lhs' exact (snd (step_props n)).
          assert (r0 : (0 : F) ≤ ' shrink).
          { rewrite <- (preserves_0 (f:=cast Q F)).
            exact (order_preserving _ _ _ (lt_le _ _ shrink_pos)). }
          lhs' exact (order_preserving (.* ' shrink) _ _ IH).
          apply eq_le.
          rewrite <- (preserves_mult (f:=cast Q F)); apply ap.
          change (nat_iter (S n) (mult shrink) 1) with (shrink * nat_iter n (mult shrink) 1).
          rewrite <- mult_assoc, (mult_comm _ shrink); reflexivity.
      Qed.

      Local Definition sign_zinc n : z n ≤ z (S n) := fst (fst (step_props n)).
      Local Definition sign_wdec n : w (S n) ≤ w n := snd (fst (step_props n)).
      Local Definition sign_zw n : z n ≤ w n := lt_le _ _ (sign_lt (sign_intervals n)).

      #[local] Instance cauchymodulus_sign_lower
        : CauchyModulus Q F (fun n => z n) (nested_modulus B shrink shrink_pos shrink_lt_1)
        := cauchymodulus_nested (fun n => z n) (fun n => w n) sign_zinc sign_wdec B shrink shrink_pos
             shrink_lt_1 sign_width (fun n => z n) (fun n => (reflexivity _, sign_zw n)).

      (** The root is the limit of the lower endpoints. *)
      Definition sign_root_islimit : {x : F & IsLimit Q F (fun n => z n) x}
        := is_complete Q F _ _ cauchymodulus_sign_lower.

      Definition sign_root_spec
        : (locator Q F sign_root_islimit.1
           * (sign_lower I0 ≤ sign_root_islimit.1 ≤ sign_upper I0)
           * (f sign_root_islimit.1 = 0))%type.
      Proof.
        destruct sign_root_islimit as [x islim]; cbn.
        assert (zxw := nested_limit_between (fun n => z n) (fun n => w n) sign_zinc sign_wdec sign_zw x islim).
        assert (wlim : IsLimit Q F (fun n => w n) x).
        { exact (islimit_nested (fun n => z n) (fun n => w n) B shrink shrink_pos shrink_lt_1
                   sign_width (fun n => w n) (fun n => (sign_zw n, reflexivity _)) x zxw). }
        refine ((_, zxw 0%nat), _).
        - exact (locator_limit Q F (fun n => sign_lower_locator _) islim).
        - apply (antisymmetry (≤)); apply not_lt_le_flip; intro lt.
          + assert (h := pos_limit f x (cont x) _ islim lt); strip_truncations.
            destruct h as [n pos].
            exact (irreflexivity (<) 0 (lt_le_trans _ _ _ pos (sign_lower_nonpos _))).
          + assert (h := pos_limit (fun y => - f y) x (iscontinuousat_negate Q F f x (cont x))
                           _ wlim (fst (flip_neg_negate _) lt)).
            strip_truncations; destruct h as [n pos].
            apply (snd (flip_neg_negate _)) in pos.
            exact (irreflexivity (<) 0 (le_lt_trans _ _ _ (sign_upper_nonneg _) pos)).
      Defined.

    End exact.

    (** The exact intermediate value theorem: if [f] is pointwise continuous, locally nonconstant and lifts to locators, and [f a ≤ 0 ≤ f b] for [a < b] with locators, then we can find a root of [f] in [[a, b]], with a locator. *)
    Definition exact_ivt `{!IsComplete Q F} (a b : F) (la : locator Q F a) (lb : locator Q F b)
      (ltab : a < b) (fa : f a ≤ 0) (fb : 0 ≤ f b)
      : {x : F & (locator Q F x * (a ≤ x ≤ b) * (f x = 0))%type}
      := let I0 := Build_SignInterval a b la lb ltab fa fb in
         ((sign_root_islimit I0).1; sign_root_spec I0).

  End search.

End ivt.
