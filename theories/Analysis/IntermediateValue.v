(** * Intermediate value theorems *)

(** We prove an approximate intermediate value theorem for pointwise continuous functions, following M. Frank, _Interpolating between choices for the approximate intermediate value theorem_ (LMCS 2020): instead of choosing the left or the right half of the interval at each step of the bisection, the next interval interpolates continuously between the two, so that no choice is needed to define the bisection. A function which takes a negative and a positive value merely takes values arbitrarily close to [0], and if it lifts to locators and the endpoints have locators, then we can find such a point, with a locator.

Note that the point is not always the limit of the bisection: interpolation can move an endpoint to a point where [f] was never evaluated. The proof shows that either the limit or one of the midpoints works. *)

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
From HoTT.Analysis Require Import Locator CauchyCompleteness BanachFixedPoint LiftsToLocators.

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

  (** Two elements of an interval of width less than [e] are [e]-close. *)
  Lemma field_close_interval (e : Qpos Q) (a b u v : F) (au : a ≤ u ≤ b) (av : a ≤ v ≤ b)
    (lt : b - a < ' (' e))
    : field_close Q e u v.
  Proof.
    split.
    - apply flip_lt_negate_l.
      rewrite <- negate_swap_r.
      refine (le_lt_trans _ _ _ _ lt).
      apply plus_le_compat; [exact (snd av)|].
      exact (snd (flip_le_negate _ _) (fst au)).
    - refine (le_lt_trans _ _ _ _ lt).
      apply plus_le_compat; [exact (snd au)|].
      exact (snd (flip_le_negate _ _) (fst av)).
  Qed.

  (** Bounds on the tail of a sequence are bounds on its limit. *)
  Lemma le_limit (y : nat -> F) (l c : F) (N : nat) (islim : IsLimit Q F y l)
    (le : forall n, (N <= n)%nat -> c ≤ y n)
    : c ≤ l.
  Proof.
    apply not_lt_le_flip; intro ltlc.
    assert (q := archimedean_property Q F 0 (c - l) (snd (flip_pos_minus _ _) ltlc)).
    strip_truncations; destruct q as [q [lt0q ltqc]].
    assert (qpos : 0 < q).
    { apply (strictly_order_reflecting (cast Q F)).
      rewrite (preserves_0 (f:=cast Q F)); exact lt0q. }
    assert (c' := islim (mkQpos q qpos)); strip_truncations; destruct c' as [M close].
    set (n := Nat.Core.nat_max N M).
    assert (lt := fst (close n (le_nat_max_r N M))).
    change (- ' q < l - y n) in lt.
    apply (irreflexivity (<) c).
    refine (le_lt_trans _ _ _ (le n (le_nat_max_l N M)) _).
    apply (fst (flip_lt_minus_r _ _ _)) in lt, ltqc.
    rewrite plus_comm in lt, ltqc.
    exact (transitivity (fst (flip_lt_minus_l _ _ _) lt) ltqc).
  Qed.

  Lemma limit_le (y : nat -> F) (l c : F) (N : nat) (islim : IsLimit Q F y l)
    (le : forall n, (N <= n)%nat -> y n ≤ c)
    : l ≤ c.
  Proof.
    apply not_lt_le_flip; intro ltcl.
    assert (q := archimedean_property Q F 0 (l - c) (snd (flip_pos_minus _ _) ltcl)).
    strip_truncations; destruct q as [q [lt0q ltqc]].
    assert (qpos : 0 < q).
    { apply (strictly_order_reflecting (cast Q F)).
      rewrite (preserves_0 (f:=cast Q F)); exact lt0q. }
    assert (c' := islim (mkQpos q qpos)); strip_truncations; destruct c' as [M close].
    set (n := Nat.Core.nat_max N M).
    assert (lt := snd (close n (le_nat_max_r N M))).
    change (l - y n < ' q) in lt.
    apply (irreflexivity (<) c).
    refine (lt_le_trans _ _ _ _ (le n (le_nat_max_l N M))).
    apply flip_lt_minus_l in lt.
    apply flip_lt_minus_r in ltqc.
    rewrite (plus_comm (' q)) in lt.
    apply (strictly_order_reflecting (+ ' q)).
    rewrite (plus_comm c); exact (transitivity ltqc lt).
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
      apply (strictly_order_preserving _).
      refine (le_lt_trans _ (' B * power r (nested_modulus e)) _ _ _).
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
      apply (field_close_interval e (z M) (w M)).
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
      exact (field_close_interval e (z n) (w n) l (y n) (zlw n) (zyw n)
               (nested_width_lt e n len)).
    Qed.

  End nested.

  (** ** The approximate intermediate value theorem *)

  (** The image of a positive rational is positive. *)
  Lemma qpos_pos_F (e : Qpos Q) : (0 : F) < ' (' e).
  Proof.
    rewrite <- (preserves_0 (f:=cast Q F)).
    exact (strictly_order_preserving _ _ _ (pos_is_pos e)).
  Qed.

  (** The heart of the proof. Suppose that [p] and [c] converge to [x], that [g] is continuous at [x], that [g] is negative at [p 0], and that [p] stays put after a step at which [g (c n)] is above [t], and jumps to [c n] after a step at which [g (c n)] is below [- t]. If [g x] is above [t], then [g] is less than [e] in absolute value at some [c n]. *)
  Section endpoint.
    Context (g : F -> F) (p c : nat -> F) (x : F) (t e : Qpos Q) (ltte : ' t < ' e)
      (p0 : g (p 0) < 0)
      (stay : forall n, ' (' t) < g (c n) -> p (S n) = p n)
      (jump : forall n, g (c n) < - ' (' t) -> p (S n) = c n)
      (plim : IsLimit Q F p x) (clim : IsLimit Q F c x) (gcont : IsContinuousAt Q F g x).

    Local Lemma endpoint_back (k : nat) (lt : ' (' t) < g (p k))
      : hexists (fun n => - ' (' e) < g (c n) < ' (' e)).
    Proof.
      assert (tpos := qpos_pos_F t).
      revert lt; induction k as [|k IH]; intro lt.
      - destruct (lt_antisym _ _ (p0, transitivity tpos lt)).
      - assert (ltte' : (' (' t) : F) < ' (' e))
          by exact (strictly_order_preserving _ _ _ ltte).
        assert (h := cotransitive ltte' (g (c k))); strip_truncations.
        destruct h as [ltt|lte].
        + apply IH; rewrite <- (stay k ltt); exact lt.
        + assert (ltte'' := snd (flip_lt_negate _ _) ltte').
          assert (h := cotransitive ltte'' (g (c k))); strip_truncations.
          destruct h as [lte'|ltt].
          * exact (tr (k; (lte', lte))).
          * rewrite (jump k ltt) in lt.
            destruct (lt_antisym _ _ (lt, transitivity ltt
                        (transitivity (fst (flip_pos_negate _) tpos) tpos))).
    Qed.

    Lemma endpoint_close (lt : ' (' t) < g x)
      : hexists (fun n => - ' (' e) < g (c n) < ' (' e)).
    Proof.
      (* Points close to [x] have values above [t]. *)
      assert (q := archimedean_property Q F 0 (g x - ' (' t)) (snd (flip_pos_minus _ _) lt)).
      strip_truncations; destruct q as [q [lt0q ltq]].
      assert (qpos : 0 < q).
      { apply (strictly_order_reflecting (cast Q F)).
        rewrite (preserves_0 (f:=cast Q F)); exact lt0q. }
      assert (d := gcont (mkQpos q qpos)); strip_truncations; destruct d as [d close].
      assert (above : forall y, field_close Q d x y -> ' (' t) < g y).
      { intros y cxy.
        assert (lt' := snd (close y cxy)); change (g x - g y < ' q) in lt'.
        apply (fst (flip_lt_minus_r _ _ _)) in ltq.
        apply (fst (flip_lt_minus_l _ _ _)) in lt'.
        apply (strictly_order_reflecting (' q +)).
        exact (transitivity ltq lt'). }
      (* Eventually [c n] is close to [x], so [p] is eventually constant, with value [x]. *)
      assert (N := clim d); strip_truncations; destruct N as [N cN].
      assert (const : forall n, (N <= n)%nat -> p n = p N).
      { intros n len; induction len as [|n len IH].
        - reflexivity.
        - exact (stay n (above (c n) (cN n len)) @ IH). }
      assert (px : x = p N).
      { apply (field_close_eq Q); intro e'.
        assert (M := plim e'); strip_truncations; destruct M as [M pM].
        rewrite <- (const (Nat.Core.nat_max N M) (le_nat_max_l N M)).
        exact (pM _ (le_nat_max_r N M)). }
      rewrite px in lt.
      exact (endpoint_back N lt).
    Qed.
  End endpoint.

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

  Lemma qpos_half_lt (e : Qpos Q) : ' (e / 2) < ' e.
  Proof.
    rewrite (ap (cast (Qpos Q) Q) (pos_split2 e)).
    exact (fst (pos_plus_lt_compat_r _ _) (pos_is_pos _)).
  Qed.

  Definition half_lt_1 : half < 1 := qpos_half_lt 1.

  Lemma half_pos : (0 : F) < ' half.
  Proof.
    exact (qpos_pos_F (1 / 2)).
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
      refine (transitivity (order_preserving (.* h) _ _ le1) _).
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
      pose proof (lt_le _ _ (qpos_pos_F (/ (t + t)))).
      rewrite <- weight_factor.
      apply (order_preserving (.* _)).
      change (' (' t + ' t) ≤ f y + ' (' t)).
      rewrite (preserves_plus (f:=cast Q F)).
      exact (order_preserving (+ _) _ _ (lt_le _ _ lt)).
    Qed.

    Lemma bisect_weight_0 (y : F) (lt : f y < - ' (' t)) : bisect_weight f t y = 0.
    Proof.
      apply clamp_0.
      pose proof (lt_le _ _ (qpos_pos_F (/ (t + t)))).
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
      assert (qpos : 0 < q).
      { apply (strictly_order_reflecting (cast Q F)).
        rewrite (preserves_0 (f:=cast Q F)).
        exact (le_lt_trans _ _ _ (snd (flip_nonneg_minus _ _) leab) ltq). }
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

    (** The approximate intermediate value theorem: [f] is less than [e] in absolute value at one of the candidates. *)
    Lemma approximate_ivt_candidates
      (cont : forall y, a ≤ y ≤ b -> IsContinuousAt Q F f y)
      : hexists (fun n => - ' (' e) < f (approximate_candidate n) < ' (' e)).
    Proof.
      assert (B := merely_bound); strip_truncations; destruct B as [B leB].
      set (x := approximate_root).
      assert (zlim : IsLimit Q F z x) by exact approximate_root_islimit.2.
      assert (zxw := nested_limit_between z w zinc wdec zw x zlim).
      assert (wlim : IsLimit Q F w x).
      { exact (islimit_nested z w B half (pos_is_pos _) half_lt_1
                 (bisect_width_le dec a b B leB) w (fun n => (zw n, reflexivity _)) x zxw). }
      assert (clim : IsLimit Q F c x).
      { exact (islimit_nested z w B half (pos_is_pos _) half_lt_1
                 (bisect_width_le dec a b B leB) c
                 (bisect_mid_between dec (bisect_weight_between f _) a b leab) x zxw). }
      assert (cont' := cont x (zxw 0)).
      assert (ltte := qpos_half_lt e).
      assert (ltte' : (' (' (e / 2)) : F) < ' (' e))
        by exact (strictly_order_preserving _ _ _ ltte).
      assert (h := cotransitive ltte' (f x)); strip_truncations; destruct h as [ltt|lte].
      - (* If [f x] is above [e / 2], the lower endpoints stop moving. *)
        refine (Trunc_functor (-1)
                  (fun nc : {n : nat & - ' (' e) < f (c n) < ' (' e)} => (S nc.1; nc.2)) _).
        refine (endpoint_close f z c x (e / 2) e ltte fa _ _ zlim clim cont' ltt).
        + intros n lt; exact (bisect_lower_1 dec a b n (bisect_weight_1 f _ _ lt)).
        + intros n lt; exact (bisect_lower_0 dec a b n (bisect_weight_0 f _ _ lt)).
      - assert (h := cotransitive (snd (flip_lt_negate _ _) ltte') (f x)); strip_truncations.
        destruct h as [lte'|ltt].
        + exact (tr (0%nat; (lte', lte))).
        + (* If [f x] is below [- e / 2], the upper endpoints stop moving. *)
          refine (Trunc_functor (-1)
                    (fun nc : {n : nat & - ' (' e) < - f (c n) < ' (' e)} => (S nc.1; _)) _).
          { assert (bd := lt_bound_negate _ _ nc.2); cbn in bd.
            rewrite negate_involutive in bd; exact bd. }
          refine (endpoint_close (fun y => - f y) w c x (e / 2) e ltte
                    (fst (flip_pos_negate _) fb) _ _ wlim clim
                    (iscontinuousat_negate Q F f x cont') (flip_lt_negate_r _ _ ltt)).
          * intros n lt.
            exact (bisect_upper_0 dec a b n (bisect_weight_0 f _ _ (flip_lt_negate_r _ _ lt))).
          * intros n lt.
            apply (snd (flip_lt_negate _ _)) in lt; rewrite 2!negate_involutive in lt.
            exact (bisect_upper_1 dec a b n (bisect_weight_1 f _ _ lt)).
    Qed.

    (** Hence [f] merely takes values arbitrarily close to [0]. *)
    Definition approximate_ivt (cont : forall y, a ≤ y ≤ b -> IsContinuousAt Q F f y)
      : hexists (fun y => - ' (' e) < f y < ' (' e))
      := Trunc_functor (-1) (fun nc : {n : nat & - ' (' e) < f (approximate_candidate n) < ' (' e)}
                               => (approximate_candidate nc.1; nc.2))
           (approximate_ivt_candidates cont).

    (** *** Locators *)

    Context (Q_eq : nat <~> Q) (lift : LiftsToLocators Q F f)
      (la : locator Q F a) (lb : locator Q F b).

    Local Notation plus := (locator_plus Q F Q_eq).
    Local Notation times := (locator_times Q F Q_eq).
    Local Notation minus := (locator_minus Q F).
    Local Notation rat := (locator_left Q F).

    Local Definition locator_0 : locator Q F 0
      := transport (locator Q F) (preserves_0 (f:=cast Q F)) (rat 0).

    Local Definition locator_1 : locator Q F 1
      := transport (locator Q F) (preserves_1 (f:=cast Q F)) (rat 1).

    (** If the endpoints of an interval have locators, then so do the midpoint and the endpoints of the next interval. *)
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

    (** A rational bound on the width of the interval. *)
    Local Definition width_bound : {B : Qpos Q & b - a ≤ ' (' B)}.
    Proof.
      destruct (upper_bound Q F Q_eq (plus lb (minus la))) as [B ltB].
      assert (Bpos : 0 < B).
      { apply (strictly_order_reflecting (cast Q F)).
        rewrite (preserves_0 (f:=cast Q F)).
        exact (le_lt_trans _ _ _ (snd (flip_nonneg_minus _ _) leab) ltB). }
      exact (mkQpos B Bpos; lt_le _ _ ltB).
    Defined.

    (** The limit of the bisection has a locator, as a limit of midpoints with locators. *)
    Definition approximate_root_locator : locator Q F approximate_root.
    Proof.
      destruct width_bound as [B leB].
      assert (zxw := nested_limit_between z w zinc wdec zw _ approximate_root_islimit.2).
      refine (locator_limit Q F (xs:=c) (M:=nested_modulus B half (pos_is_pos _) half_lt_1)
                bisect_mid_locator _).
      - exact (cauchymodulus_nested z w zinc wdec B half (pos_is_pos _) half_lt_1
                 (bisect_width_le dec a b B leB) c
                 (bisect_mid_between dec (bisect_weight_between f _) a b leab)).
      - exact (islimit_nested z w B half (pos_is_pos _) half_lt_1
                 (bisect_width_le dec a b B leB) c
                 (bisect_mid_between dec (bisect_weight_between f _) a b leab) _ zxw).
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
    (Q_eq : nat <~> Q) (lift : LiftsToLocators Q F f) (la : locator Q F a) (lb : locator Q F b)
    : {y : F & (locator Q F y * (- ' (' e) < f y < ' (' e)))%type}.
  Proof.
    set (y := approximate_candidate f a b leab (e / 2)).
    set (ly := approximate_candidate_locator f a b leab (e / 2) Q_eq lift la lb).
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

End ivt.
