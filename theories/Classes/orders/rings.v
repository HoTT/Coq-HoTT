Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.orders
  HoTT.Classes.theory.groups
  HoTT.Classes.theory.rings.
Require Export
  HoTT.Classes.orders.semirings.

Generalizable Variables R Rle Rlt R1le R1lt.

Section from_ring_order.
  Context `{IsCRing R} `{!PartialOrder Rle}
    (plus_spec : forall z, OrderPreserving (z +))
    (mult_spec : forall x y, PropHolds (0 ≤ x) -> PropHolds (0 ≤ y) ->
      PropHolds (0 ≤ x * y)).

  Lemma from_ring_order: SemiRingOrder (≤).
  Proof.
  repeat (split; try exact _).
  - intros x y E. exists (- x + y).
    rewrite simple_associativity, plus_negate_r, plus_0_l.
    reflexivity.
  - intros x y E.
    rewrite <-(plus_0_l x), <-(plus_0_l y), <-!(plus_negate_l z),
      <-!simple_associativity.
    apply (order_preserving _). trivial.
  Qed.
End from_ring_order.

Section from_strict_ring_order.
  Context `{IsCRing R} `{!StrictOrder Rlt}
    (plus_spec : forall z, StrictlyOrderPreserving (z +))
    (mult_spec : forall x y, PropHolds (0 < x) -> PropHolds (0 < y) ->
      PropHolds (0 < x * y)).

  Lemma from_strict_ring_order: StrictSemiRingOrder (<).
  Proof.
  repeat (split; try exact _).
  - intros x y E. exists (- x + y).
    rewrite simple_associativity, plus_negate_r, plus_0_l.
    reflexivity.
  - intros x y E.
    rewrite <-(plus_0_l x), <-(plus_0_l y), <-!(plus_negate_l z),
      <-!simple_associativity.
    apply (strictly_order_preserving _). trivial.
  Qed.
End from_strict_ring_order.

Section from_pseudo_ring_order.
  Context `{IsCRing R} `{Apart R} `{!PseudoOrder Rlt}
    (plus_spec : forall z, StrictlyOrderPreserving (z +))
    (mult_ext : StrongBinaryExtensionality (.*.))
    (mult_spec : forall x y, PropHolds (0 < x) -> PropHolds (0 < y) ->
      PropHolds (0 < x * y)).

  Lemma from_pseudo_ring_order: PseudoSemiRingOrder (<).
  Proof.
  repeat (split; try exact _).
  - intros x y E. exists (- x + y).
    rewrite simple_associativity, plus_negate_r, plus_0_l.
    reflexivity.
  - intros x y E.
    rewrite <-(plus_0_l x), <-(plus_0_l y), <-!(plus_negate_l z),
      <-!simple_associativity.
    apply (strictly_order_preserving _).
    trivial.
  Qed.
End from_pseudo_ring_order.

Section from_full_pseudo_ring_order.
  Context `{IsCRing R} `{Apart R} `{!FullPseudoOrder Rle Rlt}
    (plus_spec : forall z, StrictlyOrderPreserving (z +))
    (mult_ext : StrongBinaryExtensionality (.*.))
    (mult_spec : forall x y, PropHolds (0 < x) -> PropHolds (0 < y) ->
      PropHolds (0 < x * y)).

  Lemma from_full_pseudo_ring_order: FullPseudoSemiRingOrder (≤) (<).
  Proof.
  split.
  - exact _.
  - apply from_pseudo_ring_order;trivial.
  - exact le_iff_not_lt_flip;trivial.
  Qed.
End from_full_pseudo_ring_order.

Section ring_order.
  Context `{IsCRing R} `{!SemiRingOrder Rle}.
(*   Add Ring R : (stdlib_ring_theory R). *)

  Lemma flip_le_negate x y : -y ≤ -x <-> x ≤ y.
  Proof.
  assert (forall a b, a ≤ b -> -b ≤ -a).
  - intros a b E.
    transitivity (-a + -b + a);[apply eq_le|
    transitivity (-a + -b + b);[|apply eq_le]].
    + rewrite plus_comm, plus_assoc, plus_negate_r, plus_0_l.
      reflexivity.
    + apply (order_preserving _). trivial.
    + rewrite <-plus_assoc, plus_negate_l. apply plus_0_r.
  - split; intros; auto.
    rewrite <-(negate_involutive x), <-(negate_involutive y); auto.
  Qed.

  Lemma flip_nonneg_negate x : 0 ≤ x <-> -x ≤ 0.
  Proof.
  split; intros E.
  - rewrite <-negate_0. apply flip_le_negate.
    rewrite !involutive. trivial.
  - apply flip_le_negate. rewrite negate_0. trivial.
  Qed.

  Lemma flip_nonpos_negate x : x ≤ 0 <-> 0 ≤ -x.
  Proof.
  pattern x at 1;apply (transport _ (negate_involutive x)).
  split; intros; apply flip_nonneg_negate;trivial.
  Qed.

  Lemma flip_le_minus_r (x y z : R) : z ≤ y - x <-> z + x ≤ y.
  Proof.
  split; intros E.
  - rewrite plus_comm.
    rewrite (plus_conjugate_alt y x).
    apply (order_preserving _). trivial.
  - rewrite plus_comm.
    rewrite (plus_conjugate_alt z (- x)), involutive.
    apply (order_preserving _). trivial.
  Qed.

  Lemma flip_le_minus_l (x y z : R) : y - x ≤ z <-> y ≤ z + x.
  Proof.
  pattern x at 2;apply (transport _ (negate_involutive x)).
  split; apply flip_le_minus_r.
  Qed.

  Lemma flip_nonneg_minus (x y : R) : 0 ≤ y - x <-> x ≤ y.
  Proof.
  pattern x at 2;apply (transport _ (plus_0_l x)).
  apply flip_le_minus_r.
  Qed.

  Lemma flip_nonpos_minus (x y : R) : y - x ≤ 0 <-> y ≤ x.
  Proof.
  pattern x at 2;apply (transport _ (plus_0_l x)).
  apply flip_le_minus_l.
  Qed.

  Lemma nonneg_minus_compat (x y z : R) : 0 ≤ z -> x ≤ y -> x - z ≤ y.
  Proof.
  intros E1 E2.
  rewrite plus_comm, (plus_conjugate_alt y (- z)), involutive.
  apply (order_preserving (-(z) +)).
  transitivity y; trivial.
  pattern y at 1;apply (transport _ (plus_0_r y)).
  apply (order_preserving (y +)). trivial.
  Qed.

  Lemma nonneg_minus_compat_back (x y z : R) : 0 ≤ z -> x ≤ y - z -> x ≤ y.
  Proof.
  intros E1 E2.
  transitivity (y - z); trivial.
  apply nonneg_minus_compat;trivial. apply reflexivity.
  Qed.

  Lemma between_nonneg (x : R) : 0 ≤ x -> -x ≤ x.
  Proof.
  intros.
  transitivity 0; trivial.
  apply flip_nonneg_negate. trivial.
  Qed.

  (** Two elements of an interval [[a, b]] differ by at most [b - a]. *)
  Lemma interval_minus_le (a b s t : R) : a ≤ s ≤ b -> a ≤ t ≤ b -> s - t ≤ b - a.
  Proof.
    intros [_ lesb] [leat _].
    apply plus_le_compat; [exact lesb|exact (snd (flip_le_negate _ _) leat)].
  Qed.
End ring_order.

Section strict_ring_order.
  Context `{IsCRing R} `{!StrictSemiRingOrder Rlt}.
(*   Add Ring Rs : (stdlib_ring_theory R). *)

  Lemma flip_lt_negate x y : -y < -x <-> x < y.
  Proof.
  assert (forall a b, a < b -> -b < -a).
  - intros a b E.
    rewrite (plus_conjugate (-b) (-a)), involutive.
    apply lt_eq_trans with (-a + -b + b).
    + apply (strictly_order_preserving _). trivial.
    + rewrite <-plus_assoc,plus_negate_l, plus_0_r. reflexivity.
  - split; intros; auto.
    rewrite <-(negate_involutive x), <-(negate_involutive y); auto.
  Qed.

  Lemma flip_lt_negate_r x y : y < - x -> x < - y.
  Proof.
    pattern y at 1. rewrite <- (@involutive _ (-) _ y).
    apply flip_lt_negate.
  Qed.
  Lemma flip_lt_negate_l x y : - x < y -> - y < x.
  Proof.
    pattern y at 1. rewrite <- (@involutive _ (-) _ y).
    apply flip_lt_negate.
  Qed.
  Lemma flip_pos_negate x : 0 < x <-> -x < 0.
  Proof.
  split; intros E.
  - rewrite <- negate_0. apply flip_lt_negate. rewrite !involutive;trivial.
  - apply flip_lt_negate. rewrite negate_0. trivial.
  Qed.

  Lemma flip_neg_negate x : x < 0 <-> 0 < -x.
  Proof.
  pattern x at 1;apply (transport _ (negate_involutive x)).
  split; intros; apply flip_pos_negate;trivial.
  Qed.

  Lemma flip_lt_minus_r (x y z : R) : z < y - x <-> z + x < y.
  Proof.
  split; intros E.
  - rewrite plus_comm, (plus_conjugate_alt y x).
    apply (strictly_order_preserving _). trivial.
  - rewrite plus_comm, (plus_conjugate_alt z (-x)), involutive.
    apply (strictly_order_preserving _). trivial.
  Qed.

  Lemma flip_lt_minus_l (x y z : R) : y - x < z <-> y < z + x.
  Proof.
  pattern x at 2;apply (transport _ (negate_involutive x)).
  split; apply flip_lt_minus_r.
  Qed.

  Lemma flip_pos_minus (x y : R) : 0 < y - x <-> x < y.
  Proof.
  pattern x at 2;apply (transport _ (plus_0_l x)).
  apply flip_lt_minus_r.
  Qed.

  Lemma flip_neg_minus (x y : R) : y - x < 0 <-> y < x.
  Proof.
  pattern x at 2;apply (transport _ (plus_0_l x)).
  apply flip_lt_minus_l.
  Qed.

  Lemma pos_minus_compat (x y z : R) : 0 < z -> x < y -> x - z < y.
  Proof.
  intros E1 E2.
  rewrite plus_comm, (plus_conjugate_alt y (-z)), involutive.
  apply (strictly_order_preserving (-(z) +)).
  transitivity y; trivial.
  pattern y at 1;apply (transport _ (plus_0_r y)).
  apply (strictly_order_preserving (y +)).
  trivial.
  Qed.

  Lemma pos_minus_lt_compat_r x z : 0 < z <-> x - z < x.
  Proof.
    pattern x at 2;apply (transport _ (plus_0_r x)).
    split; intros.
    - apply (strictly_order_preserving _), flip_pos_negate; assumption.
    - apply flip_pos_negate, (strictly_order_reflecting (x+)); assumption.
  Qed.

  Lemma pos_minus_lt_compat_l x z : 0 < z <-> - z + x < x.
  Proof.
    split; intros ltz.
    - rewrite (commutativity (-z) x); apply pos_minus_lt_compat_r; assumption.
    - rewrite (commutativity (-z) x) in ltz.
      apply (snd (pos_minus_lt_compat_r x z)); assumption.
  Qed.

  Lemma between_pos (x : R) : 0 < x -> -x < x.
  Proof.
  intros E.
  transitivity 0; trivial.
  apply flip_pos_negate. trivial.
  Qed.

  (** A bound [- x < z < x] can be weakened to a larger [y]. *)
  Lemma between_weaken (x y z : R) : - x < z < x -> x < y -> - y < z < y.
  Proof.
    intros [ltxz ltzx] ltxy; split.
    - exact (transitivity (snd (flip_lt_negate _ _) ltxy) ltxz).
    - exact (transitivity ltzx ltxy).
  Qed.

End strict_ring_order.

Section strict_ring_apart.
  Context `{FullPseudoSemiRingOrder R}.

  Definition positive_apart_zero (z : R) (Pz : 0 < z) : z ≶ 0
    := pseudo_order_lt_apart_flip 0 z Pz.
  Definition negative_apart_zero (z : R) (Nz : z < 0) : z ≶ 0
    := pseudo_order_lt_apart z 0 Nz.

End strict_ring_apart.

Section full_pseudo_ring_order.
  Context `{IsCRing R} `{Apart R} `{!FullPseudoSemiRingOrder Rle Rlt}.

  (** An element strictly between [- y] and [y] shows that [y] is positive. *)
  Lemma pos_between_negate x y : - y < x < y -> 0 < y.
  Proof.
    intros [ltyx ltxy].
    assert (c := cotransitive (transitivity ltyx ltxy) 0).
    strip_truncations; destruct c as [ltny0|lt0y].
    - apply flip_pos_negate; assumption.
    - assumption.
  Qed.

  (** Two elements of an interval of width less than [d] are less than [d] apart. *)
  Lemma interval_minus_lt (a b s t d : R)
    : a ≤ s ≤ b -> a ≤ t ≤ b -> b - a < d -> - d < s - t < d.
  Proof.
    intros sab tab lt; split.
    - apply flip_lt_negate_l; rewrite <- negate_swap_r.
      exact (le_lt_trans _ _ _ (interval_minus_le a b t s tab sab) lt).
    - exact (le_lt_trans _ _ _ (interval_minus_le a b s t sab tab) lt).
  Qed.

  (** If [|s| < S] and [|t| < T], then [|s * t| < S * T]. *)
  Lemma mult_lt_bound s t S T
    : - S < s < S -> - T < t < T -> - (S * T) < s * t < S * T.
  Proof.
    assert (upper : forall s t, - S < s < S -> - T < t < T -> s * t < S * T).
    { clear s t.
      intros s t [ltSs ltsS] [ltTt lttT].
      assert (Spos := pos_between_negate s S (ltSs, ltsS)).
      assert (Tpos := pos_between_negate t T (ltTt, lttT)).
      assert (c := cotransitive (pos_mult S T Spos Tpos) (s * t)).
      strip_truncations; destruct c as [ltst|]; [|assumption].
      destruct (pos_mult_decompose s t ltst) as [[spos tpos]|[sneg tneg]].
      - apply mult_lt_compat; assumption.
      - rewrite <- negate_mult_negate.
        apply mult_lt_compat.
        + apply flip_neg_negate; assumption.
        + apply flip_neg_negate; assumption.
        + exact (flip_lt_negate_l S s ltSs).
        + exact (flip_lt_negate_l T t ltTt). }
    intros [ltSs ltsS] ltTtT; split.
    - apply flip_lt_negate_l.
      rewrite negate_mult_distr_l.
      apply upper; [split|exact ltTtT].
      + exact (snd (flip_lt_negate s S) ltsS).
      + exact (flip_lt_negate_l S s ltSs).
    - apply upper; [split|]; assumption.
  Qed.

  (** The difference of two products, for estimating it. *)
  Lemma mult_minus_mult x y u w
    : x * y - u * w = x * (y - w) + (x - u) * w.
  Proof.
    rewrite plus_mult_distr_l, plus_mult_distr_r.
    rewrite <- negate_mult_distr_r, <- negate_mult_distr_l.
    rewrite <- (plus_assoc (x * y) (- (x * w)) (x * w + - (u * w))).
    rewrite (plus_assoc (- (x * w)) (x * w) (- (u * w))).
    rewrite plus_negate_l, plus_0_l.
    reflexivity.
  Qed.

  (** If [|x| < X], [|w| < W], [|x - u| < D] and [|y - w| < D], then [|x * y - u * w| < X * D + D * W]. *)
  Lemma mult_minus_mult_lt_bound x y u w X W D
    : - X < x < X -> - W < w < W -> - D < x - u < D -> - D < y - w < D
      -> - (X * D + D * W) < x * y - u * w < X * D + D * W.
  Proof.
    intros ltx ltw ltxu ltyw.
    destruct (mult_lt_bound x (y - w) X D ltx ltyw) as [lt1 lt1'].
    destruct (mult_lt_bound (x - u) w D W ltxu ltw) as [lt2 lt2'].
    rewrite mult_minus_mult, negate_plus_distr.
    split; apply plus_lt_compat; assumption.
  Qed.

  (** Multiplication by [v] is monotone on [[a, b]], so [u * v] cannot lie strictly below both [a * v] and [b * v]. *)
  Lemma not_lt_mult_endpoints a b u v
    : a ≤ u -> u ≤ b -> u * v < a * v -> u * v < b * v -> Empty.
  Proof.
    intros leau leub ltua ltub.
    assert (ltua' := snd (flip_neg_minus (a * v) (u * v)) ltua).
    assert (ltub' := snd (flip_pos_minus (u * v) (b * v)) ltub).
    rewrite negate_mult_distr_l, <- plus_mult_distr_r in ltua', ltub'.
    destruct (neg_mult_decompose _ _ ltua') as [[ltua'' _]|[_ vneg]].
    - exact (fst (le_iff_not_lt_flip _ _) (snd (flip_nonneg_minus a u) leau) ltua'').
    - destruct (pos_mult_decompose _ _ ltub') as [[_ vpos]|[ltub'' _]].
      + exact (irreflexivity _ _ (transitivity vneg vpos)).
      + exact (fst (le_iff_not_lt_flip _ _) (snd (flip_nonneg_minus u b) leub) ltub'').
  Qed.

  (** Hence a strict bound on [a * v] and [b * v] is a strict bound on [u * v]. *)
  Lemma lt_mult_endpoints_l q a b u v
    : a ≤ u -> u ≤ b -> q < a * v -> q < b * v -> q < u * v.
  Proof.
    intros leau leub ltqa ltqb.
    assert (c := cotransitive ltqa (u * v)).
    strip_truncations; destruct c as [|ltua]; [assumption|].
    assert (c := cotransitive ltqb (u * v)).
    strip_truncations; destruct c as [|ltub]; [assumption|].
    destruct (not_lt_mult_endpoints a b u v leau leub ltua ltub).
  Qed.

  Lemma mult_endpoints_lt_r r a b u v
    : a ≤ u -> u ≤ b -> a * v < r -> b * v < r -> u * v < r.
  Proof.
    intros leau leub ltar ltbr.
    assert (c := cotransitive ltar (u * v)).
    strip_truncations; destruct c as [ltau|]; [|assumption].
    assert (c := cotransitive ltbr (u * v)).
    strip_truncations; destruct c as [ltbu|]; [|assumption].
    destruct (not_lt_mult_endpoints a b u (- v) leau leub);
      rewrite <- 2!negate_mult_distr_r; apply (snd (flip_lt_negate _ _)); assumption.
  Qed.

  (** Hence a bound on the four products of the endpoints of [[a, b]] and [[c, d]] is a bound on [u * w] for [u] in [[a, b]] and [w] in [[c, d]]. *)
  Lemma lt_mult_corners_l q a b c d u w
    : a ≤ u -> u ≤ b -> c ≤ w -> w ≤ d
      -> q < a * c -> q < a * d -> q < b * c -> q < b * d -> q < u * w.
  Proof.
    intros leau leub lecw lewd ltac ltad ltbc ltbd.
    rewrite (mult_comm u w).
    apply (lt_mult_endpoints_l q c d w u lecw lewd); rewrite (mult_comm _ u);
      apply (lt_mult_endpoints_l q a b u _ leau leub); assumption.
  Qed.

  Lemma mult_corners_lt_r r a b c d u w
    : a ≤ u -> u ≤ b -> c ≤ w -> w ≤ d
      -> a * c < r -> a * d < r -> b * c < r -> b * d < r -> u * w < r.
  Proof.
    intros leau leub lecw lewd ltac ltad ltbc ltbd.
    rewrite (mult_comm u w).
    apply (mult_endpoints_lt_r r c d w u lecw lewd); rewrite (mult_comm _ u);
      apply (mult_endpoints_lt_r r a b u _ leau leub); assumption.
  Qed.

End full_pseudo_ring_order.

(** ** Absolute values *)

(** The order need not be total, so an element is only nonnegative or nonpositive up to double negation; this suffices for the inequalities and equalities below. *)
Section abs.
  Context `{IsCRing R} `{Apart R} `{!FullPseudoSemiRingOrder Rle Rlt} `{!Abs R}.
  Local Existing Instance pseudo_order_apart.

  (** Up to double negation, every element is nonnegative or nonpositive. *)
  Lemma nonneg_or_nonpos_not_not (x : R) : ~~ ((0 ≤ x) + (x ≤ 0)).
  Proof.
    intro n; apply n, inr, not_lt_le_flip.
    intro lt0x; exact (n (inl (lt_le _ _ lt0x))).
  Qed.

  (** Hence inequalities and equalities, which are stable under double negation, can be proved by cases on the sign of an element. *)
  Local Lemma le_by_sign (x a b : R)
    : (0 ≤ x -> a ≤ b) -> (x ≤ 0 -> a ≤ b) -> a ≤ b.
  Proof.
    intros nonneg nonpos; apply not_lt_le_flip; intro ltba.
    apply (nonneg_or_nonpos_not_not x); intros [c|c].
    - exact (le_not_lt_flip _ _ (nonneg c) ltba).
    - exact (le_not_lt_flip _ _ (nonpos c) ltba).
  Qed.

  Local Lemma eq_by_sign (x a b : R)
    : (0 ≤ x -> a = b) -> (x ≤ 0 -> a = b) -> a = b.
  Proof.
    intros nonneg nonpos; apply (fst (tight_apart a b)); intro apab.
    apply (nonneg_or_nonpos_not_not x); intros [c|c].
    - exact (snd (tight_apart a b) (nonneg c) apab).
    - exact (snd (tight_apart a b) (nonpos c) apab).
  Qed.

  Definition abs_of_nonneg (x : R) : 0 ≤ x -> abs x = x
    := fst (abs_sig x).2.

  Definition abs_of_nonpos (x : R) : x ≤ 0 -> abs x = - x
    := snd (abs_sig x).2.

  Lemma abs_nonneg (x : R) : 0 ≤ abs x.
  Proof.
    apply (le_by_sign x); intro c.
    - rewrite (abs_of_nonneg x c); exact c.
    - rewrite (abs_of_nonpos x c); exact (fst (flip_nonpos_negate x) c).
  Qed.

  Lemma abs_0 : abs 0 = 0 :> R.
  Proof.
    exact (abs_of_nonneg 0 (reflexivity 0)).
  Qed.

  Lemma abs_negate (x : R) : abs (- x) = abs x.
  Proof.
    apply (eq_by_sign x); intro c.
    - rewrite (abs_of_nonneg x c).
      rewrite (abs_of_nonpos (- x) (fst (flip_nonneg_negate x) c)).
      apply negate_involutive.
    - rewrite (abs_of_nonpos x c).
      exact (abs_of_nonneg (- x) (fst (flip_nonpos_negate x) c)).
  Qed.

  Lemma le_abs (x : R) : x ≤ abs x.
  Proof.
    apply (le_by_sign x); intro c.
    - rewrite (abs_of_nonneg x c); reflexivity.
    - rewrite (abs_of_nonpos x c).
      exact (transitivity c (fst (flip_nonpos_negate x) c)).
  Qed.

  Lemma negate_le_abs (x : R) : - x ≤ abs x.
  Proof.
    rewrite <- (abs_negate x); apply le_abs.
  Qed.

  Lemma abs_le (x y : R) : - y ≤ x -> x ≤ y -> abs x ≤ y.
  Proof.
    intros leyx lexy; apply (le_by_sign x); intro c.
    - rewrite (abs_of_nonneg x c); exact lexy.
    - rewrite (abs_of_nonpos x c); apply flip_le_negate.
      rewrite negate_involutive; exact leyx.
  Qed.

  (** Strict bounds are not stable under double negation, so we use cotransitivity instead. *)
  Lemma abs_lt (x y : R) : - y < x -> x < y -> abs x < y.
  Proof.
    intros ltyx ltxy.
    assert (c := cotransitive ltxy (abs x)); strip_truncations.
    destruct c as [lt|lt]; [|exact lt].
    assert (nonpos : x ≤ 0).
    { apply not_lt_le_flip; intro pos.
      rewrite (abs_of_nonneg x (lt_le _ _ pos)) in lt.
      exact (irreflexivity _ _ lt). }
    rewrite (abs_of_nonpos x nonpos).
    apply flip_lt_negate; rewrite negate_involutive; exact ltyx.
  Qed.

  Lemma abs_triangle (x y : R) : abs (x + y) ≤ abs x + abs y.
  Proof.
    apply abs_le.
    - rewrite negate_plus_distr.
      apply plus_le_compat; apply flip_le_negate; rewrite negate_involutive;
        apply negate_le_abs.
    - apply plus_le_compat; apply le_abs.
  Qed.

  Lemma abs_eq_0 (x : R) : abs x = 0 -> x = 0.
  Proof.
    intro p; apply (eq_by_sign x); intro c.
    - exact ((abs_of_nonneg x c)^ @ p).
    - rewrite <- (negate_involutive x), <- (abs_of_nonpos x c), p.
      apply negate_0.
  Qed.

  Lemma abs_minus_swap (x y : R) : abs (x - y) = abs (y - x).
  Proof.
    rewrite (negate_swap_r x y); apply abs_negate.
  Qed.

End abs.

Section another_ring_order.
  Context `{IsCRing R1} `{!SemiRingOrder R1le} `{IsCRing R2} `{R2le : Le R2}
    `{is_mere_relation R2 R2le}.

  Lemma projected_ring_order (f : R2 -> R1) `{!IsSemiRingPreserving f} `{!IsInjective f}
    : (forall x y, x ≤ y <-> f x ≤ f y) -> SemiRingOrder R2le.
  Proof.
  intros P. apply (projected_srorder f P).
  intros x y E. exists (-x + y).
  rewrite plus_assoc, plus_negate_r, plus_0_l. reflexivity.
  Qed.

  Context `{!SemiRingOrder R2le} {f : R1 -> R2} `{!IsSemiRingPreserving f}.

  Lemma reflecting_preserves_nonneg : (forall x, 0 ≤ f x -> 0 ≤ x) -> OrderReflecting f.
  Proof.
  intros E. repeat (split; try exact _). intros x y F.
  apply flip_nonneg_minus, E.
  rewrite preserves_plus, preserves_negate.
  apply (flip_nonneg_minus (f x)), F.
  Qed.

  Lemma preserves_ge_negate1 `{!OrderPreserving f} x : - 1 ≤ x -> - 1 ≤ f x.
  Proof.
  intros. rewrite <-(preserves_1 (f:=f)), <-preserves_negate.
  apply (order_preserving f). trivial.
  Qed.

  Lemma preserves_le_negate1 `{!OrderPreserving f} x : x ≤ - 1 -> f x ≤ - 1.
  Proof.
  intros. rewrite <-(preserves_1 (f:=f)), <-preserves_negate.
  apply (order_preserving f). trivial.
  Qed.
End another_ring_order.

Section another_strict_ring_order.
  Context `{IsCRing R1} `{!StrictSemiRingOrder R1lt} `{IsCRing R2} `{R2lt : Lt R2}
    `{is_mere_relation R2 lt}.

  Lemma projected_strict_ring_order (f : R2 -> R1) `{!IsSemiRingPreserving f} :
    (forall x y, x < y <-> f x < f y) -> StrictSemiRingOrder R2lt.
  Proof.
  intros P. pose proof (projected_strict_order f P).
  apply from_strict_ring_order.
  - intros z x y E.
    apply P. rewrite 2!(preserves_plus (f:=f)).
    apply (strictly_order_preserving _), P. trivial.
  - intros x y E1 E2.
    apply P. rewrite preserves_mult, preserves_0.
    apply pos_mult_compat; rewrite <-(preserves_0 (f:=f)); apply P; trivial.
  Qed.
End another_strict_ring_order.

Section another_pseudo_ring_order.
  Context `{IsCRing R1} `{Apart R1} `{!PseudoSemiRingOrder R1lt}
    `{IsCRing R2} `{IsApart R2} `{R2lt : Lt R2}
    `{is_mere_relation R2 lt}.

  Lemma projected_pseudo_ring_order (f : R2 -> R1) `{!IsSemiRingPreserving f}
    `{!IsStrongInjective f}
    : (forall x y, x < y <-> f x < f y) -> PseudoSemiRingOrder R2lt.
  Proof.
  intros P.
  pose proof (projected_pseudo_order f P).
  pose proof (projected_strict_ring_order f P).
  apply from_pseudo_ring_order; try exact _.
  pose proof (@pseudo_order_apart R1 H0 R1lt pseudo_srorder_strict : IsApart R1).
  pose proof (pseudo_order_apart : IsApart R2).
  pose proof (strong_injective_mor f).
  repeat (split; try exact _).
  intros x₁ y₁ x₂ y₂ E.
  apply (strong_injective f) in E. rewrite 2!(preserves_mult (f:=f)) in E.
  apply (merely_destruct (strong_binary_extensionality (.*.) _ _ _ _ E));
  intros [?|?];apply tr; [left | right];
  apply (strong_extensionality f); trivial.
  Qed.
End another_pseudo_ring_order.

Section another_full_pseudo_ring_order.
  Context `{IsCRing R1} `{Apart R1} `{!FullPseudoSemiRingOrder R1le R1lt}
    `{IsCRing R2} `{IsApart R2} `{R2le : Le R2} `{R2lt : Lt R2}
    `{is_mere_relation R2 le} `{is_mere_relation R2 lt}.

  Lemma projected_full_pseudo_ring_order (f : R2 -> R1) `{!IsSemiRingPreserving f}
    `{!IsStrongInjective f}
    : (forall x y, x ≤ y <-> f x ≤ f y) -> (forall x y, x < y <-> f x < f y) ->
    FullPseudoSemiRingOrder R2le R2lt.
  Proof.
  intros P1 P2. pose proof (projected_full_pseudo_order f P1 P2).
  pose proof (projected_pseudo_ring_order f P2).
  split; try exact _. exact le_iff_not_lt_flip.
  Qed.
End another_full_pseudo_ring_order.
