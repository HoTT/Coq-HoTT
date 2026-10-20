Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.orders
  HoTT.Classes.interfaces.rationals
  HoTT.Classes.interfaces.archimedean
  HoTT.Classes.theory.rings
  HoTT.Classes.theory.fields
  HoTT.Classes.orders.maps
  HoTT.Classes.orders.rings
  HoTT.Classes.orders.fields
  HoTT.Classes.orders.lattices
  HoTT.Classes.orders.rationals.

Generalizable Variables Q F.

Section strict_field_order.
  Context `{Rationals Q}.
  Context {Qmeet} {Qjoin} `{@LatticeOrder Q (_ : Le Q) Qmeet Qjoin}.
  Context `{OrderedField F}.
  Context {archim : ArchimedeanProperty Q F}.

  Definition qinc : Cast Q F := rationals_to_field Q F.
  Existing Instance qinc.

  (** The [char_*] lemmas below characterize the algebraic operations in terms of the strict order and rationals. *)

  (** ** Negation *)

  (** [-x < r] iff [-r < x]. *)
  Lemma char_minus_left x y : - x < y -> - y < x.
  Proof.
    exact (flip_lt_negate_l x y).
  Qed.

  (** [q < -x] iff [x < -q]. *)
  Lemma char_minus_right x y : x < - y -> y < - x.
  Proof.
    exact (flip_lt_negate_r y x).
  Qed.

  (** ** Addition *)

  (** [q < x + y] iff there is [s : Q] with [s < x] and [q - s < y]. If [q < x + y], a rational [s] with [q - y < s < x] has [q - s < y]. Conversely, [q = s + (q - s) < x + y]. *)
  Lemma char_plus_left : forall (q : Q) (x y : F),
      ' q < x + y <-> hexists (fun s : Q => (' s < x) /\ (' (q - s) < y)).
  Proof.
    intros q x y; split.
    - intros ltqxy.
      assert (hs := archimedean_property Q F (' q - y) x (snd (flip_lt_minus_l y (' q) x) ltqxy)).
      strip_truncations; destruct hs as [s [ltqys ltsx]].
      apply tr; exists s; split; [exact ltsx|].
      rewrite preserves_minus; apply flip_lt_minus_swap_l, ltqys.
    - intros hs; strip_truncations; destruct hs as [s [ltsx ltqsy]].
      rewrite (plus_conjugate_alt q s), (preserves_plus s (q - s)).
      apply plus_lt_compat; [exact ltsx|exact ltqsy].
  Qed.

  (** [x + y < r] iff there is [t : Q] with [x < t] and [y < r - t]. If [x + y < r], a rational [t] with [x < t < r - y] has [y < r - t]. Conversely, [x + y < t + (r - t) = r]. *)
  Lemma char_plus_right : forall (r : Q) (x y : F),
      x + y < ' r <-> hexists (fun t : Q => (x < ' t) /\ (y < ' (r - t))).
  Proof.
    intros r x y; split.
    - intros ltxyr.
      assert (ht := archimedean_property Q F x (' r - y) (snd (flip_lt_minus_r y (' r) x) ltxyr)).
      strip_truncations; destruct ht as [t [ltxt lttry]].
      apply tr; exists t; split; [exact ltxt|].
      rewrite preserves_minus; apply flip_lt_minus_swap_r, lttry.
    - intros ht; strip_truncations; destruct ht as [t [ltxt ltyrt]].
      rewrite (plus_conjugate_alt r t), (preserves_plus t (r - t)).
      apply plus_lt_compat; [exact ltxt|exact ltyrt].
  Qed.

  (** ** Multiplication *)

  (** [hexists4 f] says that [f a b c d] merely holds for some [a], [b], [c] and [d]. *)
  Definition hexists4 {X Y Z W} (f : X -> Y -> Z -> W -> Type) : HProp
    := hexists (fun xyzw => match xyzw with
                            | ((x , y) , (z , w)) => f x y z w
                            end).

  (** If [max(x, -x, y, -y) < Z], then [x] and [y] lie strictly between [- Z] and [Z]. *)
  Lemma between_join_negate (x y Z : F) (lt : join (join x (- x)) (join y (- y)) < Z)
    : (- Z < x < Z) /\ (- Z < y < Z).
  Proof.
    assert (ltZ : forall v, v ≤ join (join x (- x)) (join y (- y)) -> v < Z)
      by (intros v lev; rapply le_lt_trans; [exact lev|exact lt]).
    refine ((_, _), (_, _)).
    - apply flip_lt_negate_l, ltZ.
      lhs' apply join_ub_r; apply join_ub_l.
    - apply ltZ; lhs' apply join_ub_l; apply join_ub_l.
    - apply flip_lt_negate_l, ltZ.
      lhs' apply join_ub_r; apply join_ub_r.
    - apply ltZ; lhs' apply join_ub_l; apply join_ub_r.
  Qed.

  Section times.
    (* Reflecting strict inequalities from [F] to [Q] needs [1] to be apart from [0] in [Q]; this holds for instance when the apartness of [Q] is trivial. *)
    Context `{!PropHolds ((1 : Q) ≶ 0)}.

    (** For [- Z < x < Z] and [0 < D], there are rationals [a < x < b] such that all [u] in [[a, b]] lie between [- Z] and [Z] and within [D] of [x]: we take [max(x - D, - Z) < a < x < b < min(x + D, Z)]. *)
    Local Lemma merely_rational_bounds_close (x D Z : F) (Dpos : 0 < D) (ltZx : - Z < x < Z)
      : hexists (fun ab : Q * Q => (' (fst ab) < x < ' (snd ab))
                   /\ forall u, ' (fst ab) ≤ u -> u ≤ ' (snd ab)
                                -> (- Z < u < Z) /\ (- D < x - u < D)).
    Proof.
      destruct ltZx as [ltZx ltxZ].
      assert (ha := archimedean_property Q F (join (x - D) (- Z)) x
                      (join_lt_r (x - D) (- Z) x (fst (pos_minus_lt_compat_r x D) Dpos) ltZx)).
      assert (hb := archimedean_property Q F x (meet (x + D) Z)
                      (meet_lt_l x (x + D) Z (fst (pos_plus_lt_compat_r x D) Dpos) ltxZ)).
      strip_truncations; destruct ha as [a [ltja ltax]], hb as [b [ltxb ltbm]].
      apply tr; exists (a, b); refine ((ltax, ltxb), _); intros u leau leub.
      (* Then [max(x - D, - Z) < u < min(x + D, Z)]. *)
      assert (ltju : join (x - D) (- Z) < u) by (rapply lt_le_trans; [exact ltja|exact leau]).
      assert (ltum : u < meet (x + D) Z) by (rapply le_lt_trans; [exact leub|exact ltbm]).
      split; [split|].
      - rapply le_lt_trans; [apply join_ub_r|exact ltju].
      - rapply lt_le_trans; [exact ltum|apply meet_lb_r].
      - apply between_minus_swap, between_iff_lt_minus; split.
        + rapply le_lt_trans; [apply join_ub_l|exact ltju].
        + rapply lt_le_trans; [exact ltum|apply meet_lb_l].
    Qed.

    (** Rational bounds [a < x < b] and [c < y < d] such that [u * w] is within [e] of [x * y] for all [u] in [[a, b]] and [w] in [[c, d]]. By [mult_minus_mult_lt_bound], it suffices that [u] and [w] lie between [- Z] and [Z] and within [D = e / 2 Z] of [x] and [y], for a bound [Z] on [x] and [y]; [merely_rational_bounds_close] gives such bounds. *)
    Local Lemma archimedean_mult_approx (x y e : F) (epos : 0 < e)
      : hexists4 (fun a b c d : Q =>
                    (' a < x < ' b) /\ (' c < y < ' d)
                    /\ forall u w, ' a ≤ u -> u ≤ ' b -> ' c ≤ w -> w ≤ ' d
                                   -> - e < x * y - u * w < e).
    Proof.
      set (Z := join (join x (- x)) (join y (- y)) + 1).
      assert (ltJZ : join (join x (- x)) (join y (- y)) < Z)
        by (apply pos_plus_lt_compat_r, lt_0_1).
      destruct (between_join_negate x y Z ltJZ) as [ltZx ltZy].
      assert (Zpos : 0 < Z + Z).
      { assert (Zpos := pos_between_negate x Z ltZx).
        apply pos_plus_compat; assumption. }
      set (D := e * recip' (Z + Z) (positive_apart_zero (Z + Z) Zpos)).
      assert (Dpos : 0 < D) by (apply pos_mult; [exact epos|apply pos_recip_compat]).
      assert (ZDDZ : Z * D + D * Z = e).
      { rewrite (commutativity D Z), <- plus_mult_distr_r.
        unfold D, recip'.
        rewrite (commutativity e), (associativity (Z + Z)), recip_inverse', mult_1_l.
        reflexivity. }
      assert (hx := merely_rational_bounds_close x D Z Dpos ltZx).
      assert (hy := merely_rational_bounds_close y D Z Dpos ltZy).
      strip_truncations; destruct hx as [[a b] [ltaxb boxx]], hy as [[c d] [ltcyd boxy]].
      apply tr; exists ((a, b), (c, d)); refine (ltaxb, (ltcyd, _)).
      intros u w leau leub lecw lewd.
      destruct (boxx u leau leub) as [_ closeu], (boxy w lecw lewd) as [ltZw closew].
      rewrite <- ZDDZ.
      exact (mult_minus_mult_lt_bound x y u w Z Z D ltZx ltZw closeu closew).
    Qed.

    (** A property of [u * w] for all [u] in [[a, b]] and [w] in [[c, d]] holds at the four corners. *)
    Local Lemma box_corners (P : F -> Type) (a b c d : Q) (x y : F)
      (ltaxb : ' a < x < ' b) (ltcyd : ' c < y < ' d)
      (box : forall u w, ' a ≤ u -> u ≤ ' b -> ' c ≤ w -> w ≤ ' d -> P (u * w))
      : P (' a * ' c) * P (' a * ' d) * P (' b * ' c) * P (' b * ' d).
    Proof.
      destruct ltaxb as [ltax ltxb], ltcyd as [ltcy ltyd].
      assert (leab : ' a ≤ ' b) by (apply lt_le, (transitivity ltax ltxb)).
      assert (lecd : ' c ≤ ' d) by (apply lt_le, (transitivity ltcy ltyd)).
      repeat split; apply box; first [reflexivity | assumption].
    Qed.

    (** A rational lies below the minimum of the four products [a c], [a d], [b c] and [b d] iff its image lies below the image of each. *)
    Local Lemma lt_meet_corners (q a b c d : Q)
      : q < meet (meet (a * c) (a * d)) (meet (b * c) (b * d))
        <-> (' q < ' a * ' c) * (' q < ' a * ' d) * (' q < ' b * ' c) * (' q < ' b * ' d).
    Proof.
      rewrite <- 4!(preserves_mult (f:=qinc)); split.
      - intros lt; repeat split; apply (strictly_order_preserving qinc);
          (rapply lt_le_trans; [exact lt|]).
        + lhs' apply meet_lb_l; apply meet_lb_l.
        + lhs' apply meet_lb_l; apply meet_lb_r.
        + lhs' apply meet_lb_r; apply meet_lb_l.
        + lhs' apply meet_lb_r; apply meet_lb_r.
      - intros [[[ac ad] bc] bd].
        repeat apply meet_lt_l; apply (strictly_order_reflecting qinc); assumption.
    Qed.

    (** Dually, a rational lies above the maximum of the four products iff its image lies above the image of each. *)
    Local Lemma join_corners_lt (r a b c d : Q)
      : join (join (a * c) (a * d)) (join (b * c) (b * d)) < r
        <-> (' a * ' c < ' r) * (' a * ' d < ' r) * (' b * ' c < ' r) * (' b * ' d < ' r).
    Proof.
      rewrite <- 4!(preserves_mult (f:=qinc)); split.
      - intros lt; repeat split; apply (strictly_order_preserving qinc);
          (rapply le_lt_trans; [|exact lt]).
        + rhs_V' apply join_ub_l; apply join_ub_l.
        + rhs_V' apply join_ub_l; apply join_ub_r.
        + rhs_V' apply join_ub_r; apply join_ub_l.
        + rhs_V' apply join_ub_r; apply join_ub_r.
      - intros [[[ac ad] bc] bd].
        repeat apply join_lt_r; apply (strictly_order_reflecting qinc); assumption.
    Qed.

    (** If [x * y - u * w < x * y - s], then [s < u * w]. *)
    Local Lemma lt_of_minus_lt_minus (x s t : F) : x - t < x - s -> s < t.
    Proof.
      intro lt; apply flip_lt_negate, (strictly_order_reflecting (x +)), lt.
    Qed.

    (** [q < x y] iff there are [a < x < b] and [c < y < d] with [q < min(ac, ad, bc, bd)]. If [q < x y], take boxes around [x] and [y] in which all products are within [x y - q] of [x y], hence above [q]; in particular the corners are. Conversely, [x y] lies above the minimum of the products of the corners. *)
    Lemma char_times_left : forall (q : Q) (x y : F),
            ' q < x * y
        <-> hexists4 (fun a b c d : Q =>
                        (q < meet (meet (a * c) (a * d)) (meet (b * c) (b * d)))
                        /\
                        ((' a < x < ' b)
                         /\
                         (' c < y < ' d)
                        )
                     ).
    Proof.
      intros q x y; split.
      - intros ltqxy.
        assert (h := archimedean_mult_approx x y (x * y - ' q)
                       (snd (flip_pos_minus (' q) (x * y)) ltqxy)).
        strip_truncations; destruct h as [[[a b] [c d]] [ltaxb [ltcyd approx]]].
        apply tr; exists ((a, b), (c, d)); refine (_, (ltaxb, ltcyd)).
        apply lt_meet_corners, (box_corners (fun z => ' q < z) a b c d x y ltaxb ltcyd).
        intros u w leau leub lecw lewd.
        apply (lt_of_minus_lt_minus (x * y)); exact (snd (approx u w leau leub lecw lewd)).
      - intros h; strip_truncations.
        destruct h as [[[a b] [c d]] [ltqm [[ltax ltxb] [ltcy ltyd]]]].
        destruct (fst (lt_meet_corners q a b c d) ltqm) as [[[ac ad] bc] bd].
        apply (lt_mult_corners_l (' q) (' a) (' b) (' c) (' d) x y);
          first [assumption | apply lt_le; assumption].
    Qed.

    (** [x y < r] iff there are [a < x < b] and [c < y < d] with [max(ac, ad, bc, bd) < r]. The argument is dual to that for [char_times_left]. *)
    Lemma char_times_right : forall (r : Q) (x y : F),
            x * y < ' r
        <-> hexists4 (fun a b c d : Q =>
                        (join (join (a * c) (a * d)) (join (b * c) (b * d)) < r)
                        /\
                        ((' a < x < ' b)
                         /\
                         (' c < y < ' d)
                        )
                     ).
    Proof.
      intros r x y; split.
      - intros ltxyr.
        assert (h := archimedean_mult_approx x y (' r - x * y)
                       (snd (flip_pos_minus (x * y) (' r)) ltxyr)).
        strip_truncations; destruct h as [[[a b] [c d]] [ltaxb [ltcyd approx]]].
        apply tr; exists ((a, b), (c, d)); refine (_, (ltaxb, ltcyd)).
        apply join_corners_lt, (box_corners (fun z => z < ' r) a b c d x y ltaxb ltcyd).
        intros u w leau leub lecw lewd.
        apply (lt_of_minus_lt_minus (x * y)); rewrite (negate_swap_r (x * y)).
        exact (fst (approx u w leau leub lecw lewd)).
      - intros h; strip_truncations.
        destruct h as [[[a b] [c d]] [ltjr [[ltax ltxb] [ltcy ltyd]]]].
        destruct (fst (join_corners_lt r a b c d) ltjr) as [[[ac ad] bc] bd].
        apply (mult_corners_lt_r (' r) (' a) (' b) (' c) (' d) x y);
          first [assumption | apply lt_le; assumption].
    Qed.

  End times.

  (** ** Reciprocals *)

  (** Multiplying by a positive element preserves and reflects the strict order, and multiplying by a negative element reverses it. *)
  Local Lemma lt_iff_mult_pos_r (z : F) (zpos : 0 < z) (a b : F) : a < b <-> a * z < b * z.
  Proof.
    split.
    - apply (strictly_order_preserving (.* z)).
    - apply (strictly_order_reflecting (.* z)).
  Qed.

  Local Lemma lt_iff_mult_neg_r (w : F) (wneg : w < 0) (a b : F) : a < b <-> b * w < a * w.
  Proof.
    apply (iff_compose (lt_iff_mult_pos_r (- w) (fst (flip_neg_negate w) wneg) a b)).
    rewrite <- 2!negate_mult_distr_r; apply flip_lt_negate.
  Qed.

  (** For [0 < z], [q < z⁻¹] iff [q z < 1]: multiply by [z]. *)
  Lemma char_recip_pos_left : forall (q : Q) (z : F) (nu : 0 < z),
    'q < recip' z (positive_apart_zero z nu) <-> ' q * z < 1.
  Proof.
    intros q z nu.
    rewrite <- (recip_inverse' z (positive_apart_zero z nu)), (commutativity z).
    apply lt_iff_mult_pos_r, nu.
  Qed.

  (** For [0 < z], [z⁻¹ < r] iff [1 < r z]. *)
  Lemma char_recip_pos_right : forall (r : Q) (z : F) (nu : 0 < z),
    recip' z (positive_apart_zero z nu) < ' r <-> 1 < ' r * z.
  Proof.
    intros r z nu.
    rewrite <- (recip_inverse' z (positive_apart_zero z nu)), (commutativity z).
    apply lt_iff_mult_pos_r, nu.
  Qed.

  (** For [w < 0], [q < w⁻¹] iff [1 < q w]: multiply by [w]. *)
  Lemma char_recip_neg_left : forall (q : Q) (w : F) (nu : w < 0),
    'q < recip' w (negative_apart_zero w nu) <-> 1 < ' q * w.
  Proof.
    intros q w nu.
    rewrite <- (recip_inverse' w (negative_apart_zero w nu)), (commutativity w).
    apply lt_iff_mult_neg_r, nu.
  Qed.

  (** For [w < 0], [w⁻¹ < r] iff [r w < 1]. *)
  Lemma char_recip_neg_right : forall (r : Q) (w : F) (nu : w < 0),
    recip' w (negative_apart_zero w nu) < ' r <-> ' r * w < 1.
  Proof.
    intros r w nu.
    rewrite <- (recip_inverse' w (negative_apart_zero w nu)), (commutativity w).
    apply lt_iff_mult_neg_r, nu.
  Qed.

  (** ** Meet and join *)

  (** [q < min(x, y)] iff [q < x] and [q < y]. *)
  Lemma char_meet_left : forall (q : Q) (x y : F),
      ' q < meet x y <-> ' q < x /\ ' q < y.
  Proof.
    intros q x y; split.
    - intros ltqm; split; (rapply lt_le_trans; [exact ltqm|]).
      + apply meet_lb_l.
      + apply meet_lb_r.
    - intros [ltqx ltqy]; apply meet_lt_l; assumption.
  Qed.

  (** [min(x, y) < r] iff [x < r] or [y < r]. If [min(x, y) < r], compare [x] and [y] with [min(x, y) < r]: if both lie above [min(x, y)], so does [min(x, y)]. *)
  Lemma char_meet_right : forall (r : Q) (x y : F),
      meet x y < 'r <-> hor (x < 'r) (y < 'r).
  Proof.
    intros r x y; split.
    - intros ltmr.
      assert (cx := cotransitive ltmr x).
      assert (cy := cotransitive ltmr y).
      strip_truncations.
      destruct cx as [ltmx|ltxr]; [|exact (tr (inl ltxr))].
      destruct cy as [ltmy|ltyr]; [|exact (tr (inr ltyr))].
      destruct (irreflexivity (<) (meet x y) (meet_lt_l (meet x y) x y ltmx ltmy)).
    - intros h; strip_truncations; destruct h as [ltxr|ltyr].
      + apply meet_lt_r_l; assumption.
      + apply meet_lt_r_r; assumption.
  Qed.

  (** [q < max(x, y)] iff [q < x] or [q < y]. If [q < max(x, y)], compare [x] and [y] with [q < max(x, y)]: if both lie below [max(x, y)], so does [max(x, y)]. *)
  Lemma char_join_left : forall (q : Q) (x y : F),
      ' q < join x y <-> hor ('q < x) ('q < y).
  Proof.
    intros q x y; split.
    - intros ltqj.
      assert (cx := cotransitive ltqj x).
      assert (cy := cotransitive ltqj y).
      strip_truncations.
      destruct cx as [ltqx|ltxj]; [exact (tr (inl ltqx))|].
      destruct cy as [ltqy|ltyj]; [exact (tr (inr ltqy))|].
      destruct (irreflexivity (<) (join x y) (join_lt_r x y (join x y) ltxj ltyj)).
    - intros h; strip_truncations; destruct h as [ltqx|ltqy].
      + apply join_lt_l_l; assumption.
      + apply join_lt_l_r; assumption.
  Qed.

  (** [max(x, y) < r] iff [x < r] and [y < r]. *)
  Lemma char_join_right : forall (r : Q) (x y : F),
      join x y < ' r <-> x < ' r /\ y < ' r.
  Proof.
    intros r x y; split.
    - intros ltjr; split; (rapply le_lt_trans; [|exact ltjr]).
      + apply join_ub_l.
      + apply join_ub_r.
    - intros [ltxr ltyr]; apply join_lt_r; assumption.
  Qed.

End strict_field_order.
