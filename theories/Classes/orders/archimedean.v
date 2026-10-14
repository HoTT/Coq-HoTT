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

  (** [-x < r] iff [-r < x]. *)
  Lemma char_minus_left x y : - x < y -> - y < x.
  Proof.
    intros ltnxy. rewrite <- (negate_involutive x). apply (snd (flip_lt_negate _ _)). assumption.
  Qed.

  (** [q < -x] iff [x < -q]. *)
  Lemma char_minus_right x y : x < - y -> y < - x.
  Proof.
    intros ltnxy. rewrite <- (negate_involutive y). apply (snd (flip_lt_negate _ _)). assumption.
  Qed.

  (** [q < x + y] iff there is [s : Q] with [s < x] and [q - s < y]. *)
  Lemma char_plus_left : forall (q : Q) (x y : F),
      ' q < x + y <-> hexists (fun s : Q => (' s < x) /\ (' (q - s) < y)).
  Proof.
    intros q x y; split.
    - intros ltqxy.
      assert (hs := archimedean_property Q F (' q - y) x (snd (flip_lt_minus_l _ _ _) ltqxy)).
      strip_truncations; destruct hs as [s [ltqys ltsx]].
      apply tr; exists s; split; [exact ltsx|].
      rewrite preserves_minus.
      apply flip_lt_minus_l; rewrite (commutativity y).
      apply flip_lt_minus_l; assumption.
    - intros hs; strip_truncations; destruct hs as [s [ltsx ltqsy]].
      rewrite preserves_minus in ltqsy.
      apply (transitivity (fst (flip_lt_minus_l _ _ _) ltqsy)).
      rewrite (commutativity x).
      apply (strictly_order_preserving (y +)); assumption.
  Qed.

  (** [x + y < r] iff there is [t : Q] with [x < t] and [y < r - t]. *)
  Lemma char_plus_right : forall (r : Q) (x y : F),
      x + y < ' r <-> hexists (fun t : Q => (x < ' t) /\ (y < ' (r - t))).
  Proof.
    intros r x y; split.
    - intros ltxyr.
      assert (ht := archimedean_property Q F x (' r - y) (snd (flip_lt_minus_r _ _ _) ltxyr)).
      strip_truncations; destruct ht as [t [ltxt lttry]].
      apply tr; exists t; split; [exact ltxt|].
      rewrite preserves_minus.
      apply flip_lt_minus_r; rewrite (commutativity y).
      apply flip_lt_minus_r; assumption.
    - intros ht; strip_truncations; destruct ht as [t [ltxt ltyrt]].
      rewrite preserves_minus in ltyrt.
      refine (transitivity _ (fst (flip_lt_minus_r _ _ _) ltyrt)).
      rewrite (commutativity y).
      apply (strictly_order_preserving (+ y)); assumption.
  Qed.

  (** For [0 < z], [q < z⁻¹] iff [q z < 1]. *)
  Lemma char_recip_pos_left : forall (q : Q) (z : F) (nu : 0 < z),
    'q < recip' z (positive_apart_zero z nu) <-> ' q * z < 1.
  Proof.
    intros q z nu.
    rewrite <- (recip_inverse' z (positive_apart_zero z nu)), (commutativity z).
    split.
    - apply (strictly_order_preserving (.* z)).
    - apply (strictly_order_reflecting (.* z)).
  Qed.

  (** For [0 < z], [z⁻¹ < r] iff [1 < r z]. *)
  Lemma char_recip_pos_right : forall (r : Q) (z : F) (nu : 0 < z),
    recip' z (positive_apart_zero z nu) < ' r <-> 1 < ' r * z.
  Proof.
    intros r z nu.
    rewrite <- (recip_inverse' z (positive_apart_zero z nu)), (commutativity z).
    split.
    - apply (strictly_order_preserving (.* z)).
    - apply (strictly_order_reflecting (.* z)).
  Qed.

  (** For [w < 0], [q < w⁻¹] iff [1 < q w]. *)
  Lemma char_recip_neg_left : forall (q : Q) (w : F) (nu : w < 0),
    'q < recip' w (negative_apart_zero w nu) <-> 1 < ' q * w.
  Proof.
    intros q w nu.
    set (w' := recip' w (negative_apart_zero w nu)).
    assert (ww' : w * w' = 1) by apply recip_inverse'.
    split.
    - intros ltqw'. rewrite <- ww', (commutativity w). exact (flip_neg_mult_r _ _ _ nu ltqw').
    - intros lt1qw.
      assert (w'neg : w' < 0) by apply neg_recip_compat.
      assert (lt := flip_neg_mult_r _ _ _ w'neg lt1qw).
      rewrite <- (associativity _ w w'), ww', mult_1_r, mult_1_l in lt.
      exact lt.
  Qed.

  (** For [w < 0], [w⁻¹ < r] iff [r w < 1]. *)
  Lemma char_recip_neg_right : forall (r : Q) (w : F) (nu : w < 0),
    recip' w (negative_apart_zero w nu) < ' r <-> ' r * w < 1.
  Proof.
    intros r w nu.
    set (w' := recip' w (negative_apart_zero w nu)).
    assert (ww' : w * w' = 1) by apply recip_inverse'.
    split.
    - intros ltw'r. rewrite <- ww', (commutativity w). exact (flip_neg_mult_r _ _ _ nu ltw'r).
    - intros ltrw1.
      assert (w'neg : w' < 0) by apply neg_recip_compat.
      assert (lt := flip_neg_mult_r _ _ _ w'neg ltrw1).
      rewrite <- (associativity _ w w'), ww', mult_1_r, mult_1_l in lt.
      exact lt.
  Qed.

  (** [q < min(x, y)] iff [q < x] and [q < y]. *)
  Lemma char_meet_left : forall (q : Q) (x y : F),
      ' q < meet x y <-> ' q < x /\ ' q < y.
  Proof.
    intros q x y; split.
    - intros ltqm; split; refine (lt_le_trans _ _ _ ltqm _).
      + apply meet_lb_l.
      + apply meet_lb_r.
    - intros [ltqx ltqy]; apply meet_lt_l; assumption.
  Qed.

  (** [min(x, y) < r] iff [x < r] or [y < r]. *)
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
      destruct (irreflexivity _ _ (meet_lt_l _ _ _ ltmx ltmy)).
    - intros h; strip_truncations; destruct h as [ltxr|ltyr].
      + apply meet_lt_r_l; assumption.
      + apply meet_lt_r_r; assumption.
  Qed.

  (** [q < max(x, y)] iff [q < x] or [q < y]. *)
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
      destruct (irreflexivity _ _ (join_lt_r _ _ _ ltxj ltyj)).
    - intros h; strip_truncations; destruct h as [ltqx|ltqy].
      + apply join_lt_l_l; assumption.
      + apply join_lt_l_r; assumption.
  Qed.

  (** [max(x, y) < r] iff [x < r] and [y < r]. *)
  Lemma char_join_right : forall (r : Q) (x y : F),
      join x y < ' r <-> x < ' r /\ y < ' r.
  Proof.
    intros r x y; split.
    - intros ltjr; split; refine (le_lt_trans _ _ _ _ ltjr).
      + apply join_ub_l.
      + apply join_ub_r.
    - intros [ltxr ltyr]; apply join_lt_r; assumption.
  Qed.

  Definition hexists4 {X Y Z W} (f : X -> Y -> Z -> W -> Type) : HProp
    := hexists (fun xyzw => match xyzw with
                            | ((x , y) , (z , w)) => f x y z w
                            end).

  (** If [max(x, -x, y, -y) < Z], then [x] and [y] lie strictly between [- Z] and [Z]. *)
  Lemma between_join_negate (x y Z : F) (lt : join (join x (- x)) (join y (- y)) < Z)
    : (- Z < x < Z) /\ (- Z < y < Z).
  Proof.
    assert (ltZ : forall v, v ≤ join (join x (- x)) (join y (- y)) -> v < Z)
      by (intros v lev; exact (le_lt_trans _ _ _ lev lt)).
    refine ((_, _), (_, _)).
    - apply flip_lt_negate_l, ltZ.
      exact (transitivity (join_ub_r x (- x)) (join_ub_l _ _)).
    - apply ltZ; exact (transitivity (join_ub_l x (- x)) (join_ub_l _ _)).
    - apply flip_lt_negate_l, ltZ.
      exact (transitivity (join_ub_r y (- y)) (join_ub_r _ _)).
    - apply ltZ; exact (transitivity (join_ub_l y (- y)) (join_ub_r _ _)).
  Qed.

  (** For [- Z < x < Z] and [0 < D], there are rationals [a < x < b] such that all [u] in [[a, b]] lie between [- Z] and [Z] and within [D] of [x]. *)
  Lemma merely_rational_bounds_close (x D Z : F) (Dpos : 0 < D) (ltZx : - Z < x < Z)
    : hexists (fun ab : Q * Q => (' (fst ab) < x < ' (snd ab))
                 /\ forall u, ' (fst ab) ≤ u -> u ≤ ' (snd ab)
                              -> (- Z < u < Z) /\ (- D < x - u < D)).
  Proof.
    destruct ltZx as [ltZx ltxZ].
    assert (ha := archimedean_property Q F _ x
                    (join_lt_r _ _ _ (fst (pos_minus_lt_compat_r x D) Dpos) ltZx)).
    assert (hb := archimedean_property Q F x _
                    (meet_lt_l _ _ _ (fst (pos_plus_lt_compat_r x D) Dpos) ltxZ)).
    strip_truncations; destruct ha as [a [ltja ltax]], hb as [b [ltxb ltbm]].
    apply tr; exists (a, b); refine ((ltax, ltxb), _); intros u leau leub.
    assert (ltu := fun v (lev : v ≤ join (x - D) (- Z)) =>
                     lt_le_trans _ _ _ (le_lt_trans _ _ _ lev ltja) leau).
    assert (ult := fun v (lev : meet (x + D) Z ≤ v) =>
                     le_lt_trans _ _ _ leub (lt_le_trans _ _ _ ltbm lev)).
    split; split.
    - exact (ltu _ (join_ub_r _ _)).
    - exact (ult _ (meet_lb_r _ _)).
    - apply flip_lt_minus_r; rewrite (commutativity (- D)).
      apply flip_lt_minus_l; exact (ult _ (meet_lb_l _ _)).
    - apply flip_lt_minus_l; rewrite (commutativity D).
      apply flip_lt_minus_l; exact (ltu _ (join_ub_l _ _)).
  Qed.

  Section times.
    (* Reflecting strict inequalities from [F] to [Q] needs [1] to be apart from [0] in [Q]; this holds for instance when the apartness of [Q] is trivial. *)
    Context `{!PropHolds ((1 : Q) ≶ 0)}.

    (** Rational bounds [a < x < b] and [c < y < d] such that [u * w] is within [e] of [x * y] for all [u] in [[a, b]] and [w] in [[c, d]]. *)
    Lemma archimedean_mult_approx (x y e : F) (epos : 0 < e)
      : hexists4 (fun a b c d : Q =>
                    (' a < x < ' b) /\ (' c < y < ' d)
                    /\ forall u w, ' a ≤ u -> u ≤ ' b -> ' c ≤ w -> w ≤ ' d
                                   -> x * y - e < u * w < x * y + e).
    Proof.
      (* By [mult_minus_mult_lt_bound], it suffices that [u] and [w] are within [D = e / 2Z] of [x] and [y], for a bound [Z] on [x] and [y]. *)
      set (Z := join (join x (- x)) (join y (- y)) + 1).
      destruct (between_join_negate x y Z (fst (pos_plus_lt_compat_r _ 1) lt_0_1))
        as [ltZx ltZy].
      assert (Zpos : 0 < Z + Z).
      { assert (Zpos := pos_between_negate x Z ltZx).
        apply pos_plus_compat; assumption. }
      set (D := e * recip' (Z + Z) (positive_apart_zero _ Zpos)).
      assert (Dpos : 0 < D) by exact (pos_mult _ _ epos (pos_recip_compat _ _)).
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
      destruct (mult_minus_mult_lt_bound x y u w Z Z D ltZx ltZw closeu closew) as [lo hi].
      rewrite ZDDZ in lo, hi.
      split.
      - apply flip_lt_minus_l; rewrite (commutativity (u * w)).
        apply flip_lt_minus_l; exact hi.
      - apply flip_lt_minus_l; rewrite <- (commutativity (- e)).
        apply flip_lt_minus_r; exact lo.
    Qed.

    (** [q < x y] iff there are [a < x < b] and [c < y < d] with [q < min(ac, ad, bc, bd)]. *)
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
                       (snd (flip_pos_minus _ _) ltqxy)).
        strip_truncations; destruct h as [[[a b] [c d]] [ltaxb [ltcyd approx]]].
        apply tr; exists ((a, b), (c, d)); refine (_, (ltaxb, ltcyd)).
        assert (corner : forall u w, ' a ≤ ' u -> ' u ≤ ' b -> ' c ≤ ' w -> ' w ≤ ' d
                                     -> q < u * w).
        { intros u w leau leub lecw lewd.
          apply (strictly_order_reflecting qinc).
          rewrite preserves_mult.
          assert (p : x * y - (x * y - ' q) = ' q).
          { rewrite negate_plus_distr, negate_involutive, plus_assoc,
              plus_negate_r, plus_0_l.
            reflexivity. }
          exact (transport (fun z => z < _) p (fst (approx _ _ leau leub lecw lewd))). }
        destruct ltaxb as [ltax ltxb], ltcyd as [ltcy ltyd].
        assert (leab := lt_le _ _ (transitivity ltax ltxb)).
        assert (lecd := lt_le _ _ (transitivity ltcy ltyd)).
        repeat apply meet_lt_l; apply corner; first [reflexivity | assumption].
      - intros h; strip_truncations.
        destruct h as [[[a b] [c d]] [ltqm [[ltax ltxb] [ltcy ltyd]]]].
        apply (lt_mult_corners_l _ (' a) (' b) (' c) (' d));
          try (apply lt_le; assumption);
          rewrite <- preserves_mult; apply (strictly_order_preserving qinc);
          refine (lt_le_trans _ _ _ ltqm _).
        + exact (transitivity (meet_lb_l _ _) (meet_lb_l _ _)).
        + exact (transitivity (meet_lb_l _ _) (meet_lb_r _ _)).
        + exact (transitivity (meet_lb_r _ _) (meet_lb_l _ _)).
        + exact (transitivity (meet_lb_r _ _) (meet_lb_r _ _)).
    Qed.

    (** [x y < r] iff there are [a < x < b] and [c < y < d] with [max(ac, ad, bc, bd) < r]. *)
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
                       (snd (flip_pos_minus _ _) ltxyr)).
        strip_truncations; destruct h as [[[a b] [c d]] [ltaxb [ltcyd approx]]].
        apply tr; exists ((a, b), (c, d)); refine (_, (ltaxb, ltcyd)).
        assert (corner : forall u w, ' a ≤ ' u -> ' u ≤ ' b -> ' c ≤ ' w -> ' w ≤ ' d
                                     -> u * w < r).
        { intros u w leau leub lecw lewd.
          apply (strictly_order_reflecting qinc).
          rewrite preserves_mult.
          assert (p : x * y + (' r - x * y) = ' r).
          { rewrite (commutativity (' r)), plus_assoc, plus_negate_r, plus_0_l.
            reflexivity. }
          exact (transport (fun z => _ < z) p (snd (approx _ _ leau leub lecw lewd))). }
        destruct ltaxb as [ltax ltxb], ltcyd as [ltcy ltyd].
        assert (leab := lt_le _ _ (transitivity ltax ltxb)).
        assert (lecd := lt_le _ _ (transitivity ltcy ltyd)).
        repeat apply join_lt_r; apply corner; first [reflexivity | assumption].
      - intros h; strip_truncations.
        destruct h as [[[a b] [c d]] [ltjr [[ltax ltxb] [ltcy ltyd]]]].
        apply (mult_corners_lt_r _ (' a) (' b) (' c) (' d));
          try (apply lt_le; assumption);
          rewrite <- preserves_mult; apply (strictly_order_preserving qinc);
          refine (le_lt_trans _ _ _ _ ltjr).
        + exact (transitivity (join_ub_l _ _) (join_ub_l _ _)).
        + exact (transitivity (join_ub_r _ _) (join_ub_l _ _)).
        + exact (transitivity (join_ub_l _ _) (join_ub_r _ _)).
        + exact (transitivity (join_ub_r _ _) (join_ub_r _ _)).
    Qed.

  End times.

End strict_field_order.
