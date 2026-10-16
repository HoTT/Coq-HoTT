(** * Dedekind reals *)

(** The Dedekind reals over a model [Q] of the rationals: pairs of a lower and an upper cut, predicates on [Q] that are inhabited, rounded, transitive and located.  We show that they form a set, and construct their order, lattice and field structure. *)

From HoTT Require Import Basics Spaces.Nat.Core Types.Sigma Types.Forall Types.Sum Types.Universe
  Truncations.Core Universes.HProp Universes.TruncType.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.rationals
  theory.apartness
  theory.rings
  theory.dec_fields
  theory.rationals
  interfaces.naturals
  interfaces.round
  implementations.peano_naturals
  orders.naturals
  orders.orders
  orders.rings
  orders.dec_fields.

Section dedekind.
  Context `{Funext} `{Univalence}.
  Context (Q : Type) `{Rationals Q} `{!TrivialApart Q} `{DecidablePaths Q} `{!RoundUpStrict Q}.

  Local Notation nQ := (naturals_to_semiring nat Q).

  (** ** Dedekind cuts *)

  (** The properties of a pair of predicates that make it a Dedekind cut: both are inhabited and rounded, every element of the lower cut is below every element of the upper cut, and every pair [q < r] has [q] in the lower cut or [r] in the upper cut.  We write [q < x] for [lower_cut x q] and [x < r] for [upper_cut x r] in comments. *)
  Record IsDedekindCut (lower upper : Q -> HProp) := {
    cut_lower_inhabited : hexists lower ;
    cut_upper_inhabited : hexists upper ;
    cut_lower_rounded : forall q, lower q <-> hexists (fun q' => prod (q < q') (lower q')) ;
    cut_upper_rounded : forall r, upper r <-> hexists (fun r' => prod (r' < r) (upper r')) ;
    cut_transitive : forall q r, lower q -> upper r -> q < r ;
    cut_located : forall q r, q < r -> hor (lower q) (upper r) }.

  Arguments cut_lower_inhabited {lower upper} _.
  Arguments cut_upper_inhabited {lower upper} _.
  Arguments cut_lower_rounded {lower upper} _ _.
  Arguments cut_upper_rounded {lower upper} _ _.
  Arguments cut_transitive {lower upper} _ _ _ _ _.
  Arguments cut_located {lower upper} _ _ _ _.

  Definition issig_isdedekindcut (lower upper : Q -> HProp)
    : _ <~> IsDedekindCut lower upper := ltac:(issig).

  #[export] Instance ishprop_isdedekindcut (lower upper : Q -> HProp) : IsHProp (IsDedekindCut lower upper).
  Proof.
    exact (istrunc_equiv_istrunc _ (issig_isdedekindcut lower upper)).
  Qed.

  (** A Dedekind real is a pair of a lower and an upper cut, with a proof that they form a Dedekind cut. *)
  Record DedekindReals := {
    lower_cut : Q -> HProp ;
    upper_cut : Q -> HProp ;
    isdedekindcut : IsDedekindCut lower_cut upper_cut }.

  Local Notation R := DedekindReals.

  (** Basic properties of the cuts. *)
  Section cut_lemmas.
    Context (x : R).

    Definition lower_cut_rounded := cut_lower_rounded (isdedekindcut x).
    Definition upper_cut_rounded := cut_upper_rounded (isdedekindcut x).

    Lemma lower_cut_lt (q q' : Q) : q < q' -> lower_cut x q' -> lower_cut x q.
    Proof.
      intros l p; apply (snd (lower_cut_rounded q)), tr; exact (q'; (l, p)).
    Qed.

    Lemma upper_cut_lt (r r' : Q) : r' < r -> upper_cut x r' -> upper_cut x r.
    Proof.
      intros l p; apply (snd (upper_cut_rounded r)), tr; exact (r'; (l, p)).
    Qed.

    Lemma lower_cut_le (q q' : Q) : q <= q' -> lower_cut x q' -> lower_cut x q.
    Proof.
      intros l p; destruct (le_equiv_lt q q' l) as [e|l'].
      - rewrite e; exact p.
      - exact (lower_cut_lt q q' l' p).
    Qed.

    Lemma upper_cut_le (r r' : Q) : r' <= r -> upper_cut x r' -> upper_cut x r.
    Proof.
      intros l p; destruct (le_equiv_lt r' r l) as [e|l'].
      - rewrite <- e; exact p.
      - exact (upper_cut_lt r r' l' p).
    Qed.

    Lemma cut_disjoint (q : Q) : lower_cut x q -> upper_cut x q -> Empty.
    Proof.
      intros p p'; exact (irreflexivity (<) q (cut_transitive (isdedekindcut x) q q p p')).
    Qed.
  End cut_lemmas.

  (** ** Paths between Dedekind reals *)

  Definition path_dedekindreals_cuts (x y : R)
    : lower_cut x = lower_cut y -> upper_cut x = upper_cut y -> x = y.
  Proof.
    destruct x as [lx ux c], y as [ly uy c']; cbn.
    intros p q; destruct p, q; exact (ap (Build_DedekindReals lx ux) (path_ishprop c c')).
  Defined.

  (** The type of Dedekind reals is a set. *)
  #[export] Instance ishset_dedekindreals : IsHSet R.
  Proof.
    apply (istrunc_equiv_istrunc {lower : Q -> HProp & {upper : Q -> HProp & IsDedekindCut lower upper}}).
    - make_equiv.
    - exact _.
  Qed.

  (** A Dedekind real is determined by its lower cut, and also by its upper cut, so inclusions of both cuts suffice. *)
  Lemma lower_cut_incl_rev (x y : R)
    (ll : forall q, lower_cut x q -> lower_cut y q) (uu : forall r, upper_cut x r -> upper_cut y r)
    (q : Q) : lower_cut y q -> lower_cut x q.
  Proof.
    intros p; apply (lower_cut_rounded y q) in p; strip_truncations; destruct p as [q' [l p]].
    assert (c := cut_located (isdedekindcut x) q q' l); strip_truncations; destruct c as [c|c].
    - exact c.
    - destruct (cut_disjoint y q' p (uu q' c)).
  Qed.

  Lemma upper_cut_incl_rev (x y : R)
    (ll : forall q, lower_cut x q -> lower_cut y q) (uu : forall r, upper_cut x r -> upper_cut y r)
    (r : Q) : upper_cut y r -> upper_cut x r.
  Proof.
    intros p; apply (upper_cut_rounded y r) in p; strip_truncations; destruct p as [r' [l p]].
    assert (c := cut_located (isdedekindcut x) r' r l); strip_truncations; destruct c as [c|c].
    - destruct (cut_disjoint y r' (ll r' c) p).
    - exact c.
  Qed.

  Definition path_dedekindreals (x y : R)
    (ll : forall q, lower_cut x q -> lower_cut y q) (uu : forall r, upper_cut x r -> upper_cut y r)
    : x = y.
  Proof.
    apply path_dedekindreals_cuts; apply path_forall; intros q; apply path_iff_hprop.
    - apply ll.
    - apply (lower_cut_incl_rev x y ll uu).
    - apply uu.
    - apply (upper_cut_incl_rev x y ll uu).
  Defined.

  (** ** Approximation *)

  Local Lemma pos_quarter_double (e : Qpos Q) : ' (e / 2 / 2) + ' (e / 2 / 2) < ' e.
  Proof.
    change (' (e / 2 / 2 + e / 2 / 2) < ' e); rewrite <- pos_split2.
    apply (transport (fun z => ' (e / 2) < ' z) (pos_split2 e)^).
    apply pos_plus_lt_compat_r, is_pos.
  Qed.

  Local Lemma plus_minus_cancel_l (a b : Q) : (a + b) - a = b.
  Proof.
    rewrite (plus_comm a), <- plus_assoc, plus_negate_r; apply plus_0_r.
  Qed.

  (** A Dedekind cut has a lower and an upper bound arbitrarily close to each other: walk up from a lower bound in steps of [e / 4], using locatedness at each step. *)
  Lemma cut_approximate (x : R) (e : Qpos Q)
    : hexists (fun a => hexists (fun b => prod (prod (lower_cut x a) (upper_cut x b)) (b - a < ' e))).
  Proof.
    assert (a0 := cut_lower_inhabited (isdedekindcut x)).
    assert (b0 := cut_upper_inhabited (isdedekindcut x)).
    strip_truncations; destruct a0 as [a0 la0], b0 as [b0 ub0].
    set (d := e / 2 / 2).
    set (p k := a0 + nQ k * ' d).
    assert (step : forall k, hor (hexists (fun a => hexists (fun b =>
                      prod (prod (lower_cut x a) (upper_cut x b)) (b - a < ' e))))
                      (lower_cut x (p k))).
    { induction k as [|k IH].
      - apply tr, inr; unfold p; change (nQ 0%nat) with (0 : Q).
        rewrite mult_0_l, plus_0_r; exact la0.
      - strip_truncations; destruct IH as [close|lp]; [exact (tr (inl close))|].
        assert (c := cut_located (isdedekindcut x) (p k + ' d) (p k + ' d + ' d)
                       (fst (pos_plus_lt_compat_r _ _) (is_pos d))).
        strip_truncations; destruct c as [l|u].
        + apply tr, inr.
          assert (pS : p (S k) = p k + ' d).
          { unfold p; rewrite nat_to_semiring_succ, plus_mult_distr_r, mult_1_l.
            rewrite (plus_comm (' d)), plus_assoc; reflexivity. }
          rewrite pS; exact l.
        + apply tr, inl, tr; exists (p k); apply tr; exists (p k + ' d + ' d).
          refine ((lp, u), _).
          rewrite <- (plus_assoc (p k) (' d) (' d)), plus_minus_cancel_l.
          exact (pos_quarter_double e). }
    destruct (round_up_strict Q ((b0 - a0) / ' d)) as [N lN].
    assert (lN' : b0 - a0 < nQ N * ' d).
    { refine (transport (fun z => z < _) _ (pos_mult_lt_r (' d) _ _ _ lN)).
      rewrite <- mult_assoc, (mult_comm (/ _)), dec_recip_inverse.
      - apply mult_1_r.
      - apply lt_ne_flip, is_pos. }
    specialize (step N); strip_truncations; destruct step as [close|lp]; [exact close|].
    apply Empty_rec, (irreflexivity (<) (b0 - a0)).
    refine (transitivity lN' _).
    apply flip_lt_minus_r; rewrite plus_comm.
    exact (cut_transitive (isdedekindcut x) _ _ lp ub0).
  Qed.

  (** ** Rationals *)

  Local Definition Qlt_hprop (q r : Q) : HProp := Build_HProp (q < r).

  (** The rational [q] has the lower cut [s < q] and the upper cut [q < s]. *)
  Lemma isdedekindcut_rational (q : Q)
    : IsDedekindCut (fun s => Qlt_hprop s q) (fun s => Qlt_hprop q s).
  Proof.
    split; cbn.
    - apply tr; exists (q - 1); exact (fst (pos_minus_lt_compat_r q 1) lt_0_1).
    - apply tr; exists (q + 1); exact (fst (pos_plus_lt_compat_r q 1) lt_0_1).
    - intros s; split.
      + intros l; apply tr; destruct (Q_dense s q l) as [s' ls]; exact (s'; ls).
      + intros l; strip_truncations; destruct l as [s' [l1 l2]]; exact (transitivity l1 l2).
    - intros s; split.
      + intros l; apply tr; destruct (Q_dense q s l) as [s' [l1 l2]]; exact (s'; (l2, l1)).
      + intros l; strip_truncations; destruct l as [s' [l1 l2]]; exact (transitivity l2 l1).
    - intros s t l1 l2; exact (transitivity l1 l2).
    - intros s t l; exact (cotransitive l q).
  Qed.

  Definition rational_dedekind (q : Q) : R
    := Build_DedekindReals _ _ (isdedekindcut_rational q).

  (** ** Order *)

  (** [x < y] when a rational lies between them, and [x <= y] when the lower cut of [x] is contained in that of [y]. *)
  #[export] Instance lt_dedekindreals : Lt R
    := fun x y => hexists (fun q => prod (upper_cut x q) (lower_cut y q)).

  #[export] Instance le_dedekindreals : Le R
    := fun x y => forall q, lower_cut x q -> lower_cut y q.

  #[export] Instance apart_dedekindreals : Apart R
    := fun x y => hor (x < y) (y < x).

  #[export] Instance ishprop_lt_dedekindreals : is_mere_relation R lt := _.
  #[export] Instance ishprop_le_dedekindreals : is_mere_relation R le := _.
  #[export] Instance ishprop_apart_dedekindreals : is_mere_relation R apart := _.

  Lemma lt_rational_dedekind_l (q : Q) (x : R) : rational_dedekind q < x <-> lower_cut x q.
  Proof.
    split.
    - intros l; strip_truncations; destruct l as [s [l p]]; exact (lower_cut_lt x q s l p).
    - intros p; apply (lower_cut_rounded x q) in p; strip_truncations.
      destruct p as [s [l p]]; exact (tr (s; (l, p))).
  Qed.

  Lemma lt_rational_dedekind_r (r : Q) (x : R) : x < rational_dedekind r <-> upper_cut x r.
  Proof.
    split.
    - intros l; strip_truncations; destruct l as [s [p l]]; exact (upper_cut_lt x r s l p).
    - intros p; apply (upper_cut_rounded x r) in p; strip_truncations.
      destruct p as [s [l p]]; exact (tr (s; (p, l))).
  Qed.

  Lemma le_iff_not_lt_dedekindreals (x y : R) : x <= y <-> ~ (y < x).
  Proof.
    split.
    - intros l l'; strip_truncations; destruct l' as [q [u p]].
      exact (cut_disjoint y q (l q p) u).
    - intros nl q p.
      apply (lower_cut_rounded x q) in p; strip_truncations; destruct p as [q' [l p]].
      assert (c := cut_located (isdedekindcut y) q q' l); strip_truncations.
      destruct c as [c|c]; [exact c|].
      destruct (nl (tr (q'; (c, p)))).
  Qed.

  (** ** Addition *)

  Local Lemma minus_lt_minus (q q' s : Q) : q < q' -> q - s < q' - s.
  Proof.
    exact (strictly_order_preserving (+ (- s)) q q').
  Qed.

  Local Lemma minus_minus_cancel (q s : Q) : q - (q - s) = s.
  Proof.
    rewrite negate_plus_distr, negate_involutive, plus_assoc, plus_negate_r; apply plus_0_l.
  Qed.

  Local Lemma plus_minus_telescope (x y z : Q) : (y - x) + (x - z) = y - z.
  Proof.
    rewrite <- plus_assoc, (plus_assoc (- x)), plus_negate_l, plus_0_l.
    reflexivity.
  Qed.

  Local Lemma lt_minus_swap (q r a b : Q) : b - a < r - q -> q - a < r - b.
  Proof.
    intros l.
    rewrite <- (plus_minus_telescope b q a), <- (plus_minus_telescope q r b).
    rewrite (plus_comm (q - b)).
    exact (strictly_order_preserving (+ (q - b)) _ _ l).
  Qed.

  (** [q < x + y] when [q = s + t] with [s < x] and [t < y], and dually. *)
  Section plus.
    Context (x y : R).

    Local Definition plus_lower (q : Q) : HProp
      := Build_HProp (hexists (fun s => prod (lower_cut x s) (lower_cut y (q - s)))).
    Local Definition plus_upper (r : Q) : HProp
      := Build_HProp (hexists (fun s => prod (upper_cut x s) (upper_cut y (r - s)))).

    Lemma isdedekindcut_plus : IsDedekindCut plus_lower plus_upper.
    Proof.
      split.
      - assert (a := cut_lower_inhabited (isdedekindcut x)).
        assert (b := cut_lower_inhabited (isdedekindcut y)).
        strip_truncations; destruct a as [a la], b as [b lb].
        apply tr; exists (a + b); apply tr; exists a.
        rewrite plus_minus_cancel_l; exact (la, lb).
      - assert (a := cut_upper_inhabited (isdedekindcut x)).
        assert (b := cut_upper_inhabited (isdedekindcut y)).
        strip_truncations; destruct a as [a ua], b as [b ub].
        apply tr; exists (a + b); apply tr; exists a.
        rewrite plus_minus_cancel_l; exact (ua, ub).
      - intros q; split.
        + intros p; strip_truncations; destruct p as [s [ls lt]].
          apply (lower_cut_rounded y) in lt; strip_truncations; destruct lt as [t [l lt]].
          apply tr; exists (s + t); split.
          * rewrite (plus_conjugate_alt q s).
            exact (strictly_order_preserving (s +) _ _ l).
          * apply tr; exists s; rewrite plus_minus_cancel_l; exact (ls, lt).
        + intros p; strip_truncations; destruct p as [q' [l p]]; strip_truncations.
          destruct p as [s [ls lt]].
          exact (tr (s; (ls, lower_cut_lt y _ _ (minus_lt_minus _ _ s l) lt))).
      - intros r; split.
        + intros p; strip_truncations; destruct p as [s [us ut]].
          apply (upper_cut_rounded y) in ut; strip_truncations; destruct ut as [t [l ut]].
          apply tr; exists (s + t); split.
          * rewrite (plus_conjugate_alt r s).
            exact (strictly_order_preserving (s +) _ _ l).
          * apply tr; exists s; rewrite plus_minus_cancel_l; exact (us, ut).
        + intros p; strip_truncations; destruct p as [r' [l p]]; strip_truncations.
          destruct p as [s [us ut]].
          exact (tr (s; (us, upper_cut_lt y _ _ (minus_lt_minus _ _ s l) ut))).
      - intros q r p p'; strip_truncations.
        destruct p as [s [ls lt]], p' as [s' [us' ut']].
        rewrite (plus_conjugate_alt q s), (plus_conjugate_alt r s').
        apply plus_lt_compat.
        + exact (cut_transitive (isdedekindcut x) _ _ ls us').
        + exact (cut_transitive (isdedekindcut y) _ _ lt ut').
      - intros q r l.
        assert (c := cut_approximate x (Qpos_diff q r l)); strip_truncations.
        destruct c as [a c]; strip_truncations; destruct c as [b [[la ub] lab]].
        assert (l' : q - a < r - b) by exact (lt_minus_swap q r a b lab).
        assert (c := cut_located (isdedekindcut y) _ _ l'); strip_truncations.
        destruct c as [c|c]; apply tr; [left|right]; apply tr.
        + exact (a; (la, c)).
        + exact (b; (ub, c)).
    Qed.
  End plus.

  #[export] Instance plus_dedekindreals : Plus R
    := fun x y => Build_DedekindReals _ _ (isdedekindcut_plus x y).

  (** ** Negation *)

  Section negate.
    Context (x : R).

    Lemma isdedekindcut_negate
      : IsDedekindCut (fun q => upper_cut x (- q)) (fun r => lower_cut x (- r)).
    Proof.
      split.
      - assert (b := cut_upper_inhabited (isdedekindcut x)); strip_truncations.
        destruct b as [b ub]; apply tr; exists (- b); rewrite negate_involutive; exact ub.
      - assert (a := cut_lower_inhabited (isdedekindcut x)); strip_truncations.
        destruct a as [a la]; apply tr; exists (- a); rewrite negate_involutive; exact la.
      - intros q; split.
        + intros p; apply (upper_cut_rounded x) in p; strip_truncations.
          destruct p as [r [l p]]; apply tr; exists (- r); split.
          * exact (flip_lt_negate_r _ _ l).
          * rewrite negate_involutive; exact p.
        + intros p; strip_truncations; destruct p as [q' [l p]].
          exact (upper_cut_lt x _ _ (snd (flip_lt_negate _ _) l) p).
      - intros r; split.
        + intros p; apply (lower_cut_rounded x) in p; strip_truncations.
          destruct p as [q [l p]]; apply tr; exists (- q); split.
          * exact (flip_lt_negate_l _ _ l).
          * rewrite negate_involutive; exact p.
        + intros p; strip_truncations; destruct p as [r' [l p]].
          exact (lower_cut_lt x _ _ (snd (flip_lt_negate _ _) l) p).
      - intros q r u l.
        exact (fst (flip_lt_negate _ _) (cut_transitive (isdedekindcut x) _ _ l u)).
      - intros q r l.
        assert (c := cut_located (isdedekindcut x) _ _ (snd (flip_lt_negate q r) l)).
        strip_truncations; apply tr; destruct c as [c|c]; [right|left]; exact c.
    Qed.
  End negate.

  #[export] Instance negate_dedekindreals : Negate R
    := fun x => Build_DedekindReals _ _ (isdedekindcut_negate x).

  #[export] Instance zero_dedekindreals : Zero R := rational_dedekind 0.
  #[export] Instance one_dedekindreals : One R := rational_dedekind 1.

  (** ** The additive group *)

  Lemma plus_dedekindreals_comm (x y : R) : x + y = y + x.
  Proof.
    apply path_dedekindreals.
    - intros q p; strip_truncations; destruct p as [s [ls lt]].
      apply tr; exists (q - s); rewrite minus_minus_cancel; exact (lt, ls).
    - intros r p; strip_truncations; destruct p as [s [us ut]].
      apply tr; exists (r - s); rewrite minus_minus_cancel; exact (ut, us).
  Qed.

  Local Lemma minus_plus_distr (q s t : Q) : q - (s + t) = (q - s) - t.
  Proof.
    rewrite negate_plus_distr; apply plus_assoc.
  Qed.

  Lemma plus_dedekindreals_assoc (x y z : R) : x + (y + z) = (x + y) + z.
  Proof.
    apply path_dedekindreals.
    - intros q p; strip_truncations; destruct p as [s [ls p]]; strip_truncations.
      destruct p as [t [lt lu]].
      apply tr; exists (s + t); split.
      + apply tr; exists s; rewrite plus_minus_cancel_l; exact (ls, lt).
      + rewrite minus_plus_distr; exact lu.
    - intros r p; strip_truncations; destruct p as [s [us p]]; strip_truncations.
      destruct p as [t [ut uu]].
      apply tr; exists (s + t); split.
      + apply tr; exists s; rewrite plus_minus_cancel_l; exact (us, ut).
      + rewrite minus_plus_distr; exact uu.
  Qed.

  Lemma plus_dedekindreals_0_l (x : R) : 0 + x = x.
  Proof.
    apply path_dedekindreals.
    - intros q p; strip_truncations; destruct p as [s [ls lx]]; cbn in ls.
      exact (lower_cut_lt x _ _ (fst (pos_plus_lt_compat_r q (- s)) (fst (flip_neg_negate s) ls)) lx).
    - intros r p; strip_truncations; destruct p as [s [us ux]]; cbn in us.
      exact (upper_cut_lt x _ _ (fst (pos_minus_lt_compat_r r s) us) ux).
  Qed.

  Lemma plus_dedekindreals_negate_l (x : R) : - x + x = 0.
  Proof.
    apply path_dedekindreals.
    - intros q p; strip_truncations; destruct p as [s [us lx]]; cbn in us |- *.
      assert (l := strictly_order_preserving (+ s) _ _ (cut_transitive (isdedekindcut x) _ _ lx us)).
      cbn in l; rewrite <- plus_assoc, !plus_negate_l, plus_0_r in l; exact l.
    - intros r p; strip_truncations; destruct p as [s [ls ux]]; cbn in ls |- *.
      assert (l := strictly_order_preserving (+ s) _ _ (cut_transitive (isdedekindcut x) _ _ ls ux)).
      cbn in l; rewrite <- plus_assoc, !plus_negate_l, plus_0_r in l; exact l.
  Qed.

  (** ** The strict order *)

  Definition path_dedekindreals_lower (x y : R)
    (l : forall q, lower_cut x q -> lower_cut y q) (l' : forall q, lower_cut y q -> lower_cut x q)
    : x = y.
  Proof.
    apply (path_dedekindreals x y l).
    intros r u; apply (upper_cut_rounded x r) in u; strip_truncations; destruct u as [r' [lr u]].
    assert (c := cut_located (isdedekindcut y) r' r lr); strip_truncations.
    destruct c as [c|c]; [destruct (cut_disjoint x r' (l' r' c) u)|exact c].
  Defined.

  Lemma lt_dedekindreals_irrefl (x : R) : ~ (x < x).
  Proof.
    intros l; strip_truncations; destruct l as [q [u p]]; exact (cut_disjoint x q p u).
  Qed.

  Lemma lt_dedekindreals_antisym (x y : R) : ~ (prod (x < y) (y < x)).
  Proof.
    intros [l l']; strip_truncations; destruct l as [q [uq lq]], l' as [r [ur lr]].
    apply (irreflexivity (<) q), (transitivity (y:=r)).
    - exact (cut_transitive (isdedekindcut y) _ _ lq ur).
    - exact (cut_transitive (isdedekindcut x) _ _ lr uq).
  Qed.

  Lemma lt_dedekindreals_cotrans (x y : R) : x < y -> forall z, hor (x < z) (z < y).
  Proof.
    intros l z; strip_truncations; destruct l as [q [uq lq]].
    apply (upper_cut_rounded x q) in uq; strip_truncations; destruct uq as [q' [l uq']].
    assert (c := cut_located (isdedekindcut z) q' q l); strip_truncations.
    destruct c as [c|c]; apply tr; [left|right]; apply tr.
    - exact (q'; (uq', c)).
    - exact (q; (c, lq)).
  Qed.

  Lemma lt_dedekindreals_trans (x y z : R) : x < y -> y < z -> x < z.
  Proof.
    intros l l'; strip_truncations; destruct l as [q [uq lq]], l' as [r [ur lr]].
    apply tr; exists q; split; [exact uq|].
    exact (lower_cut_lt z q r (cut_transitive (isdedekindcut y) _ _ lq ur) lr).
  Qed.

  #[export] Instance isapart_dedekindreals : IsApart R.
  Proof.
    split.
    - exact _.
    - exact _.
    - intros x y a; strip_truncations; apply tr; destruct a as [a|a]; [right|left]; exact a.
    - intros x y a z; strip_truncations; destruct a as [a|a].
      + assert (c := lt_dedekindreals_cotrans x y a z); strip_truncations.
        apply tr; destruct c as [c|c]; [left|right]; apply tr; left; exact c.
      + assert (c := lt_dedekindreals_cotrans y x a z); strip_truncations.
        apply tr; destruct c as [c|c]; [right|left]; apply tr; right; exact c.
    - intros x y; split.
      + intros na; apply path_dedekindreals_lower.
        * apply (snd (le_iff_not_lt_dedekindreals x y)); intros l; exact (na (tr (inr l))).
        * apply (snd (le_iff_not_lt_dedekindreals y x)); intros l; exact (na (tr (inl l))).
      + intros [] a; strip_truncations; destruct a as [a|a]; exact (lt_dedekindreals_irrefl x a).
  Qed.

  #[export] Instance pseudoorder_dedekindreals : PseudoOrder (_ : Lt R).
  Proof.
    split.
    - exact _.
    - exact _.
    - exact lt_dedekindreals_antisym.
    - exact lt_dedekindreals_cotrans.
    - intros x y; split.
      + intros a; refine (Trunc_rec idmap a).
        apply ishprop_sum; [exact _|exact _|].
        intros l l'; exact (lt_dedekindreals_antisym x y (l, l')).
      + exact tr.
  Qed.

  #[export] Instance fullpseudoorder_dedekindreals : FullPseudoOrder (_ : Le R) (_ : Lt R).
  Proof.
    split.
    - exact _.
    - exact _.
    - exact le_iff_not_lt_dedekindreals.
  Qed.

  (** ** Lattice structure *)

  (** Two lower bounds of a real have a common upper bound that is a lower bound, and dually. *)
  Lemma lower_cut_max (x : R) (a a' : Q) : lower_cut x a -> lower_cut x a'
    -> {c : Q & prod (lower_cut x c) (prod (a <= c) (a' <= c))}.
  Proof.
    intros la la'; destruct (le_or_lt a a') as [l|l].
    - exact (a'; (la', (l, reflexivity a'))).
    - exact (a; (la, (reflexivity a, lt_le _ _ l))).
  Qed.

  Lemma upper_cut_min (x : R) (b b' : Q) : upper_cut x b -> upper_cut x b'
    -> {c : Q & prod (upper_cut x c) (prod (c <= b) (c <= b'))}.
  Proof.
    intros ub ub'; destruct (le_or_lt b b') as [l|l].
    - exact (b; (ub, (reflexivity b, l))).
    - exact (b'; (ub', (lt_le _ _ l, reflexivity b'))).
  Qed.

  (** The join has the union of the lower cuts and the intersection of the upper cuts; dually for the meet. *)
  Section join.
    Context (x y : R).

    Lemma isdedekindcut_join
      : IsDedekindCut (fun q => Build_HProp (hor (lower_cut x q) (lower_cut y q)))
          (fun r => Build_HProp (prod (upper_cut x r) (upper_cut y r))).
    Proof.
      split; cbn.
      - assert (a := cut_lower_inhabited (isdedekindcut x)); strip_truncations.
        destruct a as [a la]; exact (tr (a; tr (inl la))).
      - assert (b := cut_upper_inhabited (isdedekindcut x)).
        assert (b' := cut_upper_inhabited (isdedekindcut y)); strip_truncations.
        destruct b as [b ub], b' as [b' ub'].
        destruct (le_or_lt b b') as [l|l]; apply tr.
        + exact (b'; (upper_cut_le x _ _ l ub, ub')).
        + exact (b; (ub, upper_cut_lt y _ _ l ub')).
      - intros q; split.
        + intros p; strip_truncations; destruct p as [p|p].
          * apply (lower_cut_rounded x q) in p; strip_truncations; destruct p as [q' [l p]].
            exact (tr (q'; (l, tr (inl p)))).
          * apply (lower_cut_rounded y q) in p; strip_truncations; destruct p as [q' [l p]].
            exact (tr (q'; (l, tr (inr p)))).
        + intros p; strip_truncations; destruct p as [q' [l p]]; strip_truncations.
          apply tr; destruct p as [p|p]; [left|right]; exact (lower_cut_lt _ _ _ l p).
      - intros r; split.
        + intros [p p'].
          apply (upper_cut_rounded x r) in p; apply (upper_cut_rounded y r) in p'.
          strip_truncations; destruct p as [s [l p]], p' as [s' [l' p']].
          destruct (le_or_lt s s') as [ls|ls]; apply tr.
          * exact (s'; (l', (upper_cut_le x _ _ ls p, p'))).
          * exact (s; (l, (p, upper_cut_lt y _ _ ls p'))).
        + intros p; strip_truncations; destruct p as [r' [l [p p']]].
          exact (upper_cut_lt x _ _ l p, upper_cut_lt y _ _ l p').
      - intros q r p [u u']; strip_truncations; destruct p as [p|p].
        + exact (cut_transitive (isdedekindcut x) _ _ p u).
        + exact (cut_transitive (isdedekindcut y) _ _ p u').
      - intros q r l.
        assert (c := cut_located (isdedekindcut x) q r l).
        assert (c' := cut_located (isdedekindcut y) q r l); strip_truncations.
        destruct c as [c|c]; [exact (tr (inl (tr (inl c))))|].
        destruct c' as [c'|c']; [exact (tr (inl (tr (inr c'))))|].
        exact (tr (inr (c, c'))).
    Qed.

    Lemma isdedekindcut_meet
      : IsDedekindCut (fun q => Build_HProp (prod (lower_cut x q) (lower_cut y q)))
          (fun r => Build_HProp (hor (upper_cut x r) (upper_cut y r))).
    Proof.
      split; cbn.
      - assert (a := cut_lower_inhabited (isdedekindcut x)).
        assert (a' := cut_lower_inhabited (isdedekindcut y)); strip_truncations.
        destruct a as [a la], a' as [a' la'].
        destruct (le_or_lt a a') as [l|l]; apply tr.
        + exact (a; (la, lower_cut_le y _ _ l la')).
        + exact (a'; (lower_cut_lt x _ _ l la, la')).
      - assert (b := cut_upper_inhabited (isdedekindcut x)); strip_truncations.
        destruct b as [b ub]; exact (tr (b; tr (inl ub))).
      - intros q; split.
        + intros [p p'].
          apply (lower_cut_rounded x q) in p; apply (lower_cut_rounded y q) in p'.
          strip_truncations; destruct p as [s [l p]], p' as [s' [l' p']].
          destruct (le_or_lt s s') as [ls|ls]; apply tr.
          * exact (s; (l, (p, lower_cut_le y _ _ ls p'))).
          * exact (s'; (l', (lower_cut_lt x _ _ ls p, p'))).
        + intros p; strip_truncations; destruct p as [q' [l [p p']]].
          exact (lower_cut_lt x _ _ l p, lower_cut_lt y _ _ l p').
      - intros r; split.
        + intros p; strip_truncations; destruct p as [p|p].
          * apply (upper_cut_rounded x r) in p; strip_truncations; destruct p as [r' [l p]].
            exact (tr (r'; (l, tr (inl p)))).
          * apply (upper_cut_rounded y r) in p; strip_truncations; destruct p as [r' [l p]].
            exact (tr (r'; (l, tr (inr p)))).
        + intros p; strip_truncations; destruct p as [r' [l p]]; strip_truncations.
          apply tr; destruct p as [p|p]; [left|right]; exact (upper_cut_lt _ _ _ l p).
      - intros q r [p p'] u; strip_truncations; destruct u as [u|u].
        + exact (cut_transitive (isdedekindcut x) _ _ p u).
        + exact (cut_transitive (isdedekindcut y) _ _ p' u).
      - intros q r l.
        assert (c := cut_located (isdedekindcut x) q r l).
        assert (c' := cut_located (isdedekindcut y) q r l); strip_truncations.
        destruct c as [c|c]; [|exact (tr (inr (tr (inl c))))].
        destruct c' as [c'|c']; [|exact (tr (inr (tr (inr c'))))].
        exact (tr (inl (c, c'))).
    Qed.
  End join.

  #[export] Instance join_dedekindreals : Join R
    := fun x y => Build_DedekindReals _ _ (isdedekindcut_join x y).
  #[export] Instance meet_dedekindreals : Meet R
    := fun x y => Build_DedekindReals _ _ (isdedekindcut_meet x y).

  #[export] Instance partialorder_dedekindreals : PartialOrder (_ : Le R).
  Proof.
    split.
    - exact _.
    - exact _.
    - split.
      + intros x q p; exact p.
      + intros x y z l l' q p; exact (l' q (l q p)).
    - intros x y l l'; exact (path_dedekindreals_lower x y l l').
  Qed.

  #[export] Instance latticeorder_dedekindreals : LatticeOrder (_ : Le R).
  Proof.
    split; split.
    - exact _.
    - intros x y q p; exact (fst p).
    - intros x y q p; exact (snd p).
    - intros x y z l l' q p; exact (l q p, l' q p).
    - exact _.
    - intros x y q p; exact (tr (inl p)).
    - intros x y q p; exact (tr (inr p)).
    - intros x y z l l' q p; strip_truncations; destruct p as [p|p]; [exact (l q p)|exact (l' q p)].
  Qed.
End dedekind.
