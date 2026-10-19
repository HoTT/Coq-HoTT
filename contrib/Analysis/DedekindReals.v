(** * Dedekind reals *)

(** The Dedekind reals over a model [Q] of the rationals: pairs of a lower and an upper cut, predicates on [Q] that are inhabited, rounded, transitive and located.  We show that they form a set and an Archimedean ordered field, and that they are Cauchy complete, with the limit given by an explicit cut. *)

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
  orders.dec_fields
  interfaces.archimedean
  interfaces.cauchy.
From HoTT.Analysis Require Import Locator.

Section dedekind.
  Context `{Funext} `{Univalence}.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}
    {Qroundup : RoundUpStrict Q}.

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

  (** By locatedness, an inclusion of upper cuts gives the reverse inclusion of lower cuts, and vice versa. So inclusions of both cuts suffice for equality of Dedekind reals. *)
  Lemma lower_cut_incl_rev (x y : R) (uu : forall r, upper_cut x r -> upper_cut y r)
    (q : Q) : lower_cut y q -> lower_cut x q.
  Proof.
    intros p; apply (lower_cut_rounded y q) in p; strip_truncations; destruct p as [q' [l p]].
    assert (c := cut_located (isdedekindcut x) q q' l); strip_truncations; destruct c as [c|c].
    - exact c.
    - destruct (cut_disjoint y q' p (uu q' c)).
  Qed.

  Lemma upper_cut_incl_rev (x y : R) (ll : forall q, lower_cut x q -> lower_cut y q)
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
    - apply (lower_cut_incl_rev x y uu).
    - apply uu.
    - apply (upper_cut_incl_rev x y ll).
  Defined.

  (** ** Approximation *)

  Local Lemma pos_quarter_double (e : Qpos Q) : ' (e / 2 / 2) + ' (e / 2 / 2) < ' e.
  Proof.
    change (' (e / 2 / 2 + e / 2 / 2) < ' e); rewrite <- pos_split2.
    apply qpos_half_lt.
  Qed.

  Local Lemma plus_minus_cancel_l (a b : Q) : (a + b) - a = b.
  Proof.
    rewrite (plus_comm a), <- plus_assoc, plus_negate_r; apply plus_0_r.
  Qed.

  (** A Dedekind cut has a lower and an upper bound arbitrarily close to each other: walk up from a lower bound in steps of [e / 4], using locatedness at each step. *)
  Lemma cut_approximate (x : R) (e : Qpos Q)
    : merely {a : Q & {b : Q & prod (prod (lower_cut x a) (upper_cut x b)) (b - a < ' e)}}.
  Proof.
    assert (a0 := cut_lower_inhabited (isdedekindcut x)).
    assert (b0 := cut_upper_inhabited (isdedekindcut x)).
    strip_truncations; destruct a0 as [a0 la0], b0 as [b0 ub0].
    set (d := e / 2 / 2).
    set (p k := a0 + nQ k * ' d).
    assert (step : forall k, hor (merely {a : Q & {b : Q &
                      prod (prod (lower_cut x a) (upper_cut x b)) (b - a < ' e)}})
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
        + apply tr, inl, tr; exists (p k); exists (p k + ' d + ' d).
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
    lhs' exact lN'.
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
  #[local] Instance lt_dedekindreals : Lt R
    := fun x y => hexists (fun q => prod (upper_cut x q) (lower_cut y q)).

  #[local] Instance le_dedekindreals : Le R
    := fun x y => forall q, lower_cut x q -> lower_cut y q.

  #[local] Instance apart_dedekindreals : Apart R
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

  Local Lemma lt_minus_swap (q r a b : Q) : b - a < r - q -> q - a < r - b.
  Proof.
    intros l.
    rewrite <- (plus_minus_telescope q b a), <- (plus_minus_telescope r q b).
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
        destruct c as [a [b [[la ub] lab]]].
        assert (l' : q - a < r - b) by exact (lt_minus_swap q r a b lab).
        assert (c := cut_located (isdedekindcut y) _ _ l'); strip_truncations.
        destruct c as [c|c]; apply tr; [left|right]; apply tr.
        + exact (a; (la, c)).
        + exact (b; (ub, c)).
    Qed.
  End plus.

  #[local] Instance plus_dedekindreals : Plus R
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

  #[local] Instance negate_dedekindreals : Negate R
    := fun x => Build_DedekindReals _ _ (isdedekindcut_negate x).

  #[local] Instance zero_dedekindreals : Zero R := rational_dedekind 0.
  #[local] Instance one_dedekindreals : One R := rational_dedekind 1.

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

  #[local] Instance join_dedekindreals : Join R
    := fun x y => Build_DedekindReals _ _ (isdedekindcut_join x y).
  #[local] Instance meet_dedekindreals : Meet R
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

  (** ** Multiplication *)

  (** Rational bounds of a real. *)
  Record CutBounds (x : R) := {
    bound_lo : Q ;
    bound_hi : Q ;
    bound_lo_lower : lower_cut x bound_lo ;
    bound_hi_upper : upper_cut x bound_hi }.

  Arguments bound_lo {x} _.
  Arguments bound_hi {x} _.
  Arguments bound_lo_lower {x} _.
  Arguments bound_hi_upper {x} _.

  Definition in_bounds {x : R} (I : CutBounds x) (s : Q) : Type
    := prod (bound_lo I <= s) (s <= bound_hi I).

  Section bounds.
    Context {x : R}.

    Lemma merely_cutbounds : merely (CutBounds x).
    Proof.
      assert (a := cut_lower_inhabited (isdedekindcut x)).
      assert (b := cut_upper_inhabited (isdedekindcut x)); strip_truncations.
      exact (tr (Build_CutBounds x a.1 b.1 a.2 b.2)).
    Qed.

    Lemma bound_lo_lt_hi (I : CutBounds x) : bound_lo I < bound_hi I.
    Proof.
      exact (cut_transitive (isdedekindcut x) _ _ (bound_lo_lower I) (bound_hi_upper I)).
    Qed.

    Lemma in_bounds_lo (I : CutBounds x) : in_bounds I (bound_lo I).
    Proof.
      exact (reflexivity _, lt_le _ _ (bound_lo_lt_hi I)).
    Qed.

    Lemma in_bounds_hi (I : CutBounds x) : in_bounds I (bound_hi I).
    Proof.
      exact (lt_le _ _ (bound_lo_lt_hi I), reflexivity _).
    Qed.

    (** Two pairs of bounds can be refined to a pair inside both. *)
    Lemma cutbounds_intersect (I I' : CutBounds x)
      : {I'' : CutBounds x & forall s, in_bounds I'' s -> prod (in_bounds I s) (in_bounds I' s)}.
    Proof.
      destruct (lower_cut_max x _ _ (bound_lo_lower I) (bound_lo_lower I')) as [a [la [l1 l2]]].
      destruct (upper_cut_min x _ _ (bound_hi_upper I) (bound_hi_upper I')) as [b [ub [l3 l4]]].
      exists (Build_CutBounds x a b la ub); intros s [l5 l6]; cbn in l5, l6.
      split; split.
      - exact (transitivity l1 l5).
      - exact (transitivity l6 l3).
      - exact (transitivity l2 l5).
      - exact (transitivity l6 l4).
    Qed.
  End bounds.

  (** Rationals below or above two given ones. *)
  Local Lemma rational_below2 (u v : Q) : {w : Q & prod (w < u) (w < v)}.
  Proof.
    destruct (le_or_lt u v) as [l|l].
    - exists (u - 1); split; [|apply (lt_le_trans _ u)]; try exact l;
        exact (fst (pos_minus_lt_compat_r u 1) lt_0_1).
    - exists (v - 1); split; [apply (transitivity (y:=v))|]; try exact l;
        exact (fst (pos_minus_lt_compat_r v 1) lt_0_1).
  Qed.

  Local Lemma rational_above2 (u v : Q) : {w : Q & prod (u < w) (v < w)}.
  Proof.
    destruct (le_or_lt u v) as [l|l].
    - exists (v + 1); split; [apply (le_lt_trans _ v)|]; try exact l;
        exact (fst (pos_plus_lt_compat_r v 1) lt_0_1).
    - exists (u + 1); split; [|apply (transitivity (y:=u))]; try exact l;
        exact (fst (pos_plus_lt_compat_r u 1) lt_0_1).
  Qed.

  (** A rational between [q] and two rationals above it, and dually. *)
  Local Lemma rational_between_below2 (q u v : Q) : q < u -> q < v -> {w : Q & prod (q < w) (prod (w < u) (w < v))}.
  Proof.
    intros lu lv; destruct (le_or_lt u v) as [l|l].
    - destruct (Q_dense q u lu) as [w [l1 l2]].
      exact (w; (l1, (l2, lt_le_trans _ _ _ l2 l))).
    - destruct (Q_dense q v lv) as [w [l1 l2]].
      exact (w; (l1, (transitivity l2 l, l2))).
  Qed.

  Local Lemma rational_between_above2 (r u v : Q) : u < r -> v < r -> {w : Q & prod (w < r) (prod (u < w) (v < w))}.
  Proof.
    intros lu lv; destruct (le_or_lt u v) as [l|l].
    - destruct (Q_dense v r lv) as [w [l1 l2]].
      exact (w; (l2, (le_lt_trans _ _ _ l l1, l1))).
    - destruct (Q_dense u r lu) as [w [l1 l2]].
      exact (w; (l2, (l1, transitivity l l1))).
  Qed.

  (** The minimum of two rationals, characterized by any property they both have. *)
  Local Lemma rational_min2 (u v : Q)
    : {m : Q & prod (prod (m <= u) (m <= v)) (forall P : Q -> Type, P u -> P v -> P m)}.
  Proof.
    destruct (le_or_lt u v) as [l|l].
    - exact (u; ((reflexivity u, l), fun P pu pv => pu)).
    - exact (v; ((lt_le _ _ l, reflexivity v), fun P pu pv => pv)).
  Qed.

  Local Lemma rational_max2 (u v : Q)
    : {m : Q & prod (prod (u <= m) (v <= m)) (forall P : Q -> Type, P u -> P v -> P m)}.
  Proof.
    destruct (le_or_lt u v) as [l|l].
    - exact (v; ((l, reflexivity v), fun P pu pv => pv)).
    - exact (u; ((reflexivity u, lt_le _ _ l), fun P pu pv => pu)).
  Qed.

  (** A rational strictly bounding two given ones in absolute value. *)
  Local Lemma rational_bound (a b : Q) : {X : Q & prod (- X < a) (b < X)}.
  Proof.
    destruct (round_up_strict Q b) as [m lm], (round_up_strict Q (- a)) as [n ln].
    exists (nQ m + nQ n); split.
    - apply flip_lt_negate_l.
      apply (lt_le_trans _ (nQ n)); [exact ln|].
      apply nonneg_plus_le_compat_l, nat_to_semiring_nonneg.
    - apply (lt_le_trans _ (nQ m)); [exact lm|].
      apply nonneg_plus_le_compat_r, nat_to_semiring_nonneg.
  Qed.

  (** A positive rational whose product with [S] is less than [e]. *)
  Local Lemma small_factor (e S : Q) : 0 < e -> 0 < S -> {D : Qpos Q & ' D * S < e}.
  Proof.
    intros epos Spos.
    pose (e' := mkQpos e epos : Qpos Q).
    pose (S' := mkQpos S Spos : Qpos Q).
    exists (e' / S' / 2); cbn.
    rewrite <- (mult_assoc e), (mult_comm (/ S)), <- !mult_assoc.
    rewrite (mult_comm (/ S)), dec_recip_inverse, mult_1_r; [|apply lt_ne_flip, Spos].
    exact (qpos_half_lt e').
  Qed.

  (** [q < x * y] when [q] is below all products of points of some bounds of [x] and of [y], and dually. *)
  Definition BelowProducts {x y : R} (q : Q) (I : CutBounds x) (J : CutBounds y) : Type
    := forall s t, in_bounds I s -> in_bounds J t -> q < s * t.

  Definition AboveProducts {x y : R} (r : Q) (I : CutBounds x) (J : CutBounds y) : Type
    := forall s t, in_bounds I s -> in_bounds J t -> s * t < r.

  (** It suffices to check the four corners. *)
  Lemma belowproducts_corners {x y : R} (q : Q) (I : CutBounds x) (J : CutBounds y)
    : q < bound_lo I * bound_lo J -> q < bound_lo I * bound_hi J
      -> q < bound_hi I * bound_lo J -> q < bound_hi I * bound_hi J -> BelowProducts q I J.
  Proof.
    intros l1 l2 l3 l4 s t [ls ls'] [lt lt'].
    exact (lt_mult_corners_l q _ _ _ _ s t ls ls' lt lt' l1 l2 l3 l4).
  Qed.

  Lemma aboveproducts_corners {x y : R} (r : Q) (I : CutBounds x) (J : CutBounds y)
    : bound_lo I * bound_lo J < r -> bound_lo I * bound_hi J < r
      -> bound_hi I * bound_lo J < r -> bound_hi I * bound_hi J < r -> AboveProducts r I J.
  Proof.
    intros l1 l2 l3 l4 s t [ls ls'] [lt lt'].
    exact (mult_corners_lt_r r _ _ _ _ s t ls ls' lt lt' l1 l2 l3 l4).
  Qed.

  Section mult.
    Context (x y : R).

    Local Definition mult_lower (q : Q) : HProp
      := Build_HProp (hexists (fun I : CutBounds x => hexists (fun J : CutBounds y => BelowProducts q I J))).
    Local Definition mult_upper (r : Q) : HProp
      := Build_HProp (hexists (fun I : CutBounds x => hexists (fun J : CutBounds y => AboveProducts r I J))).

    Local Lemma mult_lower_rounded (q : Q) : mult_lower q -> hexists (fun q' => prod (q < q') (mult_lower q')).
    Proof.
      intros p; strip_truncations; destruct p as [I p]; strip_truncations; destruct p as [J p].
      pose (c s t := p s t).
      destruct (rational_between_below2 q _ _ (c _ _ (in_bounds_lo I) (in_bounds_lo J))
                  (c _ _ (in_bounds_lo I) (in_bounds_hi J))) as [w1 [l1 [l1' l1'']]].
      destruct (rational_between_below2 q _ _ (c _ _ (in_bounds_hi I) (in_bounds_lo J))
                  (c _ _ (in_bounds_hi I) (in_bounds_hi J))) as [w2 [l2 [l2' l2'']]].
      destruct (rational_between_below2 q _ _ l1 l2) as [w [l [lw1 lw2]]].
      apply tr; exists w; split; [exact l|].
      apply tr; exists I; apply tr; exists J.
      apply belowproducts_corners.
      - exact (transitivity lw1 l1').
      - exact (transitivity lw1 l1'').
      - exact (transitivity lw2 l2').
      - exact (transitivity lw2 l2'').
    Qed.

    Local Lemma mult_upper_rounded (r : Q) : mult_upper r -> hexists (fun r' => prod (r' < r) (mult_upper r')).
    Proof.
      intros p; strip_truncations; destruct p as [I p]; strip_truncations; destruct p as [J p].
      pose (c s t := p s t).
      destruct (rational_between_above2 r _ _ (c _ _ (in_bounds_lo I) (in_bounds_lo J))
                  (c _ _ (in_bounds_lo I) (in_bounds_hi J))) as [w1 [l1 [l1' l1'']]].
      destruct (rational_between_above2 r _ _ (c _ _ (in_bounds_hi I) (in_bounds_lo J))
                  (c _ _ (in_bounds_hi I) (in_bounds_hi J))) as [w2 [l2 [l2' l2'']]].
      destruct (rational_between_above2 r _ _ l1 l2) as [w [l [lw1 lw2]]].
      apply tr; exists w; split; [exact l|].
      apply tr; exists I; apply tr; exists J.
      apply aboveproducts_corners.
      - exact (transitivity l1' lw1).
      - exact (transitivity l1'' lw1).
      - exact (transitivity l2' lw2).
      - exact (transitivity l2'' lw2).
    Qed.

    (** For locatedness, we take bounds so close that all products of their points are less than [r - q] apart. *)
    Local Lemma mult_located (q r : Q) : q < r -> hor (mult_lower q) (mult_upper r).
    Proof.
      intros l.
      assert (I0 := @merely_cutbounds x); assert (J0 := @merely_cutbounds y); strip_truncations.
      destruct (rational_bound (bound_lo I0) (bound_hi I0)) as [X [lX lX']].
      destruct (rational_bound (bound_lo J0) (bound_hi J0)) as [W [lW lW']].
      assert (Xpos := pos_between_negate (bound_lo I0) X (lX, transitivity (bound_lo_lt_hi I0) lX')).
      assert (Wpos := pos_between_negate (bound_lo J0) W (lW, transitivity (bound_lo_lt_hi J0) lW')).
      assert (epos := snd (flip_pos_minus q r) l).
      destruct (small_factor (r - q) (X + W) epos (pos_plus_compat _ _ Xpos Wpos)) as [D lD].
      assert (ax := cut_approximate x D); assert (ay := cut_approximate y D); strip_truncations.
      destruct ax as [a [b [[la ub] lab]]], ay as [c [d [[lc ud] lcd]]].
      destruct (cutbounds_intersect (Build_CutBounds x a b la ub) I0) as [I HI].
      destruct (cutbounds_intersect (Build_CutBounds y c d lc ud) J0) as [J HJ].
      assert (close : forall s t s' t', in_bounds I s -> in_bounds J t -> in_bounds I s'
                        -> in_bounds J t' -> s * t - s' * t' < r - q).
      { intros s t s' t' ins it ins' it'.
        destruct (HI s ins) as [[l1 l2] [l3 l4]], (HI s' ins') as [[l1' l2'] _].
        destruct (HJ t it) as [[m1 m2] _], (HJ t' it') as [[m1' m2'] [m3' m4']].
        cbn in l1, l2, l1', l2', m1, m2, m1', m2'.
        refine (lt_le_trans _ _ _ (snd (mult_minus_mult_lt_bound s t s' t' X W (' D)
                  (lt_le_trans _ _ _ lX l3, le_lt_trans _ _ _ l4 lX')
                  (lt_le_trans _ _ _ lW m3', le_lt_trans _ _ _ m4' lW')
                  (interval_minus_lt a b s s' (' D) (l1, l2) (l1', l2') lab)
                  (interval_minus_lt c d t t' (' D) (m1, m2) (m1', m2') lcd))) _).
        rewrite (mult_comm X), <- plus_mult_distr_l; exact (lt_le _ _ lD). }
      assert (upper_of : forall s0 t0, in_bounds I s0 -> in_bounds J t0 -> s0 * t0 <= q
                           -> mult_upper r).
      { intros s0 t0 i0 j0 le0; apply tr; exists I; apply tr; exists J; intros s t ins it.
        apply (lt_le_trans _ (r - q + s0 * t0)).
        - exact (fst (flip_lt_minus_l _ _ _) (close s t s0 t0 ins it i0 j0)).
        - apply (transitivity (y := r - q + q)).
          + apply (order_preserving (r - q +)); exact le0.
          + rewrite <- plus_assoc, plus_negate_l, plus_0_r; reflexivity. }
      destruct (le_or_lt (bound_lo I * bound_lo J) q) as [k|k1];
        [exact (tr (inr (upper_of _ _ (in_bounds_lo I) (in_bounds_lo J) k)))|].
      destruct (le_or_lt (bound_lo I * bound_hi J) q) as [k|k2];
        [exact (tr (inr (upper_of _ _ (in_bounds_lo I) (in_bounds_hi J) k)))|].
      destruct (le_or_lt (bound_hi I * bound_lo J) q) as [k|k3];
        [exact (tr (inr (upper_of _ _ (in_bounds_hi I) (in_bounds_lo J) k)))|].
      destruct (le_or_lt (bound_hi I * bound_hi J) q) as [k|k4];
        [exact (tr (inr (upper_of _ _ (in_bounds_hi I) (in_bounds_hi J) k)))|].
      exact (tr (inl (tr (I; tr (J; belowproducts_corners q I J k1 k2 k3 k4))))).
    Qed.

    Lemma isdedekindcut_mult : IsDedekindCut mult_lower mult_upper.
    Proof.
      split.
      - assert (I := @merely_cutbounds x); assert (J := @merely_cutbounds y); strip_truncations.
        destruct (rational_below2 (bound_lo I * bound_lo J) (bound_lo I * bound_hi J)) as [w1 [l1 l1']].
        destruct (rational_below2 (bound_hi I * bound_lo J) (bound_hi I * bound_hi J)) as [w2 [l2 l2']].
        destruct (rational_below2 w1 w2) as [w [lw1 lw2]].
        apply tr; exists w; apply tr; exists I; apply tr; exists J.
        apply belowproducts_corners.
        + exact (transitivity lw1 l1).
        + exact (transitivity lw1 l1').
        + exact (transitivity lw2 l2).
        + exact (transitivity lw2 l2').
      - assert (I := @merely_cutbounds x); assert (J := @merely_cutbounds y); strip_truncations.
        destruct (rational_above2 (bound_lo I * bound_lo J) (bound_lo I * bound_hi J)) as [w1 [l1 l1']].
        destruct (rational_above2 (bound_hi I * bound_lo J) (bound_hi I * bound_hi J)) as [w2 [l2 l2']].
        destruct (rational_above2 w1 w2) as [w [lw1 lw2]].
        apply tr; exists w; apply tr; exists I; apply tr; exists J.
        apply aboveproducts_corners.
        + exact (transitivity l1 lw1).
        + exact (transitivity l1' lw1).
        + exact (transitivity l2 lw2).
        + exact (transitivity l2' lw2).
      - intros q; split; [apply mult_lower_rounded|].
        intros p; strip_truncations; destruct p as [q' [l p]]; strip_truncations.
        destruct p as [I p]; strip_truncations; destruct p as [J p].
        apply tr; exists I; apply tr; exists J; intros s t ins it.
        exact (transitivity l (p s t ins it)).
      - intros r; split; [apply mult_upper_rounded|].
        intros p; strip_truncations; destruct p as [r' [l p]]; strip_truncations.
        destruct p as [I p]; strip_truncations; destruct p as [J p].
        apply tr; exists I; apply tr; exists J; intros s t ins it.
        exact (transitivity (p s t ins it) l).
      - intros q r p p'; strip_truncations.
        destruct p as [I p], p' as [I' p']; strip_truncations.
        destruct p as [J p], p' as [J' p'].
        destruct (cutbounds_intersect I I') as [I'' HI].
        destruct (cutbounds_intersect J J') as [J'' HJ].
        destruct (HI _ (in_bounds_lo I'')) as [i i'], (HJ _ (in_bounds_lo J'')) as [j j'].
        exact (transitivity (p _ _ i j) (p' _ _ i' j')).
      - exact mult_located.
    Qed.
  End mult.

  #[local] Instance mult_dedekindreals : Mult R
    := fun x y => Build_DedekindReals _ _ (isdedekindcut_mult x y).

  (** ** The multiplicative monoid and distributivity *)

  Lemma mult_dedekindreals_comm (x y : R) : x * y = y * x.
  Proof.
    apply path_dedekindreals.
    - intros q p; strip_truncations; destruct p as [I p]; strip_truncations; destruct p as [J p].
      apply tr; exists J; apply tr; exists I; intros s t ins it.
      rewrite mult_comm; exact (p t s it ins).
    - intros r p; strip_truncations; destruct p as [I p]; strip_truncations; destruct p as [J p].
      apply tr; exists J; apply tr; exists I; intros s t ins it.
      rewrite mult_comm; exact (p t s it ins).
  Qed.

  Lemma in_bounds_rational (q : Q) (I : CutBounds (rational_dedekind q)) : in_bounds I q.
  Proof.
    exact (lt_le _ _ (bound_lo_lower I), lt_le _ _ (bound_hi_upper I)).
  Qed.

  Lemma mult_dedekindreals_1_l (x : R) : 1 * x = x.
  Proof.
    apply path_dedekindreals.
    - intros q p; strip_truncations; destruct p as [I p]; strip_truncations; destruct p as [J p].
      refine (lower_cut_lt x _ _ _ (bound_lo_lower J)).
      rewrite <- (mult_1_l (bound_lo J)); exact (p _ _ (in_bounds_rational 1 I) (in_bounds_lo J)).
    - intros r p; strip_truncations; destruct p as [I p]; strip_truncations; destruct p as [J p].
      refine (upper_cut_lt x _ _ _ (bound_hi_upper J)).
      rewrite <- (mult_1_l (bound_hi J)); exact (p _ _ (in_bounds_rational 1 I) (in_bounds_hi J)).
  Qed.

  Section distribute.
    Context (x y z : R).

    Local Definition cutbounds_plus (J : CutBounds y) (K : CutBounds z) : CutBounds (y + z).
    Proof.
      srapply (Build_CutBounds (y + z) (bound_lo J + bound_lo K) (bound_hi J + bound_hi K));
        apply tr; [exists (bound_lo J)|exists (bound_hi J)]; rewrite plus_minus_cancel_l.
      - exact (bound_lo_lower J, bound_lo_lower K).
      - exact (bound_hi_upper J, bound_hi_upper K).
    Defined.

    Lemma mult_dedekindreals_plus_distr_l : x * (y + z) = x * y + x * z.
    Proof.
      symmetry; apply path_dedekindreals.
      - intros q p; strip_truncations; destruct p as [s [p p']]; strip_truncations.
        destruct p as [I1 p], p' as [I2 p']; strip_truncations.
        destruct p as [J p], p' as [K p'].
        destruct (cutbounds_intersect I1 I2) as [I HI].
        apply tr; exists I; apply tr; exists (cutbounds_plus J K).
        assert (c : forall u, in_bounds I u -> prod (q < u * (bound_lo J + bound_lo K))
                                               (q < u * (bound_hi J + bound_hi K))).
        { intros u iu; destruct (HI u iu) as [i1 i2].
          rewrite (plus_conjugate_alt q s), !plus_mult_distr_l; split; apply plus_lt_compat.
          - exact (p u _ i1 (in_bounds_lo J)).
          - exact (p' u _ i2 (in_bounds_lo K)).
          - exact (p u _ i1 (in_bounds_hi J)).
          - exact (p' u _ i2 (in_bounds_hi K)). }
        apply belowproducts_corners.
        + exact (fst (c _ (in_bounds_lo I))).
        + exact (snd (c _ (in_bounds_lo I))).
        + exact (fst (c _ (in_bounds_hi I))).
        + exact (snd (c _ (in_bounds_hi I))).
      - intros r p; strip_truncations; destruct p as [s [p p']]; strip_truncations.
        destruct p as [I1 p], p' as [I2 p']; strip_truncations.
        destruct p as [J p], p' as [K p'].
        destruct (cutbounds_intersect I1 I2) as [I HI].
        apply tr; exists I; apply tr; exists (cutbounds_plus J K).
        assert (c : forall u, in_bounds I u -> prod (u * (bound_lo J + bound_lo K) < r)
                                               (u * (bound_hi J + bound_hi K) < r)).
        { intros u iu; destruct (HI u iu) as [i1 i2].
          rewrite (plus_conjugate_alt r s), !plus_mult_distr_l; split; apply plus_lt_compat.
          - exact (p u _ i1 (in_bounds_lo J)).
          - exact (p' u _ i2 (in_bounds_lo K)).
          - exact (p u _ i1 (in_bounds_hi J)).
          - exact (p' u _ i2 (in_bounds_hi K)). }
        apply aboveproducts_corners.
        + exact (fst (c _ (in_bounds_lo I))).
        + exact (snd (c _ (in_bounds_lo I))).
        + exact (fst (c _ (in_bounds_hi I))).
        + exact (snd (c _ (in_bounds_hi I))).
    Qed.
  End distribute.

  Local Lemma lt_minus_lt (a b c d : Q) : a < b -> c < d -> a - d < b - c.
  Proof.
    intros l l'; apply plus_lt_compat; [exact l|exact (snd (flip_lt_negate _ _) l')].
  Qed.

  (** For associativity, given bounds [I], [J] and [G] of [x], [y] and [z] with [q'] below all products of their points, we bound [y * z] by the least and the greatest product of corners of [J] and [G], widened by a small [D]. *)
  Local Lemma mult_dedekindreals_assoc_lower (x y z : R) (q : Q)
    : lower_cut ((x * y) * z) q -> lower_cut (x * (y * z)) q.
  Proof.
    intros p; apply (lower_cut_rounded _ q) in p; strip_truncations; destruct p as [q' [lq p]].
    strip_truncations; destruct p as [E p]; strip_truncations; destruct p as [G pE].
    assert (lE := bound_lo_lower E); assert (uE := bound_hi_upper E); strip_truncations.
    destruct lE as [I1 lE], uE as [I2 uE]; strip_truncations.
    destruct lE as [J1 lE], uE as [J2 uE].
    destruct (cutbounds_intersect I1 I2) as [I HI], (cutbounds_intersect J1 J2) as [J HJ].
    assert (key : forall s t w, in_bounds I s -> in_bounds J t -> in_bounds G w -> q' < s * (t * w)).
    { intros s t w ins it iw; destruct (HI s ins) as [i1 i2], (HJ t it) as [j1 j2].
      rewrite mult_assoc; apply pE; [|exact iw].
      exact (lt_le _ _ (lE s t i1 j1), lt_le _ _ (uE s t i2 j2)). }
    destruct (rational_bound (bound_lo I) (bound_hi I)) as [T [lT lT']].
    assert (Tpos := pos_between_negate (bound_lo I) T (lT, transitivity (bound_lo_lt_hi I) lT')).
    destruct (small_factor (q' - q) T (snd (flip_pos_minus q q') lq) Tpos) as [D lD].
    pose (P k := forall s, in_bounds I s -> q' < s * k).
    assert (corner : forall t w, in_bounds J t -> in_bounds G w -> P (t * w))
      by (intros t w it iw s ins; exact (key s t w ins it iw)).
    destruct (rational_min2 (bound_lo J * bound_lo G) (bound_lo J * bound_hi G))
      as [m1 [[lm1 lm1'] Pm1]].
    destruct (rational_min2 (bound_hi J * bound_lo G) (bound_hi J * bound_hi G))
      as [m2 [[lm2 lm2'] Pm2]].
    destruct (rational_min2 m1 m2) as [m [[lm lm'] Pm]].
    destruct (rational_max2 (bound_lo J * bound_lo G) (bound_lo J * bound_hi G))
      as [M1 [[lM1 lM1'] PM1]].
    destruct (rational_max2 (bound_hi J * bound_lo G) (bound_hi J * bound_hi G))
      as [M2 [[lM2 lM2'] PM2]].
    destruct (rational_max2 M1 M2) as [M [[lM lM'] PM]].
    assert (Pm' : P m).
    { apply Pm; [apply Pm1|apply Pm2]; apply corner;
        first [apply in_bounds_lo|apply in_bounds_hi]. }
    assert (PM' : P M).
    { apply PM; [apply PM1|apply PM2]; apply corner;
        first [apply in_bounds_lo|apply in_bounds_hi]. }
    assert (lmD := fst (pos_minus_lt_compat_r m (' D)) (is_pos D)).
    assert (lMD := fst (pos_plus_lt_compat_r M (' D)) (is_pos D)).
    srefine (tr (I; tr (Build_CutBounds (y * z) (m - ' D) (M + ' D) _ _; _))).
    - apply tr; exists J; apply tr; exists G; apply belowproducts_corners.
      + exact (lt_le_trans _ _ _ lmD (transitivity lm lm1)).
      + exact (lt_le_trans _ _ _ lmD (transitivity lm lm1')).
      + exact (lt_le_trans _ _ _ lmD (transitivity lm' lm2)).
      + exact (lt_le_trans _ _ _ lmD (transitivity lm' lm2')).
    - apply tr; exists J; apply tr; exists G; apply aboveproducts_corners.
      + exact (le_lt_trans _ _ _ (transitivity lM1 lM) lMD).
      + exact (le_lt_trans _ _ _ (transitivity lM1' lM) lMD).
      + exact (le_lt_trans _ _ _ (transitivity lM2 lM') lMD).
      + exact (le_lt_trans _ _ _ (transitivity lM2' lM') lMD).
    - assert (c : forall s, in_bounds I s -> prod (q < s * (m - ' D)) (q < s * (M + ' D))).
      { intros s ins.
        assert (sT : prod (- T < s) (s < T))
          by exact (lt_le_trans _ _ _ lT (fst ins), le_lt_trans _ _ _ (snd ins) lT').
        assert (sD : s * ' D < q' - q).
        { rhs_V' exact (transport (fun w => w < _) (mult_comm _ _) lD).
          exact (pos_mult_lt_r (' D) (is_pos D) _ _ (snd sT)). }
        assert (sD' : - (q' - q) < s * ' D).
        { apply flip_lt_negate_l; rewrite negate_mult_distr_l.
          rhs_V' exact (transport (fun w => w < _) (mult_comm _ _) lD).
          exact (pos_mult_lt_r (' D) (is_pos D) _ _ (flip_lt_negate_l _ _ (fst sT))). }
        rewrite <- (minus_minus_cancel q' q), plus_mult_distr_l, plus_mult_distr_l.
        rewrite <- negate_mult_distr_r; split.
        - exact (lt_minus_lt _ _ _ _ (Pm' s ins) sD).
        - exact (plus_lt_compat _ _ _ _ (PM' s ins) sD'). }
      apply belowproducts_corners; cbn.
      + exact (fst (c _ (in_bounds_lo I))).
      + exact (snd (c _ (in_bounds_lo I))).
      + exact (fst (c _ (in_bounds_hi I))).
      + exact (snd (c _ (in_bounds_hi I))).
  Qed.

  Lemma mult_dedekindreals_assoc (x y z : R) : x * (y * z) = (x * y) * z.
  Proof.
    apply path_dedekindreals_lower; intros q p.
    - rewrite (mult_dedekindreals_comm (x * y) z), (mult_dedekindreals_comm x y).
      apply mult_dedekindreals_assoc_lower.
      rewrite (mult_dedekindreals_comm x (y * z)), (mult_dedekindreals_comm y z) in p; exact p.
    - exact (mult_dedekindreals_assoc_lower x y z q p).
  Qed.

  #[export] Instance iscring_dedekindreals : IsCRing R.
  Proof.
    repeat split; try exact _.
    - exact plus_dedekindreals_assoc.
    - exact plus_dedekindreals_0_l.
    - intros x; change (x + 0 = x); rewrite plus_dedekindreals_comm; apply plus_dedekindreals_0_l.
    - exact plus_dedekindreals_negate_l.
    - intros x; change (x + - x = 0); rewrite plus_dedekindreals_comm; apply plus_dedekindreals_negate_l.
    - exact plus_dedekindreals_comm.
    - exact mult_dedekindreals_assoc.
    - exact mult_dedekindreals_1_l.
    - intros x; change (x * 1 = x); rewrite mult_dedekindreals_comm; apply mult_dedekindreals_1_l.
    - exact mult_dedekindreals_comm.
    - exact mult_dedekindreals_plus_distr_l.
  Qed.

  (** ** The order and the ring structure *)

  Lemma lt_dedekindreals_iff_lower_minus (x y : R) : x < y <-> lower_cut (y - x) 0.
  Proof.
    assert (e : forall q : Q, - (0 - q) = q).
    { intros q; rewrite plus_0_l; apply negate_involutive. }
    split.
    - intros l; strip_truncations; destruct l as [q [u p]].
      apply tr; exists q; split; [exact p|].
      exact (transport (fun w => upper_cut x w) (e q)^ u).
    - intros p; strip_truncations; destruct p as [q [p u]].
      exact (tr (q; (transport (fun w => upper_cut x w) (e q) u, p))).
  Qed.

  Local Lemma plus_minus_plus_dedekind (x y z : R) : (z + y) - (z + x) = y - x.
  Proof.
    rewrite negate_plus_distr, (plus_comm z y), <- plus_assoc, (plus_assoc z).
    rewrite plus_negate_r, plus_0_l; reflexivity.
  Qed.

  #[export] Instance strictlyorderpreserving_plus_dedekindreals (z : R)
    : StrictlyOrderPreserving (z +).
  Proof.
    intros x y l; apply lt_dedekindreals_iff_lower_minus.
    rewrite plus_minus_plus_dedekind; exact (fst (lt_dedekindreals_iff_lower_minus x y) l).
  Qed.

  Local Lemma lt_dedekindreals_minus_zero (a b : R) : a < b -> a - b < 0.
  Proof.
    intros l; rewrite <- (plus_negate_r b), (plus_comm a), (plus_comm b).
    exact (strictly_order_preserving (- b +) _ _ l).
  Qed.

  Local Lemma lt_dedekindreals_zero_minus (a b : R) : b < a -> 0 < a - b.
  Proof.
    intros l; rewrite <- (plus_negate_r b), (plus_comm a), (plus_comm b).
    exact (strictly_order_preserving (- b +) _ _ l).
  Qed.

  Local Lemma lt_dedekindreals_from_minus (a b c : R) : a - b < c - b -> a < c.
  Proof.
    intros l; assert (l' := strictly_order_preserving (b +) _ _ l).
    rewrite !(plus_comm b), <- !plus_assoc, !plus_negate_l, !plus_0_r in l'; exact l'.
  Qed.

  Lemma pos_mult_dedekindreals (x y : R) : 0 < x -> 0 < y -> 0 < x * y.
  Proof.
    intros lx ly.
    apply (fst (lt_rational_dedekind_l 0 x)), (lower_cut_rounded x) in lx.
    apply (fst (lt_rational_dedekind_l 0 y)), (lower_cut_rounded y) in ly.
    assert (b := cut_upper_inhabited (isdedekindcut x)).
    assert (d := cut_upper_inhabited (isdedekindcut y)); strip_truncations.
    destruct lx as [s [ls lx]], ly as [t [lt ly]], b as [b ub], d as [d ud].
    apply (snd (lt_rational_dedekind_l 0 _)), tr.
    exists (Build_CutBounds x s b lx ub); apply tr; exists (Build_CutBounds y t d ly ud).
    intros u v [lu _] [lv _]; cbn in lu, lv.
    exact (pos_mult _ _ (lt_le_trans _ _ _ ls lu) (lt_le_trans _ _ _ lt lv)).
  Qed.

  (** If [x * z] is apart from zero, then so is [z]: bounds of [z] cannot contain zero. *)
  Lemma mult_dedekindreals_apart_zero_r (x z : R) : x * z ≶ 0 -> z ≶ 0.
  Proof.
    assert (sign : forall (I : CutBounds x) (J : CutBounds z),
               ~ (prod (bound_lo J <= 0) (0 <= bound_hi J)) -> z ≶ 0).
    { intros I J n; destruct (le_or_lt (bound_lo J) 0) as [l|l].
      - destruct (le_or_lt 0 (bound_hi J)) as [l'|l']; [destruct (n (l, l'))|].
        apply tr, inl, (snd (lt_rational_dedekind_r 0 z)).
        exact (upper_cut_lt z _ _ l' (bound_hi_upper J)).
      - apply tr, inr, (snd (lt_rational_dedekind_l 0 z)).
        exact (lower_cut_lt z _ _ l (bound_lo_lower J)). }
    intros a; strip_truncations; destruct a as [a|a].
    - apply (fst (lt_rational_dedekind_r 0 _)) in a; strip_truncations.
      destruct a as [I a]; strip_truncations; destruct a as [J a].
      apply (sign I J); intros i0.
      apply (irreflexivity (<) (0 : Q)).
      exact (transport (fun w => w < 0) (mult_0_r _) (a _ _ (in_bounds_lo I) i0)).
    - apply (fst (lt_rational_dedekind_l 0 _)) in a; strip_truncations.
      destruct a as [I a]; strip_truncations; destruct a as [J a].
      apply (sign I J); intros i0.
      apply (irreflexivity (<) (0 : Q)).
      exact (transport (fun w => 0 < w) (mult_0_r _) (a _ _ (in_bounds_lo I) i0)).
  Qed.

  Local Lemma apart_dedekindreals_iff_minus_zero (a b : R) : a ≶ b <-> a - b ≶ 0.
  Proof.
    split; intros p; strip_truncations; apply tr; destruct p as [l|l].
    - left; exact (lt_dedekindreals_minus_zero a b l).
    - right; exact (lt_dedekindreals_zero_minus a b l).
    - left; apply (lt_dedekindreals_from_minus a b b); rewrite plus_negate_r; exact l.
    - right; apply (lt_dedekindreals_from_minus b b a); rewrite plus_negate_r; exact l.
  Qed.

  #[export] Instance strongbinaryextensionality_mult_dedekindreals
    : StrongBinaryExtensionality (A:=R) (.*.).
  Proof.
    intros x1 y1 x2 y2 a.
    assert (c := cotransitive a (x1 * y2)); strip_truncations; apply tr; destruct c as [c|c].
    - right; apply apart_dedekindreals_iff_minus_zero.
      apply (mult_dedekindreals_apart_zero_r x1).
      rewrite plus_mult_distr_l, <- negate_mult_distr_r.
      exact (fst (apart_dedekindreals_iff_minus_zero _ _) c).
    - left; apply apart_dedekindreals_iff_minus_zero.
      apply (mult_dedekindreals_apart_zero_r y2).
      rewrite plus_mult_distr_l, <- negate_mult_distr_r, !(mult_comm y2).
      exact (fst (apart_dedekindreals_iff_minus_zero _ _) c).
  Qed.

  #[export] Instance fullpseudosemiringorder_dedekindreals
    : FullPseudoSemiRingOrder (_ : Le R) (_ : Lt R).
  Proof.
    apply from_full_pseudo_ring_order.
    - exact _.
    - exact _.
    - exact pos_mult_dedekindreals.
  Qed.

  (** ** The rationals as Dedekind reals *)

  Local Notation "[ q ]" := (rational_dedekind q).

  Lemma rational_dedekind_plus (q r : Q) : [q + r] = [q] + [r].
  Proof.
    symmetry; apply path_dedekindreals.
    - intros s p; strip_truncations; destruct p as [t [l l']]; cbn in l, l' |- *.
      rewrite (plus_conjugate_alt s t); exact (plus_lt_compat _ _ _ _ l l').
    - intros s p; strip_truncations; destruct p as [t [l l']]; cbn in l, l' |- *.
      rewrite (plus_conjugate_alt s t); exact (plus_lt_compat _ _ _ _ l l').
  Qed.

  Lemma rational_dedekind_mult (q r : Q) : [q * r] = [q] * [r].
  Proof.
    symmetry; apply path_dedekindreals.
    - intros s p; strip_truncations; destruct p as [I p]; strip_truncations; destruct p as [J p].
      exact (p q r (in_bounds_rational q I) (in_bounds_rational r J)).
    - intros s p; strip_truncations; destruct p as [I p]; strip_truncations; destruct p as [J p].
      exact (p q r (in_bounds_rational q I) (in_bounds_rational r J)).
  Qed.

  Lemma rational_dedekind_lt (q r : Q) : q < r <-> [q] < [r].
  Proof.
    symmetry; exact (lt_rational_dedekind_l q [r]).
  Qed.

  #[export] Instance issemiringpreserving_rational_dedekind : IsSemiRingPreserving rational_dedekind.
  Proof.
    repeat split.
    - exact rational_dedekind_plus.
    - exact rational_dedekind_mult.
  Qed.

  (** Between two Dedekind reals lies a rational. *)
  Lemma dedekindreals_archimedean (x y : R) : x < y -> hexists (fun q => prod (x < [q]) ([q] < y)).
  Proof.
    intros l; strip_truncations; destruct l as [q [u p]]; apply tr; exists q; split.
    - exact (snd (lt_rational_dedekind_r q x) u).
    - exact (snd (lt_rational_dedekind_l q y) p).
  Qed.

  #[export] Instance lt_0_1_dedekindreals : PropHolds (0 < (1 : R)).
  Proof.
    exact (fst (rational_dedekind_lt 0 1) lt_0_1).
  Qed.

  #[export] Instance apart_1_0_dedekindreals : PropHolds ((1 : R) ≶ 0).
  Proof.
    exact (tr (inr lt_0_1_dedekindreals)).
  Qed.

  (** ** Reciprocals *)

  Local Lemma recip_mult_cancel (u b : Q) : 0 < b -> u / b * b = u.
  Proof.
    intros bpos; rewrite <- mult_assoc, (mult_comm (/ b)), dec_recip_inverse.
    - apply mult_1_r.
    - apply lt_ne_flip, bpos.
  Qed.

  Local Lemma pos_quotient (u b : Q) : 0 < u -> 0 < b -> 0 < u / b.
  Proof.
    intros upos bpos; apply pos_mult; [exact upos|apply pos_dec_recip_compat, bpos].
  Qed.

  (** A positive real has a positive rational upper bound. *)
  Local Lemma merely_pos_upper (x : R) : 0 < x -> merely {b : Q & prod (0 < b) (x < [b])}.
  Proof.
    intros xpos; generalize (cut_upper_inhabited (isdedekindcut x)).
    apply Trunc_functor; intros [b ub]; exists b.
    assert (lb := snd (lt_rational_dedekind_r b x) ub); split; [|exact lb].
    exact (snd (rational_dedekind_lt 0 b) (lt_dedekindreals_trans _ _ _ xpos lb)).
  Qed.

  (** For a positive real [x], we have [q < 1 / x] when [q * x < 1] and [1 / x < r] when [1 < r * x]. *)
  Section pos_recip.
    Context (x : R) `{xpos : !PropHolds (0 < x)}.

    Local Definition pos_recip_lower (q : Q) : HProp := Build_HProp ([q] * x < 1).
    Local Definition pos_recip_upper (r : Q) : HProp := Build_HProp (1 < [r] * x).

    Lemma isdedekindcut_pos_recip : IsDedekindCut pos_recip_lower pos_recip_upper.
    Proof.
      split.
      - apply tr; exists 0; change (0 * x < 1); rewrite mult_0_l; exact lt_0_1_dedekindreals.
      - apply (fst (lt_rational_dedekind_l 0 x)), (lower_cut_rounded x) in xpos.
        strip_truncations; destruct xpos as [s [spos ls]].
        apply tr; exists (1 / s); change (1 < [1 / s] * x).
        assert (PropHolds (0 < [1 / s]))
          by exact (fst (rational_dedekind_lt 0 _) (pos_quotient 1 s lt_0_1 spos)).
        refine (transport (fun w => w < _) _
                  (strictly_order_preserving ([1 / s] *.) [s] x (snd (lt_rational_dedekind_l s x) ls))).
        rewrite <- rational_dedekind_mult, recip_mult_cancel; [reflexivity|exact spos].
      - intros q; split.
        + intros l; change ([q] * x < 1) in l.
          assert (t := dedekindreals_archimedean _ _ l).
          assert (b := merely_pos_upper x xpos); strip_truncations.
          destruct t as [t [lt lt']], b as [b [bpos lb]].
          apply (rational_dedekind_lt t 1) in lt'.
          pose (d := (1 - t) / b).
          assert (dpos : 0 < d) by exact (pos_quotient _ _ (snd (flip_pos_minus _ _) lt') bpos).
          assert (PropHolds (0 < [d])) by exact (fst (rational_dedekind_lt 0 d) dpos).
          apply tr; exists (q + d); split.
          * exact (fst (pos_plus_lt_compat_r q d) dpos).
          * change ([q + d] * x < 1).
            rewrite rational_dedekind_plus, plus_mult_distr_r.
            apply (lt_le_trans _ ([t] + [d] * [b])).
            -- apply plus_lt_compat; [exact lt|].
               exact (strictly_order_preserving ([d] *.) x [b] lb).
            -- rewrite <- rational_dedekind_mult, <- rational_dedekind_plus.
               unfold d; rewrite recip_mult_cancel, <- plus_conjugate_alt; [reflexivity|exact bpos].
        + intros l; revert l; apply Trunc_rec; intros [q' [l p]]; change ([q'] * x < 1) in p.
          change ([q] * x < 1).
          rhs_V' exact p.
          exact (strictly_order_preserving (.* x) _ _ (fst (rational_dedekind_lt q q') l)).
      - intros r; split.
        + intros l; change (1 < [r] * x) in l.
          assert (t := dedekindreals_archimedean _ _ l).
          assert (b := merely_pos_upper x xpos); strip_truncations.
          destruct t as [t [lt lt']], b as [b [bpos lb]].
          apply (rational_dedekind_lt 1 t) in lt.
          pose (d := (t - 1) / b).
          assert (dpos : 0 < d) by exact (pos_quotient _ _ (snd (flip_pos_minus _ _) lt) bpos).
          assert (PropHolds (0 < [d])) by exact (fst (rational_dedekind_lt 0 d) dpos).
          apply tr; exists (r - d); split.
          * exact (fst (pos_minus_lt_compat_r r d) dpos).
          * change (1 < [r - d] * x).
            rewrite rational_dedekind_plus, preserves_negate, plus_mult_distr_r.
            apply (le_lt_trans _ ([t] - [d] * [b])).
            -- rewrite <- rational_dedekind_mult, <- preserves_negate, <- rational_dedekind_plus.
               unfold d; rewrite recip_mult_cancel, minus_minus_cancel; [reflexivity|exact bpos].
            -- apply plus_lt_compat; [exact lt'|].
               rewrite <- negate_mult_distr_l.
               apply (snd (flip_lt_negate _ _)).
               exact (strictly_order_preserving ([d] *.) x [b] lb).
        + intros l; revert l; apply Trunc_rec; intros [r' [l p]]; change (1 < [r'] * x) in p.
          change (1 < [r] * x).
          lhs' exact p.
          exact (strictly_order_preserving (.* x) _ _ (fst (rational_dedekind_lt r' r) l)).
      - intros q r l l'.
        apply (rational_dedekind_lt q r).
        apply (strictly_order_reflecting (.* x)).
        exact (transitivity l l').
      - intros q r l.
        exact (cotransitive (strictly_order_preserving (.* x) _ _ (fst (rational_dedekind_lt q r) l)) 1).
    Qed.

    Definition pos_recip_dedekind : R := Build_DedekindReals _ _ isdedekindcut_pos_recip.

    Local Notation y := pos_recip_dedekind.

    (** We show [x * y = 1] by approximating [y] closely enough. *)
    Lemma pos_recip_dedekind_inverse : x * y = 1.
    Proof.
      apply (fst (tight_apart _ _)); intros a.
      assert (b := merely_pos_upper x xpos); revert a; apply (Trunc_rec (n:=-1)); intros a.
      revert b; apply (Trunc_rec (n:=-1)); intros [b [bpos lb]]; destruct a as [l|l].
      - apply (Trunc_rec (n:=-1) (A:={t : Q & prod (x * y < [t]) ([t] < 1)})); [|exact (dedekindreals_archimedean _ _ l)].
        intros [t [lt lt']]; apply (rational_dedekind_lt t 1) in lt'.
        pose (e := mkQpos ((1 - t) / b) (pos_quotient _ _ (snd (flip_pos_minus _ _) lt') bpos)).
        assert (PropHolds (0 < [' e])) by exact (fst (rational_dedekind_lt 0 _) (is_pos e)).
        apply (Trunc_rec (n:=-1) (A:={q : Q & {r : Q & prod (prod (lower_cut y q) (upper_cut y r)) (r - q < ' e)}}));
          [|exact (cut_approximate y e)].
        intros [q [r [[lq ur] lqr]]]; change (1 < [r] * x) in ur.
        apply (irreflexivity (<) (1 : R)), (transitivity ur).
        rewrite (mult_comm [r]).
        apply (lt_le_trans _ (x * (y + [' e]))).
        + apply (strictly_order_preserving (x *.)).
          apply (lt_le_trans _ [q + ' e]).
          * apply rational_dedekind_lt; rewrite (plus_comm q).
            exact (fst (flip_lt_minus_l q r (' e)) lqr).
          * rewrite rational_dedekind_plus; apply lt_le.
            exact (strictly_order_preserving (+ [' e]) _ _ (snd (lt_rational_dedekind_l q y) lq)).
        + rewrite plus_mult_distr_l; apply lt_le.
          apply (lt_le_trans _ ([t] + [b] * [' e])).
          * apply plus_lt_compat; [exact lt|exact (strictly_order_preserving (.* [' e]) _ _ lb)].
          * rewrite <- rational_dedekind_mult, <- rational_dedekind_plus; cbn.
            rewrite mult_comm, recip_mult_cancel, <- plus_conjugate_alt; [reflexivity|exact bpos].
      - apply (Trunc_rec (n:=-1) (A:={t : Q & prod (1 < [t]) ([t] < x * y)})); [|exact (dedekindreals_archimedean _ _ l)].
        intros [t [lt lt']]; apply (rational_dedekind_lt 1 t) in lt.
        pose (e := mkQpos ((t - 1) / b) (pos_quotient _ _ (snd (flip_pos_minus _ _) lt) bpos)).
        assert (PropHolds (0 < [' e])) by exact (fst (rational_dedekind_lt 0 _) (is_pos e)).
        apply (Trunc_rec (n:=-1) (A:={q : Q & {r : Q & prod (prod (lower_cut y q) (upper_cut y r)) (r - q < ' e)}}));
          [|exact (cut_approximate y e)].
        intros [q [r [[lq ur] lqr]]]; change ([q] * x < 1) in lq.
        apply (irreflexivity (<) (1 : R)); rhs_V' exact lq.
        rewrite (mult_comm [q]).
        apply (le_lt_trans _ (x * (y - [' e]))).
        + rewrite plus_mult_distr_l, <- negate_mult_distr_r; apply lt_le.
          apply (le_lt_trans _ ([t] - [b] * [' e])).
          * rewrite <- rational_dedekind_mult, <- preserves_negate, <- rational_dedekind_plus; cbn.
            rewrite mult_comm, recip_mult_cancel, minus_minus_cancel; [reflexivity|exact bpos].
          * apply plus_lt_compat; [exact lt'|].
            apply (snd (flip_lt_negate _ _)).
            exact (strictly_order_preserving (.* [' e]) _ _ lb).
        + apply (strictly_order_preserving (x *.)), flip_lt_minus_l.
          apply (transitivity (snd (lt_rational_dedekind_r r y) ur)).
          rewrite <- rational_dedekind_plus; apply rational_dedekind_lt; rewrite (plus_comm q).
          exact (fst (flip_lt_minus_l q r (' e)) lqr).
    Qed.
  End pos_recip.

  Arguments pos_recip_dedekind x {xpos}.

  (** A real apart from zero has a positive square, so we can take [1 / x = x * (1 / (x * x))]. *)
  #[local] Instance recip_dedekindreals : Recip R
    := fun x => x.1 * @pos_recip_dedekind (x.1 * x.1) (square_pos x.1 x.2).

  #[export] Instance isfield_dedekindreals : IsField R.
  Proof.
    split.
    - exact _.
    - exact _.
    - exact _.
    - exact _.
    - exact _.
    - intros [x a]; cbn; unfold recip, recip_dedekindreals; cbn.
      rewrite mult_assoc; apply pos_recip_dedekind_inverse.
  Qed.

  #[export] Instance orderedfield_dedekindreals : OrderedField R.
  Proof.
    split; exact _.
  Qed.

End dedekind.

Arguments cut_lower_inhabited {Q _ lower upper} _.
Arguments cut_upper_inhabited {Q _ lower upper} _.
Arguments cut_lower_rounded {Q _ lower upper} _ _.
Arguments cut_upper_rounded {Q _ lower upper} _ _.
Arguments cut_transitive {Q _ lower upper} _ _ _ _ _.
Arguments cut_located {Q _ lower upper} _ _ _ _.

(** The operations on [DedekindReals Q] use the same operations on [Q], so as instances they would make the search for, say, [Lt ?A] loop by taking [?A] to be [DedekindReals ?A'] over and over.  We therefore only use them when the type is known to be the Dedekind reals. *)
#[export] Hint Extern 1 (Lt (DedekindReals _)) => exact (lt_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Le (DedekindReals _)) => exact (le_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Apart (DedekindReals _)) => exact (apart_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Plus (DedekindReals _)) => exact (plus_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Negate (DedekindReals _)) => exact (negate_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Zero (DedekindReals _)) => exact (zero_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (One (DedekindReals _)) => exact (one_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Join (DedekindReals _)) => exact (join_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Meet (DedekindReals _)) => exact (meet_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Mult (DedekindReals _)) => exact (mult_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Recip (DedekindReals _)) => exact (recip_dedekindreals _) : typeclass_instances.

(** ** The Archimedean property and Cauchy completeness *)

(** We use a new section, so that the inclusion of the rationals into fields is not restricted to the universes used above: the Dedekind reals live in a universe above that of [Q]. *)
Section complete.
  Context `{Funext} `{Univalence}.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}
    {Qroundup : RoundUpStrict@{_ UQ _ UQ} Q}.

  Local Notation R := (DedekindReals Q (Qlt:=Qlt)).
  Local Notation "[ q ]" := (rational_dedekind Q q).

  (** The inclusion of the rationals into an ordered field is the unique semiring morphism, so on the Dedekind reals it is [rational_dedekind]. *)
  Lemma rationals_to_field_dedekindreals (q : Q) : rationals_to_field Q R q = [q].
  Proof.
    exact (rationals_initial (h:=rational_dedekind Q) q).
  Qed.

  #[export] Instance archimedean_dedekindreals : ArchimedeanProperty Q R.
  Proof.
    intros x y l; generalize (dedekindreals_archimedean Q x y l); apply Trunc_functor.
    intros [q lq]; exists q.
    exact (transport (fun z => prod (x < z) (z < y)) (rationals_initial (h:=rational_dedekind Q) q)^ lq).
  Qed.

  (** ** Cauchy completeness *)

  Section limit.
    Context (x : nat -> R) (M : Qpos Q -> nat) `{!CauchyModulus Q R x M}.

    (** Two terms beyond [M e] are [e]-close, so their cuts are too. *)
    Local Lemma modulus_cut_lt (e : Qpos Q) (m n : nat) (a b : Q)
      : (M e <= m)%nat -> (M e <= n)%nat -> lower_cut Q (x m) a -> upper_cut Q (x n) b -> a < b + ' e.
    Proof.
      intros lm ln la ub.
      assert (c := snd (cauchy_convergence Q R x e m n lm ln)).
      apply flip_lt_minus_l in c; unfold cast in c.
      rewrite (rationals_initial (h:=rational_dedekind Q)) in c.
      apply (snd (rational_dedekind_lt Q _ _)); rewrite plus_comm, (rational_dedekind_plus Q (Qroundup:=Qroundup)).
      lhs' exact (snd (lt_rational_dedekind_l Q a (x m)) la).
      lhs' exact c.
      exact (strictly_order_preserving ([' e] +) _ _ (snd (lt_rational_dedekind_r Q b (x n)) ub)).
    Qed.

    (** The limit: [q < l] when [q + e + d < x (M e)] for some [e] and [d], and dually. *)
    Local Definition limit_lower (q : Q) : HProp
      := Build_HProp (hexists (fun e : Qpos Q => hexists (fun d : Qpos Q =>
                       lower_cut Q (x (M e)) (q + ' e + ' d)))).
    Local Definition limit_upper (r : Q) : HProp
      := Build_HProp (hexists (fun e : Qpos Q => hexists (fun d : Qpos Q =>
                       upper_cut Q (x (M e)) (r - ' e - ' d)))).

    Local Lemma plus_minus_pos (q : Q) (e d : Qpos Q) : q - ' e - ' d + ' e + ' d = q.
    Proof.
      rewrite <- !plus_assoc, (plus_comm (' e) (' d)), (plus_assoc (- ' d)), plus_negate_l, plus_0_l.
      rewrite plus_negate_l; apply plus_0_r.
    Qed.

    Local Lemma plus_plus_minus (q : Q) (e d : Qpos Q) : q + ' e + ' d - ' e - ' d = q.
    Proof.
      rewrite <- !plus_assoc, (plus_assoc (' d) (- ' e)), (plus_comm (' d) (- ' e)).
      rewrite <- (plus_assoc (- ' e)), !plus_negate_r, plus_0_r, plus_negate_r; apply plus_0_r.
    Qed.

    Local Lemma plus_half_shift (q : Q) (e d : Qpos Q)
      : q + ' (d / 2) + ' e + ' (d / 2) = q + ' e + ' d.
    Proof.
      rhs exact (ap (fun z => q + ' e + ' z) (pos_split2 d)).
      change (q + ' (d / 2) + ' e + ' (d / 2) = q + ' e + (' (d / 2) + ' (d / 2))).
      rewrite <- (plus_assoc q (' (d / 2)) (' e)), (plus_comm (' (d / 2)) (' e)), plus_assoc.
      apply (plus_assoc _ (' (d / 2)) (' (d / 2)))^.
    Qed.

    Local Lemma minus_half_shift (r : Q) (e d : Qpos Q)
      : r - ' (d / 2) - ' e - ' (d / 2) = r - ' e - ' d.
    Proof.
      rhs exact (ap (fun z => r - ' e - ' z) (pos_split2 d)).
      change (r - ' (d / 2) - ' e - ' (d / 2) = r - ' e - (' (d / 2) + ' (d / 2))).
      rewrite negate_plus_distr.
      rewrite <- (plus_assoc r (- ' (d / 2)) (- ' e)), (plus_comm (- ' (d / 2)) (- ' e)), plus_assoc.
      apply (plus_assoc _ (- ' (d / 2)) (- ' (d / 2)))^.
    Qed.

    (** Two consequences of [modulus_cut_lt] that give transitivity of the limit cut. *)
    Local Lemma limit_transitive_aux (q s : Q) (e d : Qpos Q) : q + ' e + ' d < s + ' e -> q < s.
    Proof.
      intros l.
      rewrite <- (plus_assoc q), (plus_comm (' e)), plus_assoc in l.
      apply (strictly_order_reflecting (+ ' e)) in l.
      exact (transitivity (fst (pos_plus_lt_compat_r q (' d)) (is_pos d)) l).
    Qed.

    Local Lemma limit_transitive_aux' (q r : Q) (e d e' d' : Qpos Q)
      : q + ' e + ' d < r - ' e' - ' d' + ' e' -> q < r.
    Proof.
      intros l.
      rewrite <- (plus_assoc (r - ' e')), (plus_comm (- ' d')), plus_assoc in l.
      rewrite <- (plus_assoc r), plus_negate_l, plus_0_r in l.
      lhs' exact (fst (pos_plus_lt_compat_r q (' e)) (is_pos e)).
      lhs' exact (fst (pos_plus_lt_compat_r _ (' d)) (is_pos d)).
      lhs' exact l.
      exact (fst (pos_minus_lt_compat_r r (' d')) (is_pos d')).
    Qed.

    Lemma isdedekindcut_limit : IsDedekindCut Q limit_lower limit_upper.
    Proof.
      split.
      - assert (a := cut_lower_inhabited (isdedekindcut Q (x (M 1)))); strip_truncations.
        destruct a as [a la]; apply tr; exists (a - ' 1 - ' 1); apply tr; exists 1; apply tr; exists 1.
        rewrite plus_minus_pos; exact la.
      - assert (b := cut_upper_inhabited (isdedekindcut Q (x (M 1)))); strip_truncations.
        destruct b as [b ub]; apply tr; exists (b + ' 1 + ' 1); apply tr; exists 1; apply tr; exists 1.
        rewrite plus_plus_minus; exact ub.
      - intros q; split.
        + intros p; strip_truncations; destruct p as [e p]; strip_truncations; destruct p as [d p].
          apply tr; exists (q + ' (d / 2)); split; [apply pos_plus_lt_compat_r, is_pos|].
          apply tr; exists e; apply tr; exists (d / 2).
          rewrite plus_half_shift; exact p.
        + intros p; strip_truncations; destruct p as [q' [l p]]; strip_truncations.
          destruct p as [e p]; strip_truncations; destruct p as [d p].
          apply tr; exists e; apply tr; exists d.
          refine (lower_cut_lt Q _ _ _ _ p).
          apply (strictly_order_preserving (+ ' d)), (strictly_order_preserving (+ ' e)), l.
      - intros r; split.
        + intros p; strip_truncations; destruct p as [e p]; strip_truncations; destruct p as [d p].
          apply tr; exists (r - ' (d / 2)); split; [apply pos_minus_lt_compat_r, is_pos|].
          apply tr; exists e; apply tr; exists (d / 2).
          rewrite minus_half_shift; exact p.
        + intros p; strip_truncations; destruct p as [r' [l p]]; strip_truncations.
          destruct p as [e p]; strip_truncations; destruct p as [d p].
          apply tr; exists e; apply tr; exists d.
          refine (upper_cut_lt Q _ _ _ _ p).
          apply (strictly_order_preserving (+ - ' d)), (strictly_order_preserving (+ - ' e)), l.
      - intros q r p p'; strip_truncations.
        destruct p as [e p], p' as [e' p']; strip_truncations.
        destruct p as [d p], p' as [d' p'].
        destruct (leq_dichotomy (M e) (M e')) as [lM|lM].
        + rhs_V' exact (fst (pos_minus_lt_compat_r r (' e')) (is_pos e')).
          rhs_V' exact (fst (pos_minus_lt_compat_r _ (' d')) (is_pos d')).
          exact (limit_transitive_aux q _ e d (modulus_cut_lt e _ _ _ _ (leq_refl _) lM p p')).
        + exact (limit_transitive_aux' q r e d e' d'
                   (modulus_cut_lt e' _ _ _ _ (leq_lt lM) (leq_refl _) p p')).
      - (* The cut of [x (M (e / 2))] approximates the limit cut up to [e]. *)
        rapply (located_from_approximations Q (Tr (-1))
                  (fun e => lower_cut Q (x (M (e / 2)))) (fun e => upper_cut Q (x (M (e / 2))))).
        + exact (fun e => cut_located (isdedekindcut Q (x (M (e / 2))))).
        + intros e q c; apply tr; exists (e / 2); apply tr; exists (e / 2).
          rewrite <- plus_assoc.
          exact (transport (fun z => lower_cut Q (x (M (e / 2))) (q + ' z)) (pos_split2 e) c).
        + intros e r c; apply tr; exists (e / 2); apply tr; exists (e / 2).
          rewrite <- plus_assoc, <- negate_plus_distr.
          exact (transport (fun z => upper_cut Q (x (M (e / 2))) (r - ' z)) (pos_split2 e) c).
    Qed.

    Definition limit_dedekind : R := Build_DedekindReals Q limit_lower limit_upper isdedekindcut_limit.

    Local Lemma rational_dedekind_minus (r h : Q) : [r - h] = [r] - [h].
    Proof.
      rewrite (rational_dedekind_plus Q (Qroundup:=Qroundup)); apply ap.
      exact (preserves_negate (f:=rational_dedekind Q) h).
    Qed.

    Local Lemma not_lt_flip_dedekind (a b : Q) : b < a -> ~ (a < b).
    Proof.
      intros l l'; exact (irreflexivity (<) a (transitivity l' l)).
    Qed.

    (** Beyond [M (e / 2)], the terms are at most [e / 2] above the limit. *)
    Local Lemma limit_minus_le (e : Qpos Q) (n : nat) : leq (M (e / 2)) n
      -> limit_dedekind - x n <= [' (e / 2)].
    Proof.
      intros ln; apply le_iff_not_lt_flip; intros l.
      apply flip_lt_minus_r in l.
      apply (Trunc_rec (n:=-1) (A:={r : Q & prod ([' (e / 2)] + x n < [r]) ([r] < limit_dedekind)}));
        [|exact (dedekindreals_archimedean Q _ _ l)].
      intros [r [lr lr']].
      apply (fst (lt_rational_dedekind_l Q r _)) in lr'.
      rewrite plus_comm in lr; apply flip_lt_minus_r in lr.
      rewrite <- rational_dedekind_minus in lr; apply (fst (lt_rational_dedekind_r Q _ _)) in lr.
      revert lr'; apply (Trunc_rec (n:=-1)); intros [e' p]; revert p.
      apply (Trunc_rec (n:=-1)); intros [d' p].
      destruct (leq_dichotomy (M (e / 2)) (M e')) as [lM|lM].
      - refine (not_lt_flip_dedekind _ _ _ (modulus_cut_lt (e / 2) _ _ _ _ lM ln p lr)).
        rewrite <- plus_assoc, plus_negate_l, plus_0_r.
        exact (transitivity (fst (pos_plus_lt_compat_r r (' e')) (is_pos e'))
                 (fst (pos_plus_lt_compat_r _ (' d')) (is_pos d'))).
      - refine (not_lt_flip_dedekind _ _ _
                  (modulus_cut_lt e' _ _ _ _ (leq_refl _) (leq_trans (leq_lt lM) ln) p lr)).
        rhs_V' exact (fst (pos_plus_lt_compat_r _ (' d')) (is_pos d')).
        apply (strictly_order_preserving (+ ' e')), pos_minus_lt_compat_r, is_pos.
    Qed.

    (** Beyond [M (e / 2)], the terms are at most [e / 2] below the limit. *)
    Local Lemma minus_limit_le (e : Qpos Q) (n : nat) : leq (M (e / 2)) n
      -> x n - limit_dedekind <= [' (e / 2)].
    Proof.
      intros ln; apply le_iff_not_lt_flip; intros l.
      apply flip_lt_minus_r in l.
      apply (Trunc_rec (n:=-1) (A:={r : Q & prod ([' (e / 2)] + limit_dedekind < [r]) ([r] < x n)}));
        [|exact (dedekindreals_archimedean Q _ _ l)].
      intros [r [lr lr']].
      apply (fst (lt_rational_dedekind_l Q r _)) in lr'.
      rewrite plus_comm in lr; apply flip_lt_minus_r in lr.
      rewrite <- rational_dedekind_minus in lr; apply (fst (lt_rational_dedekind_r Q _ _)) in lr.
      revert lr; apply (Trunc_rec (n:=-1)); intros [e' p]; revert p.
      apply (Trunc_rec (n:=-1)); intros [d' p].
      destruct (leq_dichotomy (M (e / 2)) (M e')) as [lM|lM].
      - refine (not_lt_flip_dedekind _ _ _ (modulus_cut_lt (e / 2) _ _ _ _ ln lM lr' p)).
        apply (lt_le_trans _ (r - ' (e / 2) + ' (e / 2))).
        + apply (strictly_order_preserving (+ ' (e / 2))).
          exact (transitivity (fst (pos_minus_lt_compat_r _ (' d')) (is_pos d'))
                   (fst (pos_minus_lt_compat_r _ (' e')) (is_pos e'))).
        + rewrite <- plus_assoc, plus_negate_l, plus_0_r; apply reflexivity.
      - refine (not_lt_flip_dedekind _ _ _
                  (modulus_cut_lt e' _ _ _ _ (leq_trans (leq_lt lM) ln) (leq_refl _) lr' p)).
        apply (lt_le_trans _ (r - ' (e / 2) - ' e' + ' e')).
        + apply (strictly_order_preserving (+ ' e')), pos_minus_lt_compat_r, is_pos.
        + rewrite <- plus_assoc, plus_negate_l, plus_0_r.
          apply lt_le, pos_minus_lt_compat_r, is_pos.
    Qed.

    Lemma islimit_limit_dedekind : IsLimit Q R x limit_dedekind.
    Proof.
      intros e; apply tr; exists (M (e / 2)); intros n ln; unfold cast.
      rewrite (rationals_initial (h:=rational_dedekind Q)).
      assert (half : [' (e / 2)] < [' e]).
      { apply rational_dedekind_lt, qpos_half_lt. }
      split.
      - rewrite negate_swap_r; apply (snd (flip_lt_negate _ _)).
        exact (le_lt_trans _ _ _ (minus_limit_le e n ln) half).
      - exact (le_lt_trans _ _ _ (limit_minus_le e n ln) half).
    Qed.
  End limit.

  (** The Dedekind reals are Cauchy complete, with the limit given by [limit_dedekind]. *)
  #[export] Instance iscomplete_dedekindreals : IsComplete Q R.
  Proof.
    intros x M H'; exists (limit_dedekind x M); exact (islimit_limit_dedekind x M).
  Qed.
End complete.
