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

  (** Cotransitivity with a rational: by roundedness, [q < y] gives [q < q' < y], and locatedness of [x] at [q < q'] gives [q < x] or [x < y]. *)
  Lemma lower_cut_cotrans (x y : R) (q : Q) : lower_cut y q -> hor (lower_cut x q) (x < y).
  Proof.
    intros p.
    apply (lower_cut_rounded y q) in p; strip_truncations; destruct p as [q' [ltqq' p]].
    assert (c := cut_located (isdedekindcut x) q q' ltqq'); strip_truncations.
    apply tr; destruct c as [lq|uq'].
    - left; exact lq.
    - right; apply tr; exact (q'; (uq', p)).
  Qed.

  Lemma upper_cut_cotrans (x y : R) (r : Q) : upper_cut x r -> hor (upper_cut y r) (x < y).
  Proof.
    intros p.
    apply (upper_cut_rounded x r) in p; strip_truncations; destruct p as [r' [ltr'r p]].
    assert (c := cut_located (isdedekindcut y) r' r ltr'r); strip_truncations.
    apply tr; destruct c as [lr'|ur].
    - right; apply tr; exact (r'; (p, lr')).
    - left; exact ur.
  Qed.

  (** ** Paths between Dedekind reals *)

  Definition path_dedekindreals_cuts (x y : R)
    : lower_cut x = lower_cut y -> upper_cut x = upper_cut y -> x = y.
  Proof.
    destruct x as [lx ux c], y as [ly uy c']; cbn.
    intros p q; destruct p, q; exact (ap (Build_DedekindReals lx ux) (path_ishprop c c')).
  Defined.

  #[export] Instance ishset_dedekindreals : IsHSet R.
  Proof.
    apply (istrunc_equiv_istrunc {lower : Q -> HProp & {upper : Q -> HProp & IsDedekindCut lower upper}}).
    - make_equiv.
    - exact _.
  Qed.

  (** By locatedness, an inclusion of upper cuts gives the reverse inclusion of lower cuts, and vice versa. *)
  Lemma lower_cut_incl_rev (x y : R) (uu : forall r, upper_cut x r -> upper_cut y r)
    (q : Q) : lower_cut y q -> lower_cut x q.
  Proof.
    intros p; assert (c := lower_cut_cotrans x y q p); strip_truncations.
    destruct c as [lq|ltxy]; [exact lq|].
    strip_truncations; destruct ltxy as [s [us ls]].
    destruct (cut_disjoint y s ls (uu s us)).
  Qed.

  Lemma upper_cut_incl_rev (x y : R) (ll : forall q, lower_cut x q -> lower_cut y q)
    (r : Q) : upper_cut y r -> upper_cut x r.
  Proof.
    intros p; assert (c := upper_cut_cotrans y x r p); strip_truncations.
    destruct c as [ur|ltyx]; [exact ur|].
    strip_truncations; destruct ltyx as [s [us ls]].
    destruct (cut_disjoint y s (ll s ls) us).
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

  Definition path_dedekindreals_lower (x y : R)
    (l : forall q, lower_cut x q -> lower_cut y q) (l' : forall q, lower_cut y q -> lower_cut x q)
    : x = y
    := path_dedekindreals x y l (upper_cut_incl_rev y x l').

  (** ** Approximation *)

  (** We find bounds of [x] less than [e] apart by walking up from a lower bound in steps of [d = e / 3], using locatedness at each step, until we pass an upper bound. *)
  Section approximate.
    Context (x : R) (e : Qpos Q).

    Local Definition close_bounds : Type
      := {a : Q & {b : Q & prod (prod (lower_cut x a) (upper_cut x b)) (b - a < ' e)}}.

    Local Definition d : Q := ' (e / 3).

    Local Lemma approximate_step (a : Q) : lower_cut x a -> hor close_bounds (lower_cut x (a + d)).
    Proof.
      intros la.
      assert (lt : a + d < a + d + d) by apply pos_plus_lt_compat_r, pos_is_pos.
      assert (c := cut_located (isdedekindcut x) _ _ lt); strip_truncations.
      apply tr; destruct c as [lad|uadd].
      - right; exact lad.
      - left; exists a, (a + d + d); split; [exact (la, uadd)|].
        rewrite <- (plus_assoc a d d), <- plus_conjugate.
        apply qpos_two_thirds_lt.
    Qed.

    Local Lemma approximate_walk (a : Q) (la : lower_cut x a) (k : nat)
      : hor close_bounds (lower_cut x (a + nQ k * d)).
    Proof.
      induction k as [|k IH].
      - apply tr, inr; change (nQ 0) with 0; rewrite mult_0_l, plus_0_r; exact la.
      - strip_truncations; destruct IH as [close|lk]; [exact (tr (inl close))|].
        assert (p : a + nQ (S k) * d = a + nQ k * d + d).
        { rewrite nat_to_semiring_succ, (plus_comm 1), plus_mult_distr_r, mult_1_l.
          apply plus_assoc. }
        rewrite p; exact (approximate_step _ lk).
    Qed.

    Lemma cut_approximate
      : merely {a : Q & {b : Q & prod (prod (lower_cut x a) (upper_cut x b)) (b - a < ' e)}}.
    Proof.
      assert (a0 := cut_lower_inhabited (isdedekindcut x)).
      assert (b0 := cut_upper_inhabited (isdedekindcut x)).
      strip_truncations; destruct a0 as [a la], b0 as [b ub].
      destruct (round_up_strict Q ((b - a) / d)) as [N ltN].
      assert (ltb : b < a + nQ N * d).
      { rewrite plus_comm; apply flip_lt_minus_l.
        apply (flip_lt_mult_dec_recip_l (b - a) (nQ N) d); [apply pos_is_pos|exact ltN]. }
      assert (c := approximate_walk a la N); strip_truncations.
      destruct c as [close|laN]; [exact (tr close)|].
      destruct (lt_flip _ _ ltb (cut_transitive (isdedekindcut x) _ _ laN ub)).
    Qed.

  End approximate.

  (** ** Rationals *)

  Local Definition Qlt_hprop (q r : Q) : HProp := Build_HProp (q < r).

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
    - intros nl q p; assert (c := lower_cut_cotrans y x q p); strip_truncations.
      destruct c as [lq|ltyx]; [exact lq|destruct (nl ltyx)].
  Qed.

  (** ** Addition *)

  (** [q < x + y] when [q = s + t] with [s < x] and [t < y], and dually. *)
  Section plus.
    Context (x y : R).

    Local Definition plus_lower (q : Q) : HProp
      := Build_HProp (hexists (fun s => prod (lower_cut x s) (lower_cut y (q - s)))).
    Local Definition plus_upper (r : Q) : HProp
      := Build_HProp (hexists (fun s => prod (upper_cut x s) (upper_cut y (r - s)))).

    Local Lemma plus_lower_rounded (q : Q)
      : plus_lower q <-> hexists (fun q' => prod (q < q') (plus_lower q')).
    Proof.
      split.
      - intros p; strip_truncations; destruct p as [s [ls lt]].
        apply (lower_cut_rounded y) in lt; strip_truncations; destruct lt as [t [ltt lt]].
        apply tr; exists (s + t); split.
        + rewrite (plus_conjugate_alt q s); apply (strictly_order_preserving (s +)), ltt.
        + apply tr; exists s; rewrite <- plus_conjugate; exact (ls, lt).
      - intros p; strip_truncations; destruct p as [q' [ltqq' p]]; strip_truncations.
        destruct p as [s [ls lt]]; apply tr; exists s; split; [exact ls|].
        apply (lower_cut_lt y _ (q' - s)); [|exact lt].
        apply (strictly_order_preserving (+ (- s))), ltqq'.
    Qed.

    Local Lemma plus_upper_rounded (r : Q)
      : plus_upper r <-> hexists (fun r' => prod (r' < r) (plus_upper r')).
    Proof.
      split.
      - intros p; strip_truncations; destruct p as [s [us ut]].
        apply (upper_cut_rounded y) in ut; strip_truncations; destruct ut as [t [ltt ut]].
        apply tr; exists (s + t); split.
        + rewrite (plus_conjugate_alt r s); apply (strictly_order_preserving (s +)), ltt.
        + apply tr; exists s; rewrite <- plus_conjugate; exact (us, ut).
      - intros p; strip_truncations; destruct p as [r' [ltr'r p]]; strip_truncations.
        destruct p as [s [us ut]]; apply tr; exists s; split; [exact us|].
        apply (upper_cut_lt y _ (r' - s)); [|exact ut].
        apply (strictly_order_preserving (+ (- s))), ltr'r.
    Qed.

    Local Lemma lt_minus_swap (q r a b : Q) : b - a < r - q -> q - a < r - b.
    Proof.
      intros l.
      rewrite <- (plus_minus_telescope q b a), <- (plus_minus_telescope r q b).
      rewrite (plus_comm (q - b)).
      apply (strictly_order_preserving (+ (q - b))), l.
    Qed.

    (** For locatedness at [q < r], we take bounds [a < x < b] with [b - a < r - q] and locate [y] at [q - a < r - b]. *)
    Local Lemma plus_located (q r : Q) : q < r -> hor (plus_lower q) (plus_upper r).
    Proof.
      intros l.
      assert (c := cut_approximate x (Qpos_diff q r l)); strip_truncations.
      destruct c as [a [b [[la ub] lab]]].
      assert (l' : q - a < r - b) by exact (lt_minus_swap q r a b lab).
      assert (c := cut_located (isdedekindcut y) _ _ l'); strip_truncations.
      apply tr; destruct c as [c|c].
      - left; apply tr; exact (a; (la, c)).
      - right; apply tr; exact (b; (ub, c)).
    Qed.

    Lemma isdedekindcut_plus : IsDedekindCut plus_lower plus_upper.
    Proof.
      split.
      - assert (a := cut_lower_inhabited (isdedekindcut x)).
        assert (b := cut_lower_inhabited (isdedekindcut y)).
        strip_truncations; destruct a as [a la], b as [b lb].
        apply tr; exists (a + b); apply tr; exists a.
        rewrite <- plus_conjugate; exact (la, lb).
      - assert (a := cut_upper_inhabited (isdedekindcut x)).
        assert (b := cut_upper_inhabited (isdedekindcut y)).
        strip_truncations; destruct a as [a ua], b as [b ub].
        apply tr; exists (a + b); apply tr; exists a.
        rewrite <- plus_conjugate; exact (ua, ub).
      - exact plus_lower_rounded.
      - exact plus_upper_rounded.
      - intros q r p p'; strip_truncations.
        destruct p as [s [ls lt]], p' as [s' [us' ut']].
        rewrite (plus_conjugate_alt q s), (plus_conjugate_alt r s').
        apply plus_lt_compat.
        + exact (cut_transitive (isdedekindcut x) _ _ ls us').
        + exact (cut_transitive (isdedekindcut y) _ _ lt ut').
      - exact plus_located.
    Qed.
  End plus.

  #[local] Instance plus_dedekindreals : Plus R
    := fun x y => Build_DedekindReals _ _ (isdedekindcut_plus x y).

  (** ** Negation *)

  Lemma isdedekindcut_negate (x : R)
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
        * apply flip_lt_negate_r, l.
        * rewrite negate_involutive; exact p.
      + intros p; strip_truncations; destruct p as [q' [l p]].
        apply (upper_cut_lt x _ (- q')); [|exact p].
        exact (snd (flip_lt_negate q q') l).
    - intros r; split.
      + intros p; apply (lower_cut_rounded x) in p; strip_truncations.
        destruct p as [q [l p]]; apply tr; exists (- q); split.
        * apply flip_lt_negate_l, l.
        * rewrite negate_involutive; exact p.
      + intros p; strip_truncations; destruct p as [r' [l p]].
        apply (lower_cut_lt x _ (- r')); [|exact p].
        exact (snd (flip_lt_negate r' r) l).
    - intros q r u l.
      apply (fst (flip_lt_negate q r)), (cut_transitive (isdedekindcut x)); [exact l|exact u].
    - intros q r l.
      assert (c := cut_located (isdedekindcut x) (- r) (- q) (snd (flip_lt_negate q r) l)).
      strip_truncations; apply tr; destruct c as [c|c]; [right|left]; exact c.
  Qed.

  #[local] Instance negate_dedekindreals : Negate R
    := fun x => Build_DedekindReals _ _ (isdedekindcut_negate x).

  #[local] Instance zero_dedekindreals : Zero R := rational_dedekind 0.
  #[local] Instance one_dedekindreals : One R := rational_dedekind 1.

  (** ** The additive group *)

  Local Lemma minus_minus_cancel (q s : Q) : q - (q - s) = s.
  Proof.
    rewrite negate_plus_distr, negate_involutive, plus_assoc, plus_negate_r; apply plus_0_l.
  Qed.

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
      + apply tr; exists s; rewrite <- plus_conjugate; exact (ls, lt).
      + rewrite minus_plus_distr; exact lu.
    - intros r p; strip_truncations; destruct p as [s [us p]]; strip_truncations.
      destruct p as [t [ut uu]].
      apply tr; exists (s + t); split.
      + apply tr; exists s; rewrite <- plus_conjugate; exact (us, ut).
      + rewrite minus_plus_distr; exact uu.
  Qed.

  (** [q < 0 + x] when [q - s < x] for some [s < 0], so [q < q - s < x], and dually. *)
  Lemma plus_dedekindreals_0_l (x : R) : 0 + x = x.
  Proof.
    apply path_dedekindreals.
    - intros q p; strip_truncations; destruct p as [s [sneg lx]].
      assert (lt : q < q - s) by apply pos_plus_lt_compat_r, flip_neg_negate, sneg.
      exact (lower_cut_lt x _ _ lt lx).
    - intros r p; strip_truncations; destruct p as [s [spos ux]].
      assert (lt : r - s < r) by apply pos_minus_lt_compat_r, spos.
      exact (upper_cut_lt x _ _ lt ux).
  Qed.

  (** [q < - x + x] when [s < - x] and [q - s < x], so [q - s < - s], and dually. *)
  Lemma plus_dedekindreals_negate_l (x : R) : - x + x = 0.
  Proof.
    apply path_dedekindreals.
    - intros q p; strip_truncations; destruct p as [s [us lx]]; cbn.
      apply (strictly_order_reflecting (+ (- s))); rewrite plus_0_l.
      exact (cut_transitive (isdedekindcut x) _ _ lx us).
    - intros r p; strip_truncations; destruct p as [s [ls ux]]; cbn.
      apply (strictly_order_reflecting (+ (- s))); rewrite plus_0_l.
      exact (cut_transitive (isdedekindcut x) _ _ ls ux).
  Qed.

  (** ** The strict order *)

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
    assert (c := upper_cut_cotrans x z q uq); strip_truncations.
    apply tr; destruct c as [uzq|ltxz].
    - right; apply tr; exact (q; (uzq, lq)).
    - left; exact ltxz.
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

  (** The minimum and the maximum of two rationals, characterized by any property they both have. *)
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

  (** The join has the union of the lower cuts and the intersection of the upper cuts.  For the upper cuts, we use that two upper bounds of [x] and [y] have a maximum which is an upper bound of both. *)
  Section join.
    Context (x y : R).

    Local Definition join_lower (q : Q) : HProp := Build_HProp (hor (lower_cut x q) (lower_cut y q)).
    Local Definition join_upper (r : Q) : HProp := Build_HProp (prod (upper_cut x r) (upper_cut y r)).

    Local Lemma upper_cut_max (b b' : Q) : upper_cut x b -> upper_cut y b'
      -> {m : Q & prod (join_upper m) (forall P : Q -> Type, P b -> P b' -> P m)}.
    Proof.
      intros ub ub'; destruct (rational_max2 b b') as [m [[lbm lb'm] Pm]].
      exact (m; ((upper_cut_le x m b lbm ub, upper_cut_le y m b' lb'm ub'), Pm)).
    Qed.

    Local Lemma join_lower_rounded (q : Q)
      : join_lower q <-> hexists (fun q' => prod (q < q') (join_lower q')).
    Proof.
      split.
      - intros p; strip_truncations; destruct p as [p|p].
        + apply (lower_cut_rounded x q) in p; strip_truncations; destruct p as [q' [l p]].
          exact (tr (q'; (l, tr (inl p)))).
        + apply (lower_cut_rounded y q) in p; strip_truncations; destruct p as [q' [l p]].
          exact (tr (q'; (l, tr (inr p)))).
      - intros p; strip_truncations; destruct p as [q' [l p]]; strip_truncations.
        apply tr; destruct p as [p|p]; [left|right]; exact (lower_cut_lt _ q q' l p).
    Qed.

    Local Lemma join_upper_rounded (r : Q)
      : join_upper r <-> hexists (fun r' => prod (r' < r) (join_upper r')).
    Proof.
      split.
      - intros [p p'].
        apply (upper_cut_rounded x r) in p; apply (upper_cut_rounded y r) in p'.
        strip_truncations; destruct p as [s [l p]], p' as [s' [l' p']].
        destruct (upper_cut_max s s' p p') as [m [um Pm]].
        exact (tr (m; (Pm (fun m => m < r) l l', um))).
      - intros p; strip_truncations; destruct p as [r' [l [p p']]].
        exact (upper_cut_lt x _ _ l p, upper_cut_lt y _ _ l p').
    Qed.

    Lemma isdedekindcut_join : IsDedekindCut join_lower join_upper.
    Proof.
      split.
      - assert (a := cut_lower_inhabited (isdedekindcut x)); strip_truncations.
        destruct a as [a la]; exact (tr (a; tr (inl la))).
      - assert (b := cut_upper_inhabited (isdedekindcut x)).
        assert (b' := cut_upper_inhabited (isdedekindcut y)); strip_truncations.
        destruct (upper_cut_max _ _ b.2 b'.2) as [m [um _]].
        exact (tr (m; um)).
      - exact join_lower_rounded.
      - exact join_upper_rounded.
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
  End join.

  #[local] Instance join_dedekindreals : Join R
    := fun x y => Build_DedekindReals _ _ (isdedekindcut_join x y).

  Local Definition meet_lower (x y : R) (q : Q) : HProp
    := Build_HProp (prod (lower_cut x q) (lower_cut y q)).
  Local Definition meet_upper (x y : R) (r : Q) : HProp
    := Build_HProp (hor (upper_cut x r) (upper_cut y r)).

  (** The meet is dual to the join: the cuts of [- join (- x) (- y)] are those of the meet of [x] and [y], precomposed with [fun q => - - q]. *)
  Lemma isdedekindcut_meet (x y : R) : IsDedekindCut (meet_lower x y) (meet_upper x y).
  Proof.
    assert (p : (fun q : Q => - - q) = idmap) by (apply path_forall; exact negate_involutive).
    exact (transport (fun f => IsDedekindCut (meet_lower x y o f) (meet_upper x y o f)) p
             (isdedekindcut (- join (- x) (- y)))).
  Qed.

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
      split; [reflexivity|apply lt_le, bound_lo_lt_hi].
    Qed.

    Lemma in_bounds_hi (I : CutBounds x) : in_bounds I (bound_hi I).
    Proof.
      split; [apply lt_le, bound_lo_lt_hi|reflexivity].
    Qed.

    (** Two pairs of bounds can be refined to a pair inside both: take the greater lower bound and the smaller upper bound. *)
    Lemma cutbounds_intersect (I I' : CutBounds x)
      : {I'' : CutBounds x & forall s, in_bounds I'' s -> prod (in_bounds I s) (in_bounds I' s)}.
    Proof.
      destruct (rational_max2 (bound_lo I) (bound_lo I')) as [a [[la la'] Pa]].
      destruct (rational_min2 (bound_hi I) (bound_hi I')) as [b [[lb lb'] Pb]].
      exists (Build_CutBounds x a b (Pa (lower_cut x) (bound_lo_lower I) (bound_lo_lower I'))
                (Pb (upper_cut x) (bound_hi_upper I) (bound_hi_upper I'))).
      intros s [las lsb]; split; split.
      - exact (transitivity la las).
      - exact (transitivity lsb lb).
      - exact (transitivity la' las).
      - exact (transitivity lsb lb').
    Qed.

    (** The points of bounds are strictly bounded in absolute value by a positive rational. *)
    Lemma cutbounds_abs (I : CutBounds x)
      : {Z : Q & prod (0 < Z) (forall u, in_bounds I u -> - Z < u < Z)}.
    Proof.
      destruct (round_up_strict Q (bound_hi I)) as [m lm].
      destruct (round_up_strict Q (- bound_lo I)) as [n ln].
      assert (lZ : - (nQ m + nQ n) < bound_lo I).
      { apply flip_lt_negate_l; rapply lt_le_trans; [exact ln|].
        apply nonneg_plus_le_compat_l, nat_to_semiring_nonneg. }
      assert (lZ' : bound_hi I < nQ m + nQ n).
      { rapply lt_le_trans; [exact lm|].
        apply nonneg_plus_le_compat_r, nat_to_semiring_nonneg. }
      exists (nQ m + nQ n); split.
      - apply (pos_between_negate (bound_lo I)); split; [exact lZ|].
        exact (transitivity (bound_lo_lt_hi I) lZ').
      - intros u [l l']; split.
        + rapply lt_le_trans; [exact lZ|exact l].
        + rapply le_lt_trans; [exact l'|exact lZ'].
    Qed.
  End bounds.

  (** A positive rational whose product with [S] is less than [e]. *)
  Local Lemma small_factor (e S : Q) : 0 < e -> 0 < S -> {D : Qpos Q & ' D * S < e}.
  Proof.
    intros epos Spos.
    exists (mkQpos e epos / 2 / mkQpos S Spos); cbn.
    rewrite dec_recip_mult_cancel_r; [|apply lt_ne_flip, Spos].
    exact (qpos_half_lt (mkQpos e epos)).
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
    rapply lt_mult_corners_l; eassumption.
  Qed.

  Lemma aboveproducts_corners {x y : R} (r : Q) (I : CutBounds x) (J : CutBounds y)
    : bound_lo I * bound_lo J < r -> bound_lo I * bound_hi J < r
      -> bound_hi I * bound_lo J < r -> bound_hi I * bound_hi J < r -> AboveProducts r I J.
  Proof.
    intros l1 l2 l3 l4 s t [ls ls'] [lt lt'].
    rapply mult_corners_lt_r; eassumption.
  Qed.

  Definition IsProduct {x y : R} (I : CutBounds x) (J : CutBounds y) (m : Q) : Type
    := {s : Q & {t : Q & prod (prod (in_bounds I s) (in_bounds J t)) (m = s * t)}}.

  (** The least and the greatest product of points of [I] and [J] are attained at corners. *)
  Lemma products_min {x y : R} (I : CutBounds x) (J : CutBounds y)
    : {m : Q & prod (IsProduct I J m) (forall q, q < m -> BelowProducts q I J)}.
  Proof.
    pose (corner s t (is : in_bounds I s) (it : in_bounds J t)
            := (s; (t; ((is, it), idpath))) : IsProduct I J (s * t)).
    destruct (rational_min2 (bound_lo I * bound_lo J) (bound_lo I * bound_hi J))
      as [m1 [[l1 l1'] P1]].
    destruct (rational_min2 (bound_hi I * bound_lo J) (bound_hi I * bound_hi J))
      as [m2 [[l2 l2'] P2]].
    destruct (rational_min2 m1 m2) as [m [[lm1 lm2] P]].
    exists m; split.
    - apply P; [apply P1|apply P2]; apply corner; first [apply in_bounds_lo|apply in_bounds_hi].
    - intros q lqm.
      assert (below : forall c, m <= c -> q < c) by (intros c; exact (lt_le_trans q m c lqm)).
      apply belowproducts_corners; apply below.
      + exact (transitivity lm1 l1).
      + exact (transitivity lm1 l1').
      + exact (transitivity lm2 l2).
      + exact (transitivity lm2 l2').
  Qed.

  Lemma products_max {x y : R} (I : CutBounds x) (J : CutBounds y)
    : {M : Q & prod (IsProduct I J M) (forall r, M < r -> AboveProducts r I J)}.
  Proof.
    pose (corner s t (is : in_bounds I s) (it : in_bounds J t)
            := (s; (t; ((is, it), idpath))) : IsProduct I J (s * t)).
    destruct (rational_max2 (bound_lo I * bound_lo J) (bound_lo I * bound_hi J))
      as [M1 [[l1 l1'] P1]].
    destruct (rational_max2 (bound_hi I * bound_lo J) (bound_hi I * bound_hi J))
      as [M2 [[l2 l2'] P2]].
    destruct (rational_max2 M1 M2) as [M [[lM1 lM2] P]].
    exists M; split.
    - apply P; [apply P1|apply P2]; apply corner; first [apply in_bounds_lo|apply in_bounds_hi].
    - intros r lMr.
      assert (above : forall c, c <= M -> c < r) by (intros c lcM; exact (le_lt_trans c M r lcM lMr)).
      apply aboveproducts_corners; apply above.
      + exact (transitivity l1 lM1).
      + exact (transitivity l1' lM1).
      + exact (transitivity l2 lM2).
      + exact (transitivity l2' lM2).
  Qed.

  Section mult.
    Context (x y : R).

    Local Definition mult_lower (q : Q) : HProp
      := Build_HProp (hexists (fun I : CutBounds x => hexists (fun J : CutBounds y => BelowProducts q I J))).
    Local Definition mult_upper (r : Q) : HProp
      := Build_HProp (hexists (fun I : CutBounds x => hexists (fun J : CutBounds y => AboveProducts r I J))).

    (** Roundedness: a rational between [q] and the least product is still below all products. *)
    Local Lemma mult_lower_rounded (q : Q)
      : mult_lower q <-> hexists (fun q' => prod (q < q') (mult_lower q')).
    Proof.
      split.
      - intros p; strip_truncations; destruct p as [I p]; strip_truncations; destruct p as [J p].
        destruct (products_min I J) as [m [[s [t [[is it] pm]]] below]].
        destruct (Q_dense q m) as [w [lqw lwm]]; [rewrite pm; exact (p s t is it)|].
        apply tr; exists w; split; [exact lqw|].
        apply tr; exists I; apply tr; exists J; exact (below w lwm).
      - intros p; strip_truncations; destruct p as [q' [l p]]; strip_truncations.
        destruct p as [I p]; strip_truncations; destruct p as [J p].
        apply tr; exists I; apply tr; exists J; intros s t is it.
        exact (transitivity l (p s t is it)).
    Qed.

    Local Lemma mult_upper_rounded (r : Q)
      : mult_upper r <-> hexists (fun r' => prod (r' < r) (mult_upper r')).
    Proof.
      split.
      - intros p; strip_truncations; destruct p as [I p]; strip_truncations; destruct p as [J p].
        destruct (products_max I J) as [M [[s [t [[is it] pM]]] above]].
        destruct (Q_dense M r) as [w [lMw lwr]]; [rewrite pM; exact (p s t is it)|].
        apply tr; exists w; split; [exact lwr|].
        apply tr; exists I; apply tr; exists J; exact (above w lMw).
      - intros p; strip_truncations; destruct p as [r' [l p]]; strip_truncations.
        destruct p as [I p]; strip_truncations; destruct p as [J p].
        apply tr; exists I; apply tr; exists J; intros s t is it.
        exact (transitivity (p s t is it) l).
    Qed.

    (** We approximate [x] and [y] within [D], with [D] so small that any two products of points of the bounds are less than [e] apart. *)
    Local Lemma close_cutbounds (e : Q) (epos : 0 < e)
      : merely {I : CutBounds x & {J : CutBounds y & forall s t s' t', in_bounds I s -> in_bounds J t
          -> in_bounds I s' -> in_bounds J t' -> s * t - s' * t' < e}}.
    Proof.
      assert (I0 := @merely_cutbounds x); assert (J0 := @merely_cutbounds y); strip_truncations.
      destruct (cutbounds_abs I0) as [X [Xpos IX]], (cutbounds_abs J0) as [W [Wpos JW]].
      destruct (small_factor e (X + W) epos (pos_plus_compat X W Xpos Wpos)) as [D lD].
      assert (ax := cut_approximate x D); assert (ay := cut_approximate y D); strip_truncations.
      destruct ax as [a [b [[la ub] lab]]], ay as [c [d [[lc ud] lcd]]].
      destruct (cutbounds_intersect (Build_CutBounds x a b la ub) I0) as [I HI].
      destruct (cutbounds_intersect (Build_CutBounds y c d lc ud) J0) as [J HJ].
      apply tr; exists I, J; intros s t s' t' is it is' it'.
      destruct (HI s is) as [isab isX], (HI s' is') as [is'ab _].
      destruct (HJ t it) as [itcd _], (HJ t' it') as [it'cd it'W].
      assert (ss' := interval_minus_lt a b s s' (' D) isab is'ab lab).
      assert (tt' := interval_minus_lt c d t t' (' D) itcd it'cd lcd).
      assert (bound := snd (mult_minus_mult_lt_bound s t s' t' X W (' D) (IX s isX) (JW t' it'W) ss' tt')).
      rewrite (mult_comm X), <- plus_mult_distr_l in bound.
      exact (transitivity bound lD).
    Qed.

    (** For locatedness at [q < r], we take bounds whose products are less than [r - q] apart.  If [q] is below their least product [m], it is in the lower cut; otherwise all products are below [m + (r - q) <= r]. *)
    Local Lemma mult_located (q r : Q) : q < r -> hor (mult_lower q) (mult_upper r).
    Proof.
      intros ltqr.
      assert (c := close_cutbounds (r - q) (snd (flip_pos_minus q r) ltqr)); strip_truncations.
      destruct c as [I [J close]].
      destruct (products_min I J) as [m [[s0 [t0 [[is0 it0] pm]]] below]].
      destruct (le_or_lt m q) as [lmq|lqm].
      - apply tr, inr, tr; exists I; apply tr; exists J; intros s t is it.
        assert (lt := close s t s0 t0 is it is0 it0).
        rewrite <- pm in lt; apply flip_lt_minus_l in lt.
        apply (order_preserving (r - q +)) in lmq; rewrite minus_plus_cancel in lmq.
        rapply lt_le_trans; [exact lt|exact lmq].
      - apply tr, inl, tr; exists I; apply tr; exists J; exact (below q lqm).
    Qed.

    Lemma isdedekindcut_mult : IsDedekindCut mult_lower mult_upper.
    Proof.
      split.
      - assert (I := @merely_cutbounds x); assert (J := @merely_cutbounds y); strip_truncations.
        destruct (products_min I J) as [m [_ below]].
        apply tr; exists (m - 1); apply tr; exists I; apply tr; exists J.
        apply below, pos_minus_lt_compat_r, lt_0_1.
      - assert (I := @merely_cutbounds x); assert (J := @merely_cutbounds y); strip_truncations.
        destruct (products_max I J) as [M [_ above]].
        apply tr; exists (M + 1); apply tr; exists I; apply tr; exists J.
        apply above, pos_plus_lt_compat_r, lt_0_1.
      - exact mult_lower_rounded.
      - exact mult_upper_rounded.
      - intros q r p p'; strip_truncations.
        destruct p as [I p], p' as [I' p']; strip_truncations.
        destruct p as [J p], p' as [J' p'].
        destruct (cutbounds_intersect I I') as [I'' HI], (cutbounds_intersect J J') as [J'' HJ].
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
    split; apply lt_le; [exact (bound_lo_lower I)|exact (bound_hi_upper I)].
  Qed.

  Lemma mult_dedekindreals_1_l (x : R) : 1 * x = x.
  Proof.
    apply path_dedekindreals.
    - intros q p; strip_truncations; destruct p as [I p]; strip_truncations; destruct p as [J p].
      apply (lower_cut_lt x q (bound_lo J)); [|exact (bound_lo_lower J)].
      rewrite <- (mult_1_l (bound_lo J)); exact (p 1 _ (in_bounds_rational 1 I) (in_bounds_lo J)).
    - intros r p; strip_truncations; destruct p as [I p]; strip_truncations; destruct p as [J p].
      apply (upper_cut_lt x r (bound_hi J)); [|exact (bound_hi_upper J)].
      rewrite <- (mult_1_l (bound_hi J)); exact (p 1 _ (in_bounds_rational 1 I) (in_bounds_hi J)).
  Qed.

  (** If [s] is below the products of [I] and [J] and [q - s] below those of [I] and [K], then [q] is below the products of [I] and the bounds [J + K] of [y + z], and dually. *)
  Section distribute.
    Context (x y z : R).

    Local Definition cutbounds_plus (J : CutBounds y) (K : CutBounds z) : CutBounds (y + z).
    Proof.
      srapply (Build_CutBounds (y + z) (bound_lo J + bound_lo K) (bound_hi J + bound_hi K));
        apply tr; [exists (bound_lo J)|exists (bound_hi J)]; rewrite <- plus_conjugate.
      - exact (bound_lo_lower J, bound_lo_lower K).
      - exact (bound_hi_upper J, bound_hi_upper K).
    Defined.

    Local Lemma belowproducts_plus {I I1 I2 : CutBounds x} {J : CutBounds y} {K : CutBounds z}
      (q s : Q) (sub : forall u, in_bounds I u -> prod (in_bounds I1 u) (in_bounds I2 u))
      : BelowProducts s I1 J -> BelowProducts (q - s) I2 K -> BelowProducts q I (cutbounds_plus J K).
    Proof.
      intros p p'.
      assert (c : forall u v w, in_bounds I u -> in_bounds J v -> in_bounds K w -> q < u * (v + w)).
      { intros u v w iu iv iw; destruct (sub u iu) as [i1 i2].
        rewrite (plus_conjugate_alt q s), plus_mult_distr_l.
        apply plus_lt_compat; [exact (p u v i1 iv)|exact (p' u w i2 iw)]. }
      apply belowproducts_corners; apply c; first [apply in_bounds_lo|apply in_bounds_hi].
    Qed.

    Local Lemma aboveproducts_plus {I I1 I2 : CutBounds x} {J : CutBounds y} {K : CutBounds z}
      (r s : Q) (sub : forall u, in_bounds I u -> prod (in_bounds I1 u) (in_bounds I2 u))
      : AboveProducts s I1 J -> AboveProducts (r - s) I2 K -> AboveProducts r I (cutbounds_plus J K).
    Proof.
      intros p p'.
      assert (c : forall u v w, in_bounds I u -> in_bounds J v -> in_bounds K w -> u * (v + w) < r).
      { intros u v w iu iv iw; destruct (sub u iu) as [i1 i2].
        rewrite (plus_conjugate_alt r s), plus_mult_distr_l.
        apply plus_lt_compat; [exact (p u v i1 iv)|exact (p' u w i2 iw)]. }
      apply aboveproducts_corners; apply c; first [apply in_bounds_lo|apply in_bounds_hi].
    Qed.

    Lemma mult_dedekindreals_plus_distr_l : x * (y + z) = x * y + x * z.
    Proof.
      symmetry; apply path_dedekindreals.
      - intros q p; strip_truncations; destruct p as [s [p p']]; strip_truncations.
        destruct p as [I1 p], p' as [I2 p']; strip_truncations.
        destruct p as [J p], p' as [K p'].
        destruct (cutbounds_intersect I1 I2) as [I sub].
        apply tr; exists I; apply tr; exists (cutbounds_plus J K).
        exact (belowproducts_plus q s sub p p').
      - intros r p; strip_truncations; destruct p as [s [p p']]; strip_truncations.
        destruct p as [I1 p], p' as [I2 p']; strip_truncations.
        destruct p as [J p], p' as [K p'].
        destruct (cutbounds_intersect I1 I2) as [I sub].
        apply tr; exists I; apply tr; exists (cutbounds_plus J K).
        exact (aboveproducts_plus r s sub p p').
    Qed.
  End distribute.

  (** For associativity, it suffices to show that the lower cut of [(x * y) * z] is contained in that of [x * (y * z)]. *)
  Section assoc.
    Context (x y z : R).

    (** If [q'] is below the products of bounds [E] of [x * y] and [G] of [z], then it is below [s * (t * w)] for [s], [t] and [w] in bounds of [x], [y] and [z] whose products [s * t] lie in [E]. *)
    Local Lemma assoc_cutbounds (q' : Q) (E : CutBounds (x * y)) (G : CutBounds z)
      : BelowProducts q' E G -> merely {I : CutBounds x & {J : CutBounds y &
          forall s t w, in_bounds I s -> in_bounds J t -> in_bounds G w -> q' < s * (t * w)}}.
    Proof.
      intros pE.
      assert (lE := bound_lo_lower E); assert (uE := bound_hi_upper E); strip_truncations.
      destruct lE as [I1 lE], uE as [I2 uE]; strip_truncations.
      destruct lE as [J1 lE], uE as [J2 uE].
      destruct (cutbounds_intersect I1 I2) as [I HI], (cutbounds_intersect J1 J2) as [J HJ].
      apply tr; exists I, J; intros s t w is it iw.
      destruct (HI s is) as [i1 i2], (HJ t it) as [j1 j2].
      rewrite mult_assoc; apply pE; [|exact iw].
      split; apply lt_le; [exact (lE s t i1 j1)|exact (uE s t i2 j2)].
    Qed.

    (** Given such [I], [J] and [q < q'], let [m] and [M] be the least and the greatest product of points of [J] and [G], and take [D] so small that [|s * D| < q' - q] for [s] in [I].  Then [m - D < y * z < M + D], and [s * (m - D)] and [s * (M + D)] are above [q' - (q' - q) = q]. *)
    Local Lemma assoc_widen (q q' : Q) (ltqq' : q < q') (I : CutBounds x) (J : CutBounds y)
      (G : CutBounds z) (key : forall s t w, in_bounds I s -> in_bounds J t -> in_bounds G w
                                 -> q' < s * (t * w))
      : lower_cut (x * (y * z)) q.
    Proof.
      destruct (cutbounds_abs I) as [T [Tpos IT]].
      destruct (small_factor (q' - q) T (snd (flip_pos_minus q q') ltqq') Tpos) as [D lD].
      destruct (products_min J G) as [m [[t0 [w0 [[it0 iw0] pm]]] below]].
      destruct (products_max J G) as [M [[t1 [w1 [[it1 iw1] pM]]] above]].
      assert (lK : lower_cut (y * z) (m - ' D)).
      { apply tr; exists J; apply tr; exists G; apply below, pos_minus_lt_compat_r, pos_is_pos. }
      assert (uK : upper_cut (y * z) (M + ' D)).
      { apply tr; exists J; apply tr; exists G; apply above, pos_plus_lt_compat_r, pos_is_pos. }
      assert (sD : forall s, in_bounds I s -> - (q' - q) < s * ' D < q' - q).
      { intros s is; destruct (IT s is) as [lTs lsT].
        rewrite mult_comm in lD; split.
        - apply flip_lt_negate_l; rewrite negate_mult_distr_l.
          rhs_V' exact lD; apply (strictly_order_preserving (.* ' D)), flip_lt_negate_l, lTs.
        - rhs_V' exact lD; apply (strictly_order_preserving (.* ' D)), lsT. }
      assert (shift : forall a b, q' < a -> - (q' - q) < b -> q < a + b).
      { intros a b la lb; rewrite <- (minus_minus_cancel q' q); apply plus_lt_compat; assumption. }
      assert (c : forall s, in_bounds I s -> prod (q < s * (m - ' D)) (q < s * (M + ' D))).
      { intros s is; rewrite 2!plus_mult_distr_l, <- negate_mult_distr_r; split; apply shift.
        - rewrite pm; exact (key s t0 w0 is it0 iw0).
        - exact (snd (flip_lt_negate (s * ' D) (q' - q)) (snd (sD s is))).
        - rewrite pM; exact (key s t1 w1 is it1 iw1).
        - exact (fst (sD s is)). }
      apply tr; exists I; apply tr; exists (Build_CutBounds (y * z) (m - ' D) (M + ' D) lK uK).
      apply belowproducts_corners; cbn.
      + exact (fst (c _ (in_bounds_lo I))).
      + exact (snd (c _ (in_bounds_lo I))).
      + exact (fst (c _ (in_bounds_hi I))).
      + exact (snd (c _ (in_bounds_hi I))).
    Qed.

    Lemma mult_dedekindreals_assoc_lower (q : Q)
      : lower_cut ((x * y) * z) q -> lower_cut (x * (y * z)) q.
    Proof.
      intros p; apply (lower_cut_rounded _ q) in p; strip_truncations; destruct p as [q' [lq p]].
      strip_truncations; destruct p as [E p]; strip_truncations; destruct p as [G pE].
      assert (c := assoc_cutbounds q' E G pE); strip_truncations; destruct c as [I [J key]].
      exact (assoc_widen q q' lq I J G key).
    Qed.
  End assoc.

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

  #[export] Instance strictlyorderpreserving_plus_dedekindreals (z : R)
    : StrictlyOrderPreserving (z +).
  Proof.
    intros x y l; apply lt_dedekindreals_iff_lower_minus.
    rewrite plus_minus_plus_l; exact (fst (lt_dedekindreals_iff_lower_minus x y) l).
  Qed.

  Local Lemma lt_dedekindreals_minus_zero (a b : R) : a < b -> a - b < 0.
  Proof.
    intros l; rewrite <- (plus_negate_r b), (plus_comm a), (plus_comm b).
    apply (strictly_order_preserving (- b +)), l.
  Qed.

  Local Lemma lt_dedekindreals_zero_minus (a b : R) : b < a -> 0 < a - b.
  Proof.
    intros l; rewrite <- (plus_negate_r b), (plus_comm a), (plus_comm b).
    apply (strictly_order_preserving (- b +)), l.
  Qed.

  Local Lemma lt_dedekindreals_from_minus (a b c : R) : a - b < c - b -> a < c.
  Proof.
    intros l; apply (strictly_order_preserving (b +) (a - b) (c - b)) in l.
    rewrite !(plus_comm b), !minus_plus_cancel in l; exact l.
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
    apply pos_mult; [exact (lt_le_trans 0 s u ls lu)|exact (lt_le_trans 0 t v lt lv)].
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
      rewrite (plus_conjugate_alt s t); apply plus_lt_compat; [exact l|exact l'].
    - intros s p; strip_truncations; destruct p as [t [l l']]; cbn in l, l' |- *.
      rewrite (plus_conjugate_alt s t); apply plus_lt_compat; [exact l|exact l'].
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

  Local Lemma plus_one_minus_dedekind (t : Q) : [t] + [1 - t] = 1.
  Proof.
    rewrite <- rational_dedekind_plus, <- plus_conjugate_alt; reflexivity.
  Qed.

  Local Lemma minus_minus_one_dedekind (t : Q) : [t] - [t - 1] = 1.
  Proof.
    rewrite <- preserves_negate, <- rational_dedekind_plus, minus_minus_cancel; reflexivity.
  Qed.

  Local Lemma quotient_mult_dedekind (u b : Q) : 0 < b -> [u / b] * [b] = [u].
  Proof.
    intros bpos; rewrite <- rational_dedekind_mult, dec_recip_mult_cancel_r; [reflexivity|].
    apply lt_ne_flip, bpos.
  Qed.

  (** For a positive real [x], we have [q < 1 / x] when [q * x < 1] and [1 / x < r] when [1 < r * x]. *)
  Section pos_recip.
    Context (x : R) `{xpos : !PropHolds (0 < x)}.

    Local Definition pos_recip_lower (q : Q) : HProp := Build_HProp ([q] * x < 1).
    Local Definition pos_recip_upper (r : Q) : HProp := Build_HProp (1 < [r] * x).

    (** If [x < b], then [u / b * x < u]. *)
    Local Lemma mult_quotient_lt (u b : Q) : 0 < u -> 0 < b -> x < [b] -> [u / b] * x < [u].
    Proof.
      intros upos bpos lb.
      assert (PropHolds (0 < [u / b])) by exact (fst (rational_dedekind_lt 0 _) (pos_quotient u b upos bpos)).
      rewrite <- (quotient_mult_dedekind u b bpos).
      apply (strictly_order_preserving ([u / b] *.)), lb.
    Qed.

    (** If [q * x < t < 1] and [x < b], then [(q + (1 - t) / b) * x < t + (1 - t) = 1]. *)
    Local Lemma pos_recip_lower_rounded (q : Q)
      : [q] * x < 1 <-> hexists (fun q' => prod (q < q') ([q'] * x < 1)).
    Proof.
      split.
      2: { apply Trunc_rec; intros [q' [l p]].
           rhs_V' exact p.
           exact (strictly_order_preserving (.* x) [q] [q'] (fst (rational_dedekind_lt q q') l)). }
      intros l.
      assert (t := dedekindreals_archimedean _ _ l); assert (b := merely_pos_upper x xpos).
      strip_truncations; destruct t as [t [lt lt1]], b as [b [bpos lb]].
      apply (rational_dedekind_lt t 1) in lt1.
      assert (upos : 0 < 1 - t) by exact (snd (flip_pos_minus t 1) lt1).
      apply tr; exists (q + (1 - t) / b); split.
      - apply pos_plus_lt_compat_r, pos_quotient; [exact upos|exact bpos].
      - rewrite rational_dedekind_plus, plus_mult_distr_r, <- (plus_one_minus_dedekind t).
        apply plus_lt_compat; [exact lt|exact (mult_quotient_lt (1 - t) b upos bpos lb)].
    Qed.

    (** If [1 < t < r * x] and [x < b], then [(r - (t - 1) / b) * x > t - (t - 1) = 1]. *)
    Local Lemma pos_recip_upper_rounded (r : Q)
      : 1 < [r] * x <-> hexists (fun r' => prod (r' < r) (1 < [r'] * x)).
    Proof.
      split.
      2: { apply Trunc_rec; intros [r' [l p]].
           lhs' exact p.
           exact (strictly_order_preserving (.* x) [r'] [r] (fst (rational_dedekind_lt r' r) l)). }
      intros l.
      assert (t := dedekindreals_archimedean _ _ l); assert (b := merely_pos_upper x xpos).
      strip_truncations; destruct t as [t [lt1 lt]], b as [b [bpos lb]].
      apply (rational_dedekind_lt 1 t) in lt1.
      assert (upos : 0 < t - 1) by exact (snd (flip_pos_minus 1 t) lt1).
      apply tr; exists (r - (t - 1) / b); split.
      - apply pos_minus_lt_compat_r, pos_quotient; [exact upos|exact bpos].
      - rewrite rational_dedekind_plus, preserves_negate, plus_mult_distr_r.
        rewrite <- negate_mult_distr_l, <- (minus_minus_one_dedekind t).
        apply plus_lt_compat; [exact lt|].
        apply (snd (flip_lt_negate _ [t - 1])), (mult_quotient_lt (t - 1) b upos bpos lb).
    Qed.

    Lemma isdedekindcut_pos_recip : IsDedekindCut pos_recip_lower pos_recip_upper.
    Proof.
      split.
      - assert (l : [0] * x < 1) by (rewrite (mult_0_l x); exact lt_0_1_dedekindreals).
        apply tr; exists 0; exact l.
      - apply (fst (lt_rational_dedekind_l 0 x)), (lower_cut_rounded x) in xpos.
        strip_truncations; destruct xpos as [s [spos ls]].
        assert (PropHolds (0 < [1 / s])) by exact (fst (rational_dedekind_lt 0 _) (pos_quotient 1 s lt_0_1 spos)).
        assert (l : 1 < [1 / s] * x).
        { assert (p : [1 / s] * [s] = 1) by exact (quotient_mult_dedekind 1 s spos).
          rewrite <- p; apply (strictly_order_preserving ([1 / s] *.)), lt_rational_dedekind_l, ls. }
        apply tr; exists (1 / s); exact l.
      - exact pos_recip_lower_rounded.
      - exact pos_recip_upper_rounded.
      - intros q r l l'.
        apply (rational_dedekind_lt q r), (strictly_order_reflecting (.* x)).
        exact (transitivity l l').
      - intros q r l.
        exact (cotransitive (strictly_order_preserving (.* x) [q] [r] (fst (rational_dedekind_lt q r) l)) 1).
    Qed.

    Definition pos_recip_dedekind : R := Build_DedekindReals _ _ isdedekindcut_pos_recip.

    Local Notation y := pos_recip_dedekind.

    (** If [y * x < t < 1], we approximate [q < y < r] with [r - q < (1 - t) / b] for an upper bound [b] of [x].  Then [1 < r * x < (y + (1 - t) / b) * x < t + (1 - t) = 1]. *)
    Local Lemma not_mult_pos_recip_lt_1 : ~ (y * x < 1).
    Proof.
      (* We use [Trunc_rec] rather than [strip_truncations], which would also strip [xpos]. *)
      intros l; generalize (dedekindreals_archimedean _ _ l); apply Trunc_rec.
      intros [t [lt lt1]]; apply (rational_dedekind_lt t 1) in lt1.
      generalize (merely_pos_upper x xpos); apply Trunc_rec; intros [b [bpos lb]].
      assert (upos : 0 < 1 - t) by exact (snd (flip_pos_minus t 1) lt1).
      generalize (cut_approximate y (mkQpos ((1 - t) / b) (pos_quotient _ b upos bpos))).
      apply Trunc_rec; intros [q [r [[lq ur] lqr]]].
      assert (lr : [r] < y + [(1 - t) / b]).
      { rapply lt_le_trans; [|apply lt_le, (strictly_order_preserving (+ [(1 - t) / b])), lt_rational_dedekind_l, lq].
        rewrite <- rational_dedekind_plus; apply rational_dedekind_lt.
        rewrite plus_comm; apply flip_lt_minus_l, lqr. }
      apply (irreflexivity (<) (1 : R)); lhs' exact ur.
      lhs' apply (strictly_order_preserving (.* x)), lr.
      rewrite plus_mult_distr_r, <- (plus_one_minus_dedekind t).
      apply plus_lt_compat; [exact lt|exact (mult_quotient_lt (1 - t) b upos bpos lb)].
    Qed.

    (** Dually, if [1 < t < y * x], then [1 > q * x > (y - (t - 1) / b) * x > t - (t - 1) = 1]. *)
    Local Lemma not_one_lt_mult_pos_recip : ~ (1 < y * x).
    Proof.
      intros l; generalize (dedekindreals_archimedean _ _ l); apply Trunc_rec.
      intros [t [lt1 lt]]; apply (rational_dedekind_lt 1 t) in lt1.
      generalize (merely_pos_upper x xpos); apply Trunc_rec; intros [b [bpos lb]].
      assert (upos : 0 < t - 1) by exact (snd (flip_pos_minus 1 t) lt1).
      generalize (cut_approximate y (mkQpos ((t - 1) / b) (pos_quotient _ b upos bpos))).
      apply Trunc_rec; intros [q [r [[lq ur] lqr]]].
      assert (lq' : y - [(t - 1) / b] < [q]).
      { rapply le_lt_trans; [apply lt_le, (strictly_order_preserving (+ - [(t - 1) / b])), lt_rational_dedekind_r, ur|].
        rewrite <- preserves_negate, <- rational_dedekind_plus; apply rational_dedekind_lt.
        apply flip_lt_minus_l; rewrite plus_comm; apply flip_lt_minus_l, lqr. }
      apply (irreflexivity (<) (1 : R)); rhs_V' exact lq.
      rhs_V' apply (strictly_order_preserving (.* x)), lq'.
      rewrite plus_mult_distr_r, <- negate_mult_distr_l, <- (minus_minus_one_dedekind t).
      apply plus_lt_compat; [exact lt|].
      apply (snd (flip_lt_negate _ [t - 1])), (mult_quotient_lt (t - 1) b upos bpos lb).
    Qed.

    Lemma pos_recip_dedekind_inverse : x * y = 1.
    Proof.
      apply (fst (tight_apart _ _)); intros a; refine (Trunc_rec _ a).
      rewrite mult_dedekindreals_comm; intros [l|l].
      - exact (not_mult_pos_recip_lt_1 l).
      - exact (not_one_lt_mult_pos_recip l).
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
    Local Lemma modulus_cut_lt (e : Qpos Q) {m n : nat} {a b : Q}
      : (M e <= m)%nat -> (M e <= n)%nat -> lower_cut Q (x m) a -> upper_cut Q (x n) b -> a < b + ' e.
    Proof.
      intros lm ln la ub.
      assert (c := snd (cauchy_convergence Q R x e m n lm ln)).
      apply flip_lt_minus_l in c; unfold cast in c.
      rewrite (rationals_initial (h:=rational_dedekind Q)) in c.
      apply (snd (rational_dedekind_lt Q _ _)); rewrite plus_comm, (rational_dedekind_plus Q (Qroundup:=Qroundup)).
      lhs' exact (snd (lt_rational_dedekind_l Q a (x m)) la).
      lhs' exact c.
      exact (strictly_order_preserving ([' e] +) (x n) [b] (snd (lt_rational_dedekind_r Q b (x n)) ub)).
    Qed.

    (** The limit: [q < l] when [q + e + d < x (M e)] for some [e] and [d], and dually. *)
    Local Definition limit_lower (q : Q) : HProp
      := Build_HProp (hexists (fun e : Qpos Q => hexists (fun d : Qpos Q =>
                       lower_cut Q (x (M e)) (q + ' e + ' d)))).
    Local Definition limit_upper (r : Q) : HProp
      := Build_HProp (hexists (fun e : Qpos Q => hexists (fun d : Qpos Q =>
                       upper_cut Q (x (M e)) (r - ' e - ' d)))).

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

    (** For roundedness, we split [d] in halves. *)
    Local Lemma limit_lower_rounded (q : Q)
      : limit_lower q <-> hexists (fun q' => prod (q < q') (limit_lower q')).
    Proof.
      split.
      - intros p; strip_truncations; destruct p as [e p]; strip_truncations; destruct p as [d p].
        apply tr; exists (q + ' (d / 2)); split; [apply pos_plus_lt_compat_r, pos_is_pos|].
        apply tr; exists e; apply tr; exists (d / 2).
        rewrite plus_half_shift; exact p.
      - intros p; strip_truncations; destruct p as [q' [l p]]; strip_truncations.
        destruct p as [e p]; strip_truncations; destruct p as [d p].
        apply tr; exists e; apply tr; exists d.
        apply (lower_cut_lt Q (x (M e)) _ (q' + ' e + ' d)); [|exact p].
        apply (strictly_order_preserving (+ ' d)), (strictly_order_preserving (+ ' e)), l.
    Qed.

    Local Lemma limit_upper_rounded (r : Q)
      : limit_upper r <-> hexists (fun r' => prod (r' < r) (limit_upper r')).
    Proof.
      split.
      - intros p; strip_truncations; destruct p as [e p]; strip_truncations; destruct p as [d p].
        apply tr; exists (r - ' (d / 2)); split; [apply pos_minus_lt_compat_r, pos_is_pos|].
        apply tr; exists e; apply tr; exists (d / 2).
        rewrite minus_half_shift; exact p.
      - intros p; strip_truncations; destruct p as [r' [l p]]; strip_truncations.
        destruct p as [e p]; strip_truncations; destruct p as [d p].
        apply tr; exists e; apply tr; exists d.
        apply (upper_cut_lt Q (x (M e)) _ (r' - ' e - ' d)); [|exact p].
        apply (strictly_order_preserving (+ - ' d)), (strictly_order_preserving (+ - ' e)), l.
    Qed.

    Local Lemma lt_plus_pos2 (q : Q) (e d : Qpos Q) : q < q + ' e + ' d.
    Proof.
      rhs_V' apply pos_plus_lt_compat_r, pos_is_pos.
      apply pos_plus_lt_compat_r, pos_is_pos.
    Qed.

    Local Lemma minus_pos2_lt (r : Q) (e d : Qpos Q) : r - ' e - ' d < r.
    Proof.
      lhs' apply pos_minus_lt_compat_r, pos_is_pos.
      apply pos_minus_lt_compat_r, pos_is_pos.
    Qed.

    (** For transitivity, given [q + e + d < x (M e)] and [x (M e') < r - e' - d'], we compare the two terms with [modulus_cut_lt] at the larger of [M e] and [M e']. *)
    Local Lemma limit_transitive (q r : Q) : limit_lower q -> limit_upper r -> q < r.
    Proof.
      intros p p'; strip_truncations.
      destruct p as [e p], p' as [e' p']; strip_truncations.
      destruct p as [d p], p' as [d' p'].
      destruct (leq_dichotomy (M e) (M e')) as [lM|lM].
      - assert (c := modulus_cut_lt e (leq_refl _) lM p p').
        rewrite <- (plus_assoc q), (plus_comm (' e)), plus_assoc in c.
        apply (strictly_order_reflecting (+ ' e)) in c.
        lhs' apply (pos_plus_lt_compat_r q (' d)), pos_is_pos.
        lhs' exact c.
        apply minus_pos2_lt.
      - assert (c := modulus_cut_lt e' (leq_lt lM) (leq_refl _) p p').
        rewrite <- (plus_assoc (r - ' e')), (plus_comm (- ' d')), plus_assoc, minus_plus_cancel in c.
        lhs' exact (lt_plus_pos2 q e d).
        lhs' exact c.
        apply pos_minus_lt_compat_r, pos_is_pos.
    Qed.

    Lemma isdedekindcut_limit : IsDedekindCut Q limit_lower limit_upper.
    Proof.
      split.
      - assert (a := cut_lower_inhabited (isdedekindcut Q (x (M 1)))); strip_truncations.
        destruct a as [a la]; apply tr; exists (a - ' 1 - ' 1); apply tr; exists 1; apply tr; exists 1.
        rewrite 2!minus_plus_cancel; exact la.
      - assert (b := cut_upper_inhabited (isdedekindcut Q (x (M 1)))); strip_truncations.
        destruct b as [b ub]; apply tr; exists (b + ' 1 + ' 1); apply tr; exists 1; apply tr; exists 1.
        rewrite 2!plus_minus_cancel; exact ub.
      - exact limit_lower_rounded.
      - exact limit_upper_rounded.
      - exact limit_transitive.
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

    (** Beyond [M (e / 2)], the terms are at most [e / 2] above the limit: otherwise there is [r] with [x n < r - e / 2] and [r + e' + d' < x (M e')], which contradicts [modulus_cut_lt]. *)
    Local Lemma limit_minus_le (e : Qpos Q) (n : nat) : leq (M (e / 2)) n
      -> limit_dedekind - x n <= [' (e / 2)].
    Proof.
      intros ln; apply le_iff_not_lt_flip; intros l.
      apply flip_lt_minus_r in l.
      assert (c := dedekindreals_archimedean Q _ _ l); strip_truncations.
      destruct c as [r [lr lr']].
      rewrite plus_comm in lr; apply flip_lt_minus_r in lr.
      rewrite <- rational_dedekind_minus in lr; apply (fst (lt_rational_dedekind_r Q _ _)) in lr.
      apply (fst (lt_rational_dedekind_l Q r _)) in lr'; strip_truncations.
      destruct lr' as [e' p]; strip_truncations; destruct p as [d' p].
      destruct (leq_dichotomy (M (e / 2)) (M e')) as [lM|lM].
      - apply (irreflexivity (<) (r + ' e' + ' d')); lhs' exact (modulus_cut_lt (e / 2) lM ln p lr).
        rewrite minus_plus_cancel; apply lt_plus_pos2.
      - apply (irreflexivity (<) (r + ' e' + ' d')).
        lhs' exact (modulus_cut_lt e' (leq_refl _) (leq_trans (leq_lt lM) ln) p lr).
        rhs_V' apply pos_plus_lt_compat_r, (pos_is_pos d').
        apply (strictly_order_preserving (+ ' e')), pos_minus_lt_compat_r, pos_is_pos.
    Qed.

    (** Dually, beyond [M (e / 2)], the terms are at most [e / 2] below the limit. *)
    Local Lemma minus_limit_le (e : Qpos Q) (n : nat) : leq (M (e / 2)) n
      -> x n - limit_dedekind <= [' (e / 2)].
    Proof.
      intros ln; apply le_iff_not_lt_flip; intros l.
      apply flip_lt_minus_r in l.
      assert (c := dedekindreals_archimedean Q _ _ l); strip_truncations.
      destruct c as [r [lr lr']].
      apply (fst (lt_rational_dedekind_l Q r _)) in lr'.
      rewrite plus_comm in lr; apply flip_lt_minus_r in lr.
      rewrite <- rational_dedekind_minus in lr; apply (fst (lt_rational_dedekind_r Q _ _)) in lr.
      strip_truncations; destruct lr as [e' p]; strip_truncations; destruct p as [d' p].
      destruct (leq_dichotomy (M (e / 2)) (M e')) as [lM|lM].
      - apply (irreflexivity (<) r); lhs' exact (modulus_cut_lt (e / 2) ln lM lr' p).
        rapply lt_le_trans; [apply (strictly_order_preserving (+ ' (e / 2))), minus_pos2_lt|].
        rewrite minus_plus_cancel; reflexivity.
      - apply (irreflexivity (<) r).
        lhs' exact (modulus_cut_lt e' (leq_trans (leq_lt lM) ln) (leq_refl _) lr' p).
        rapply lt_le_trans; [apply (strictly_order_preserving (+ ' e')), pos_minus_lt_compat_r, pos_is_pos|].
        rewrite minus_plus_cancel; apply lt_le, pos_minus_lt_compat_r, pos_is_pos.
    Qed.

    Lemma islimit_limit_dedekind : IsLimit Q R x limit_dedekind.
    Proof.
      intros e; apply tr; exists (M (e / 2)); intros n ln; unfold cast.
      rewrite (rationals_initial (h:=rational_dedekind Q)).
      assert (half : [' (e / 2)] < [' e]).
      { apply rational_dedekind_lt, qpos_half_lt. }
      split.
      - rewrite negate_swap_r; apply (snd (flip_lt_negate _ _)).
        rapply le_lt_trans; [exact (minus_limit_le e n ln)|exact half].
      - rapply le_lt_trans; [exact (limit_minus_le e n ln)|exact half].
    Qed.
  End limit.

  (** The Dedekind reals are Cauchy complete, with the limit given by [limit_dedekind]. *)
  #[export] Instance iscomplete_dedekindreals : IsComplete Q R.
  Proof.
    intros x M H'; exists (limit_dedekind x M); exact (islimit_limit_dedekind x M).
  Qed.
End complete.
