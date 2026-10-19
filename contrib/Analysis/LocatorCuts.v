(** * Dedekind cuts as structure *)

(** A Dedekind cut is a pair of predicates on the rationals with eight properties: both are bounded (inhabited), closed downwards respectively upwards, open, the cut is transitive and located. Each property except closedness and transitivity has a structural counterpart, obtained by replacing [hexists] by [sig] and [hor] by [sum]; the structural counterpart of locatedness is a locator. We show that a cut with a locator has the full structure, that the structure gives a Cauchy real, and that a choice of locators for all reals contradicts continuity: it gives a map to [Bool] taking two different values, which implies the weak limited principle of omniscience. *)

From HoTT Require Import Basics Types.Bool Types.Sum Types.Sigma Truncations.Core
  Universes.HProp Universes.HSet.
From HoTT.Spaces Require Import Nat.Core.
From HoTT.Misc Require Import CompactTypes.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.naturals
  interfaces.integers
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
  orders.rationals.
From HoTT.Analysis Require Import Locator.
From HoTT_Contrib.Analysis Require Import
  MetricSpace CauchyCompleteness CauchyReals DedekindReals RealsInclusions LocatorDigits.

(** A map to [Bool] is strongly nonconstant when it merely takes two different values. *)
Definition IsStronglyNonconstant {A : Type} (f : A -> Bool)
  := hexists (fun x : A => hexists (fun y : A => f x <> f y)).

Section wlpo.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec_paths : DecidablePaths Q} {Qtriv : TrivialApart Q}
    {Qroundup : RoundUpStrict Q}.
  Context (F : Type) `{Forderedfield : OrderedField F}.
  Context {Farchimedean : ArchimedeanProperty Q F} {Fcomplete : IsComplete Q F}.
  Context `{Funext}.

  Local Existing Instance qinc.

  (** ** A choice of locators gives a strongly nonconstant map *)

  Section choice.
    Context (l : forall x : F, locator Q F x).

    (** Whether the locator of [x] locates [0 < x] or [x < 1]. *)
    Definition locator_choice_bool (x : F) : Bool := if l x 0 1 lt_0_1 then true else false.

    Lemma locator_choice_bool_0 : locator_choice_bool (' 0) = false.
    Proof.
      unfold locator_choice_bool; destruct (l (' 0) 0 1 lt_0_1) as [lt|lt].
      - destruct (irreflexivity _ _ lt).
      - reflexivity.
    Qed.

    Lemma locator_choice_bool_1 : locator_choice_bool (' 1) = true.
    Proof.
      unfold locator_choice_bool; destruct (l (' 1) 0 1 lt_0_1) as [lt|lt].
      - reflexivity.
      - destruct (irreflexivity _ _ lt).
    Qed.

    Definition isstronglynonconstant_locator_choice_bool
      : IsStronglyNonconstant locator_choice_bool
      := tr (' 0; tr (' 1; fun p => false_ne_true (locator_choice_bool_0^ @ p @ locator_choice_bool_1))).
  End choice.

  (** ** Strongly nonconstant maps imply WLPO *)

  (** Bisection of [[0, 1]] with intervals of width [w n = 2^(- n)]. *)

  Local Notation w := (digit_weight Q 1).

  Local Lemma w_succ (n : nat) : w n = w (S n) + w (S n).
  Proof.
    rewrite (digit_weight_succ Q 1 n).
    assert (p : naturals_to_semiring nat Q 1 = 1) by exact preserves_1.
    rewrite p, mult_1_l; reflexivity.
  Qed.

  Local Definition w_pos (n : nat) : 0 < w n := digit_weight_pos Q 1 n.

  Section bisection.
    Context (g : Q -> Bool) (g01 : g 0 <> g 1).

    (** Bisection: [g] takes different values at the endpoints of [[a n, a n + w n]]. *)
    Fixpoint bisect (n : nat) : Q
      := match n with
         | O => 0
         | S n => if dec (g (bisect n + w (S n)) = g (bisect n))
                 then bisect n + w (S n) else bisect n
         end.

    Lemma bisect_separates (n : nat) : g (bisect n) <> g (bisect n + w n).
    Proof.
      induction n as [|n IH].
      - change (g 0 <> g (0 + 1)); rewrite plus_0_l; exact g01.
      - rewrite (w_succ n) in IH; cbn [bisect].
        destruct (dec (g (bisect n + w (S n)) = g (bisect n))) as [e|ne].
        + rewrite e, <- plus_assoc; exact IH.
        + exact (fun p => ne p^).
    Qed.

    Local Notation a := bisect.

    Lemma bisect_succ_bounds (n : nat)
      : a n ≤ a (S n) /\ a (S n) + w (S n) ≤ a n + w n.
    Proof.
      assert (wle : w (S n) ≤ w n).
      { rewrite (w_succ n); apply nonneg_plus_le_compat_r, lt_le, w_pos. }
      cbn [bisect].
      destruct (dec (g (a n + w (S n)) = g (a n))) as [e|ne]; split.
      - apply nonneg_plus_le_compat_r, lt_le, w_pos.
      - rewrite <- plus_assoc, <- w_succ; reflexivity.
      - reflexivity.
      - apply (order_preserving (a n +)), wle.
    Qed.

    Lemma bisect_bounds (m n : nat) : (m <= n)%nat
      -> a m ≤ a n /\ a n + w n ≤ a m + w m.
    Proof.
      intros le; induction le as [|n le [IH1 IH2]].
      - split; reflexivity.
      - destruct (bisect_succ_bounds n) as [b1 b2]; split.
        + exact (transitivity IH1 b1).
        + exact (transitivity b2 IH2).
    Qed.

    (** Two rationals in an interval of width less than [e] are [e]-close. *)
    Local Lemma rational_close_interval (c d u v : Q) (e : Qpos Q)
      : c ≤ u ≤ c + d -> c ≤ v ≤ c + d -> d < ' e -> rational_close Q e u v.
    Proof.
      intros lu lv lde; apply (interval_minus_lt c (c + d) u v _ lu lv).
      rewrite (plus_comm c d), <- plus_assoc, plus_negate_r, plus_0_r; exact lde.
    Qed.

    Local Lemma bisect_in_interval (m n : nat) (le : (m <= n)%nat) (t : Q)
      : a n ≤ t ≤ a n + w n -> a m ≤ t ≤ a m + w m.
    Proof.
      destruct (bisect_bounds m n le) as [b1 b2]; intros [t1 t2]; split.
      - exact (transitivity b1 t1).
      - exact (transitivity t2 b2).
    Qed.

    Local Lemma bisect_self_in_interval (n : nat) : a n ≤ a n ≤ a n + w n.
    Proof.
      split; [reflexivity|]; apply nonneg_plus_le_compat_r, lt_le, w_pos.
    Qed.

    Definition bisect_modulus : MetricCauchyModulus Q (rational_close Q) a (digit_modulus Q 1 _)
      := fun e m n lem len =>
           rational_close_interval _ _ _ _ e
             (bisect_in_interval _ _ lem _ (bisect_self_in_interval m))
             (bisect_in_interval _ _ len _ (bisect_self_in_interval n))
             (digit_weight_modulus Q 1 _ e _ (leq_refl _)).

    Definition bisect_sequence : CauchySequence Q
      := {| cauchy_seq := a; cauchy_modulus := digit_modulus Q 1 _;
            cauchy_ismodulus := bisect_modulus |}.

    Section search.
      Context (b0 : Bool) (P : nat -> Type) `{forall n, Decidable (P n)}.

      (** An endpoint of the [j]th interval at which [g] does not take the value [b0]. *)
      Local Definition endpoint (j : nat) : Q
        := if dec (g (a j) = b0) then a j + w j else a j.

      Local Lemma endpoint_ne (j : nat) : g (endpoint j) <> b0.
      Proof.
        unfold endpoint; destruct (dec (g (a j) = b0)) as [e|ne].
        - intros p; exact (bisect_separates j (e @ p^)).
        - exact ne.
      Qed.

      Local Lemma endpoint_in_interval (j : nat) : a j ≤ endpoint j ≤ a j + w j.
      Proof.
        unfold endpoint; destruct (dec (g (a j) = b0)).
        - split; [apply nonneg_plus_le_compat_r, lt_le, w_pos|reflexivity].
        - exact (bisect_self_in_interval j).
      Qed.

      (** Whether [P i] holds for some [i < n]. *)
      Local Fixpoint seen (n : nat) : Bool
        := match n with
           | O => false
           | S n => if seen n then true else if dec (P n) then true else false
           end.

      (** The bisection sequence until the first [i] with [P i], then constantly the corresponding endpoint. *)
      Local Fixpoint search (n : nat) : Q
        := match n with
           | O => a 0
           | S n => if seen n then search n else if dec (P n) then endpoint n else a (S n)
           end.

      Local Lemma search_unseen (n : nat) : seen n = false -> search n = a n.
      Proof.
        induction n as [|n IH]; [reflexivity|]; cbn [seen search].
        revert IH; destruct (seen n); intros IH h.
        - destruct (true_ne_false h).
        - destruct (dec (P n)); [destruct (true_ne_false h)|reflexivity].
      Qed.

      Local Lemma seen_le (m n : nat) : (m <= n)%nat -> seen m = true -> seen n = true.
      Proof.
        intros le h; induction le as [|n le IH]; [exact h|]; cbn [seen].
        rewrite IH; reflexivity.
      Qed.

      Local Lemma search_seen (m n : nat) : (m <= n)%nat -> seen m = true -> search n = search m.
      Proof.
        intros le h; induction le as [|n le IH]; [reflexivity|]; cbn [search].
        rewrite (seen_le m n le h); exact IH.
      Qed.

      Local Lemma search_unseen_interval (m n : nat) : (m <= n)%nat -> seen m = false
        -> a m ≤ search n ≤ a m + w m.
      Proof.
        intros le h; induction le as [|n le IH].
        - rewrite (search_unseen m h); exact (bisect_self_in_interval m).
        - cbn [search]; destruct (seen n); [exact IH|].
          destruct (dec (P n)).
          + exact (bisect_in_interval _ _ le _ (endpoint_in_interval n)).
          + exact (bisect_in_interval _ _ (leq_succ_r le) _ (bisect_self_in_interval _)).
      Qed.

      Local Lemma search_endpoint (n : nat) : seen n = true -> {j : nat & search n = endpoint j}.
      Proof.
        induction n as [|n IH]; cbn [seen search].
        - intros h; destruct (true_ne_false h^).
        - revert IH; destruct (seen n); intros IH h; [exact (IH idpath)|].
          destruct (dec (P n)); [exact (n; idpath)|destruct (true_ne_false h^)].
      Qed.

      Local Lemma seen_succ (i : nat) : P i -> seen (S i) = true.
      Proof.
        intros p; cbn [seen]; destruct (seen i); [reflexivity|].
        destruct (dec (P i)) as [_|np]; [reflexivity|destruct (np p)].
      Qed.

      Local Lemma never_seen (np : forall n, ~ P n) (n : nat) : seen n = false.
      Proof.
        induction n as [|n IH]; [reflexivity|]; cbn [seen]; rewrite IH.
        destruct (dec (P n)) as [p|_]; [destruct (np n p)|reflexivity].
      Qed.

      Definition search_modulus
        : MetricCauchyModulus Q (rational_close Q) search (digit_modulus Q 1 _).
      Proof.
        intros e m n lem len.
        set (N := digit_modulus Q 1 _ e) in *.
        generalize (search_seen N m lem) (search_seen N n len) (search_unseen_interval N m lem)
          (search_unseen_interval N n len).
        destruct (seen N); intros sm sn um un.
        - rewrite (sm idpath), (sn idpath); apply (rational_close_refl Q).
        - exact (rational_close_interval _ _ _ _ e (um idpath) (un idpath)
                   (digit_weight_modulus Q 1 _ e _ (leq_refl _))).
      Defined.

      Definition search_sequence : CauchySequence Q
        := {| cauchy_seq := search; cauchy_modulus := digit_modulus Q 1 _;
              cauchy_ismodulus := search_modulus |}.

      (** If [P] never holds, the search sequence has the same limit as the bisection. *)
      Local Lemma search_limit_never (np : forall n, ~ P n)
        : cauchy_limit Q F search_sequence = cauchy_limit Q F bisect_sequence.
      Proof.
        apply (limit_unique Q (fun n => ' search n)).
        - exact (islimit_cauchy_limit Q F search_sequence).
        - assert (p : (fun n => ' search n) = (fun n => ' a n)).
          { apply path_forall; intro n; exact (ap _ (search_unseen n (never_seen np n))). }
          rewrite p; exact (islimit_cauchy_limit Q F bisect_sequence).
      Qed.

      (** If [P i] holds, the search sequence is eventually constant. *)
      Local Lemma search_limit_seen (i : nat) (p : P i)
        : cauchy_limit Q F search_sequence = ' search (S i).
      Proof.
        apply (limit_unique Q (fun n => ' search n)).
        - exact (islimit_cauchy_limit Q F search_sequence).
        - intro e; apply tr; exists (S i); intros n le.
          rewrite (search_seen _ _ le (seen_succ i p)), plus_negate_r.
          assert (epos := pos_rationals_to_field_qpos Q (F:=F) e).
          split; [apply flip_pos_negate|]; exact epos.
      Qed.
    End search.

    (** Let [h] be a map on [F] that restricts to [g] on the rationals. *)
    Context (h : F -> Bool) (hg : forall q, h (' q) = g q).

    (** Comparing [h] at the limit of the bisection and at the limit of the search sequence decides whether [P] never holds. *)
    Lemma wlpo_bisection : WLPO.
    Proof.
      intros P decP.
      set (b0 := h (cauchy_limit Q F bisect_sequence)).
      set (m := cauchy_limit Q F (search_sequence b0 P)).
      destruct (dec (h m = b0)) as [e|ne].
      - left; intros [i p].
        destruct (search_endpoint b0 P (S i) (seen_succ P i p)) as [j q].
        apply (endpoint_ne b0 j).
        rewrite <- hg, <- q, <- (search_limit_seen b0 P i p); exact e.
      - right; intros np; apply ne.
        exact (ap h (search_limit_never b0 P (fun n p => np (n; p)))).
    Qed.
  End bisection.

  (** Hence a map [F -> Bool] that takes two different values implies [WLPO]: we restrict it to the line through the two points, parametrized by the rationals. *)
  Lemma wlpo_nonconstant (f : F -> Bool) (x y : F) : f x <> f y -> WLPO.
  Proof.
    intros ne.
    assert (g01 : f (x + ' 0 * (y - x)) <> f (x + ' 1 * (y - x))).
    { assert (p0 : ' (0 : Q) = (0 : F)) by exact (preserves_0 (f:=cast Q F)).
      assert (p1 : ' (1 : Q) = (1 : F)) by exact (preserves_1 (f:=cast Q F)).
      rewrite p0, p1, mult_0_l, plus_0_r, mult_1_l, (plus_comm y), plus_assoc, plus_negate_r, plus_0_l.
      exact ne. }
    exact (wlpo_bisection (fun q => f (x + ' q * (y - x))) g01 (fun t => f (x + t * (y - x)))
             (fun q => idpath)).
  Qed.

  Definition wlpo_isstronglynonconstant (f : F -> Bool) : IsStronglyNonconstant f -> WLPO.
  Proof.
    apply Trunc_rec; intros [x h]; revert h; apply Trunc_rec; intros [y ne].
    exact (wlpo_nonconstant f x y ne).
  Defined.

  (** A choice of locators for all elements of [F] therefore implies [WLPO]. *)
  Definition wlpo_locator_choice (l : forall x : F, locator Q F x) : WLPO
    := wlpo_isstronglynonconstant _ (isstronglynonconstant_locator_choice_bool l).
End wlpo.

Section cuts.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}
    {Qroundup : RoundUpStrict@{_ UQ _ UQ} Q}.

  (** ** The properties and structures of a cut *)

  Section components.
    Context (L U : Q -> HProp).

    (** We write [q < x] for [L q] and [x < r] for [U r] in comments. The properties of a Dedekind cut [x = (L, U)]. *)

    Definition BoundedLower := hexists L.
    Definition BoundedUpper := hexists U.
    Definition ClosedLower := forall q q', q < q' -> L q' -> L q.
    Definition ClosedUpper := forall r r', r' < r -> U r' -> U r.
    Definition OpenLower := forall q, L q -> hexists (fun q' => prod (q < q') (L q')).
    Definition OpenUpper := forall r, U r -> hexists (fun r' => prod (r' < r) (U r')).
    Definition CutTransitive := forall q r, L q -> U r -> q < r.
    Definition CutLocated := forall q r, q < r -> hor (L q) (U r).

    (** Their structural counterparts; closedness and transitivity are their own counterparts. *)
    Definition LowerBound := {q : Q & L q}.
    Definition UpperBound := {r : Q & U r}.
    Definition LowerRounding := forall q, L q -> {q' : Q & prod (q < q') (L q')}.
    Definition UpperRounding := forall r, U r -> {r' : Q & prod (r' < r) (U r')}.
    Definition CutLocator := forall q r, q < r -> L q + U r.

    (** Being a Dedekind cut, a proposition. *)
    Record IsCut := {
      iscut_bounded_lower : BoundedLower ;
      iscut_bounded_upper : BoundedUpper ;
      iscut_closed_lower : ClosedLower ;
      iscut_closed_upper : ClosedUpper ;
      iscut_open_lower : OpenLower ;
      iscut_open_upper : OpenUpper ;
      iscut_transitive : CutTransitive ;
      iscut_located : CutLocated }.

    (** The structure of a Dedekind cut. *)
    Record CutStructure := {
      cutstructure_lower_bound : LowerBound ;
      cutstructure_upper_bound : UpperBound ;
      cutstructure_closed_lower : ClosedLower ;
      cutstructure_closed_upper : ClosedUpper ;
      cutstructure_lower_rounding : LowerRounding ;
      cutstructure_upper_rounding : UpperRounding ;
      cutstructure_transitive : CutTransitive ;
      cutstructure_locator : CutLocator }.

    Definition issig_iscut : _ <~> IsCut := ltac:(issig).

    #[export] Instance ishprop_iscut `{Funext} : IsHProp IsCut.
    Proof.
      exact (istrunc_equiv_istrunc _ issig_iscut).
    Qed.

    (** The structure of a cut gives the property, by truncating each component. *)
    Definition iscut_cutstructure (s : CutStructure) : IsCut.
    Proof.
      destruct s as [[q lq] [r ur] cl cu ol ou t l].
      snapply Build_IsCut.
      - exact (tr (q; lq)).
      - exact (tr (r; ur)).
      - exact cl.
      - exact cu.
      - intros q' lq'; exact (tr (ol q' lq')).
      - intros r' ur'; exact (tr (ou r' ur')).
      - exact t.
      - intros q' r' ltqr; exact (tr (l q' r' ltqr)).
    Defined.

    Definition iscut_merely_cutstructure `{Funext} : merely CutStructure -> IsCut
      := Trunc_rec iscut_cutstructure.

    (** The properties are those of [IsDedekindCut], with roundedness split into closedness and openness. *)
    Lemma iscut_iff_isdedekindcut : IsCut <-> IsDedekindCut Q L U.
    Proof.
      split.
      - intros [bl bu cl cu ol ou t l]; snapply Build_IsDedekindCut.
        + exact bl.
        + exact bu.
        + intro q; split; [exact (ol q)|].
          apply Trunc_rec; intros [q' [ltqq' lq']]; exact (cl q q' ltqq' lq').
        + intro r; split; [exact (ou r)|].
          apply Trunc_rec; intros [r' [ltr'r ur']]; exact (cu r r' ltr'r ur').
        + exact t.
        + exact l.
      - intros c; snapply Build_IsCut.
        + exact (cut_lower_inhabited c).
        + exact (cut_upper_inhabited c).
        + intros q q' ltqq' lq'; apply (snd (cut_lower_rounded c q)), tr; exact (q'; (ltqq', lq')).
        + intros r r' ltr'r ur'; apply (snd (cut_upper_rounded c r)), tr; exact (r'; (ltr'r, ur')).
        + intro q; exact (fst (cut_lower_rounded c q)).
        + intro r; exact (fst (cut_upper_rounded c r)).
        + exact (cut_transitive c).
        + exact (cut_located c).
    Qed.
  End components.

  (** ** Cuts with locators *)

  Section dedekind.
    Context `{Funext} `{Univalence}.
    Local Notation RD := (DedekindReals Q (Qlt:=Qlt)).
    Local Instance archimedean_RD {c : FieldCharacteristic RD 0}
      : ArchimedeanProperty Q RD (Achar:=c)
      := archimedean_property_change_char Q RD _ c (archimedean_dedekindreals Q).
    Local Existing Instance qinc.

    (** The order of the Dedekind reals with the rationals is given by the cuts, so a locator in the sense of the ordered field [RD] is the structural counterpart of locatedness. *)
    Lemma lt_rationals_dedekind_l (q : Q) (x : RD) : ' q < x <-> lower_cut Q x q.
    Proof.
      assert (p : ' q = rational_dedekind Q q) by exact (rationals_initial (h:=rational_dedekind Q) _).
      rewrite p.
      exact (lt_rational_dedekind_l Q q x).
    Qed.

    Lemma lt_rationals_dedekind_r (r : Q) (x : RD) : x < ' r <-> upper_cut Q x r.
    Proof.
      assert (p : ' r = rational_dedekind Q r) by exact (rationals_initial (h:=rational_dedekind Q) _).
      rewrite p.
      exact (lt_rational_dedekind_r Q r x).
    Qed.

    Definition cut_locator_iff_locator (x : RD)
      : CutLocator (lower_cut Q x) (upper_cut Q x) <-> locator Q RD x.
    Proof.
      split; intros l q r ltqr; generalize (l q r ltqr); apply functor_sum.
      1,3: apply lt_rationals_dedekind_l.
      all: apply lt_rationals_dedekind_r.
    Defined.

    (** A Dedekind real which merely has a locator is a Cauchy real. *)
    Lemma iscauchyreal_merely_locator (x : RD)
      : merely (locator Q RD x) -> IsCauchyReal Q RD x.
    Proof.
      intros l; apply (snd (iscauchyreal_iff_limit Q RD x)).
      exact (fst (merely_locator_iff_limit Q RD x) l).
    Qed.

    (** The Cauchy reals coincide with the Dedekind reals exactly when every Dedekind real is a Cauchy real, since the canonical map is an embedding. *)
    Lemma isequiv_cauchy_reals_to_dedekind_iff
      : (forall x : RD, IsCauchyReal Q RD x) <-> IsEquiv (cauchy_reals_to_field Q RD).
    Proof.
      split.
      - intros h.
        snapply isequiv_surj_emb.
        + exact (BuildIsSurjection _ h).
        + exact (isembedding_isinj_hset _ (isinj_cauchy_reals_to_field Q)).
      - intros e x; exact (tr ((cauchy_reals_to_field Q RD)^-1 x; eisretr _ x)).
    Qed.

    Context {L U : Q -> HProp} (c : IsCut L U).

    (** A cut with a locator has the full structure of a cut: bounds by bounded search, and openness from the Archimedean structure, using locators for rationals. *)
    Definition cut_dedekind : RD := Build_DedekindReals Q L U (fst (iscut_iff_isdedekindcut L U) c).

    Context (l : CutLocator L U).
    Local Definition l' : locator Q RD cut_dedekind := fst (cut_locator_iff_locator cut_dedekind) l.

    Definition lower_bound_cut_locator : LowerBound L.
    Proof.
      destruct (lower_bound Q RD l') as [q ltqx].
      exact (q; fst (lt_rationals_dedekind_l q cut_dedekind) ltqx).
    Defined.

    Definition upper_bound_cut_locator : UpperBound U.
    Proof.
      destruct (upper_bound Q RD l') as [r ltxr].
      exact (r; fst (lt_rationals_dedekind_r r cut_dedekind) ltxr).
    Defined.

    Definition lower_rounding_cut_locator : LowerRounding L.
    Proof.
      intros q lq.
      destruct (archimedean_structure Q RD (locator_left Q RD q) l'
                  (snd (lt_rationals_dedekind_l q cut_dedekind) lq)) as [q' [ltqq' ltq'x]].
      exact (q'; (strictly_order_reflecting _ _ _ ltqq', fst (lt_rationals_dedekind_l q' cut_dedekind) ltq'x)).
    Defined.

    Definition upper_rounding_cut_locator : UpperRounding U.
    Proof.
      intros r ur.
      destruct (archimedean_structure Q RD l' (locator_left Q RD r)
                  (snd (lt_rationals_dedekind_r r cut_dedekind) ur)) as [r' [ltxr' ltr'r]].
      exact (r'; (strictly_order_reflecting _ _ _ ltr'r, fst (lt_rationals_dedekind_r r' cut_dedekind) ltxr')).
    Defined.

    Definition cutstructure_iscut_locator : CutStructure L U
      := {| cutstructure_lower_bound := lower_bound_cut_locator;
            cutstructure_upper_bound := upper_bound_cut_locator;
            cutstructure_closed_lower := iscut_closed_lower L U c;
            cutstructure_closed_upper := iscut_closed_upper L U c;
            cutstructure_lower_rounding := lower_rounding_cut_locator;
            cutstructure_upper_rounding := upper_rounding_cut_locator;
            cutstructure_transitive := iscut_transitive L U c;
            cutstructure_locator := l |}.

    (** A cut which merely has a locator is a Cauchy real. *)
    Lemma iscauchyreal_iscut_merely_locator : merely (CutLocator L U) -> IsCauchyReal Q RD cut_dedekind.
    Proof.
      intros ml; apply iscauchyreal_merely_locator.
      exact (Trunc_functor _ (fst (cut_locator_iff_locator cut_dedekind)) ml).
    Qed.
  End dedekind.

  Section dedekind2.
    Context `{Funext} `{Univalence}.
    Local Notation RD := (DedekindReals Q (Qlt:=Qlt)).
    Local Existing Instance archimedean_RD.

    (** Hence a cut which merely has the structure of a cut is a Cauchy real. *)
    Lemma iscauchyreal_merely_cutstructure {L U : Q -> HProp} (s : merely (CutStructure L U))
      : IsCauchyReal Q RD (cut_dedekind (iscut_merely_cutstructure L U s)).
    Proof.
      exact (iscauchyreal_iscut_merely_locator _ (Trunc_functor _ (cutstructure_locator L U) s)).
    Qed.

    (** If every cut merely had the structure of a cut, every Dedekind real would be a Cauchy real, so that by [isequiv_cauchy_reals_to_dedekind_iff] the Cauchy reals and the Dedekind reals would coincide. This is not provable, since they differ in some models (Lubarsky, "On the Cauchy completeness of the constructive Cauchy reals"); here we only formalize the implication, not the model. *)
    Lemma iscauchyreal_all_merely_cutstructure
      (h : forall L U : Q -> HProp, IsCut L U -> merely (CutStructure L U)) (x : RD)
      : IsCauchyReal Q RD x.
    Proof.
      apply (iscauchyreal_merely_locator).
      refine (Trunc_functor _ _ (h _ _ (snd (iscut_iff_isdedekindcut _ _) (isdedekindcut Q x)))).
      intro s; exact (fst (cut_locator_iff_locator x) (cutstructure_locator _ _ s)).
    Qed.

    Context (Z : Type) {Zap : Apart Z} {Zplus : Plus Z} {Zmult : Mult Z}
      {Zzero : Zero Z} {Zone : One Z} {Zneg : Negate Z} {Zle : Le Z} {Zlt : Lt Z}
      {ZtoRing : IntegersToRing Z} {Zints : Integers Z} {Ztriv : TrivialApart Z}
      (d : nat) (dpos : (0 < d)%nat).

    (** Every Dedekind real merely has a signed-digit representation if and only if the Cauchy reals and the Dedekind reals coincide. *)
    Lemma signed_digits_iff_isequiv_cauchy_reals_to_dedekind
      : (forall x : RD, merely (SignedDigits Q RD Z d x)) <-> IsEquiv (cauchy_reals_to_field Q RD).
    Proof.
      refine (iff_compose _ isequiv_cauchy_reals_to_dedekind_iff).
      split; intros h x.
      - apply (iscauchyreal_merely_locator).
        exact (snd (merely_locator_iff_signed_digits Q RD Z d dpos x) (h x)).
      - apply (fst (merely_locator_iff_signed_digits Q RD Z d dpos x)).
        apply (snd (merely_locator_iff_limit Q RD x)).
        exact (fst (iscauchyreal_iff_limit Q RD x) (h x)).
    Qed.
  End dedekind2.
End cuts.
