From HoTT Require Import
  Basics DProp Misc.BoundedSearch Spaces.Finite.Fin ExcludedMiddle
  Modalities.ReflectiveSubuniverse Modalities.Identity
  Classes.interfaces.abstract_algebra
  Classes.interfaces.orders
  Classes.interfaces.rationals
  Classes.interfaces.cauchy
  Classes.interfaces.archimedean
  Classes.interfaces.round
  Classes.interfaces.naturals
  Classes.implementations.peano_naturals
  Classes.orders.archimedean
  Classes.orders.dec_fields
  Classes.orders.naturals
  Classes.orders.lattices
  Classes.theory.apartness
  Classes.theory.rationals
  Classes.orders.fields
  Classes.orders.rationals
  Classes.theory.fields
  Classes.theory.dec_fields.

Local Open Scope type_scope.

Section locator.
  Context (Q : Type).
  Context `{Qrats : Rationals Q}.
  Context {Qdec_paths : DecidablePaths Q}.
  Context {Qtriv : TrivialApart Q}.
  Context `{!Trichotomy (<)}.
  Context (F : Type).
  Context `{Forderedfield : OrderedField F}.
  Context {Fabs : Abs F}.
  Context {Farchimedean : ArchimedeanProperty Q F}.
  Context {Fcomplete : IsComplete Q F}.
  Context {Qroundup : RoundUpStrict Q}.

  Instance qinc : Cast Q F := rationals_to_field Q F.

  (* Definition of a locator for a fixed real number. *)
  Definition locator (x : F) := forall q r : Q, q < r -> (' q < x) + (x < ' r).

  (* Alternative definition; see equivalence below *)
  Record locator' (x : F) :=
    { locates_right : forall q r : Q, q < r -> DHProp
    ; locates_right_true : forall q r : Q, forall nu : q < r, locates_right q r nu -> ' q < x
    ; locates_right_false : forall q r : Q, forall nu : q < r, ~ locates_right q r nu -> x < ' r
    }.

  Arguments locates_right       [x] _ [q] [r] _.
  Arguments locates_right_true  [x] _ [q] [r] _.
  Arguments locates_right_false [x] _ [q] [r] _.

  Definition locates_left `{Funext} {x : F} (l : locator' x) {q r : Q} : q < r -> DHProp :=
    fun nu => Build_DHProp (Build_HProp (~ (locates_right l nu))) _.

  Section classical.
    Context `{ExcludedMiddle}.

    Lemma all_reals_locators (x : F) : locator x.
    Proof.
      intros q r ltqr.
      case (LEM (' q < x)).
      - exact _.
      - exact inl.
      - intros notlt.
        apply inr.
        assert (ltqr' : ' q < ' r)
          by auto.
        exact (nlt_lt_trans notlt ltqr').
    Qed.

  End classical.

  Section rational.
    Context (s : Q).

    Lemma locator_left : locator (' s).
    Proof.
      intros q r ltqr.
      destruct (trichotomy _ q s) as [ltqs|[eqqs|ltsq]].
      - apply inl. apply (strictly_order_preserving _); assumption.
      - rewrite eqqs in ltqr. apply inr, (strictly_order_preserving _); assumption.
      - apply inr, (strictly_order_preserving _), (transitivity ltsq ltqr); assumption.
    Qed.

    Definition locator_second : locator (' s).
    Proof.
      intros q r ltqr.
      destruct (trichotomy _ s r) as [ltsr|[eqsr|ltrs]].
      - apply inr, (strictly_order_preserving _); assumption.
      - rewrite <- eqsr in ltqr. apply inl, (strictly_order_preserving _); assumption.
      - apply inl, (strictly_order_preserving _), (transitivity ltqr ltrs).
    Qed.

  End rational.

  Section logic.

    Context {x : F}.

    Definition locator_locator' : locator x -> locator' x.
    Proof.
      intros l.
      refine (Build_locator' x (fun q r nu => Build_DHProp (Build_HProp (is_inl (l q r nu))) _) _ _).
      - intros q r nu. simpl. apply un_inl.
      - intros q r nu. simpl. destruct (l q r nu) as [ltqx|].
        + simpl; intros f; destruct (f tt).
        + intros ?; assumption.
    Defined.

    Definition locator'_locator : locator' x -> locator x.
    Proof.
      intros l' q r nu.
      destruct (dec (locates_right l' nu)) as [yes|no].
      - apply inl. exact (locates_right_true l' nu yes).
      - apply inr. exact (locates_right_false l' nu no).
    Defined.
  End logic.

  Section logic2.

    Context `{Funext} `{Univalence} {x : F}.

    Coercion locator_locator' : locator >-> locator'.

    Definition locator_locator'_locator (l : locator x) : locator'_locator (locator_locator' l) = l.
    Proof.
      apply path_forall; intros q.
      apply path_forall; intros r.
      apply path_forall; intros nu.
      unfold locator'_locator, locator_locator'. simpl.
      destruct (l q r nu); auto.
    Qed.

    Local Definition locsig : _ <~> locator' x := ltac:(issig).

    Lemma locator'_locator_locator' (l' : locator' x)
      : locator_locator' (locator'_locator l') = l'.
    Proof.
      enough (p : locsig ^-1 (locator_locator' (locator'_locator l')) = locsig ^-1 l').
      - exact (equiv_inj (locsig ^-1) p).
      - unfold locsig; simpl.
        destruct l'; unfold locator'_locator, locator_locator'; simpl.
        apply path_sigma_hprop; simpl.
        apply path_forall; intro q;
          apply path_forall; intro r;
            apply path_arrow; intro nu.
        apply equiv_path_dhprop; simpl.
        rewrite (path_dec (locates_right0 q r nu)).
        destruct (dec (locates_right0 q r nu)); auto.
    Qed.

    Definition equiv_locator_locator' : locator x <~> locator' x
      := equiv_adjointify
           locator_locator'
           locator'_locator
           locator'_locator_locator'
           locator_locator'_locator.

    Lemma nltqx_locates_left {q r : Q} (l' : locator' x) (ltqr : q < r)
      : ~ (' q < x) -> locates_left l' ltqr.
    Proof.
      assert (f := locates_right_true l' ltqr).
      exact (not_contrapositive f).
    Qed.

    Lemma ltxq_locates_left {q r : Q} (l' : locator' x) (ltqr : q < r)
      : x < ' q -> locates_left l' ltqr.
    Proof.
      intros ltxq. apply nltqx_locates_left.
      apply lt_flip; assumption.
    Qed.

    Lemma nltxr_locates_right {q r : Q} (l' : locator' x) (ltqr : q < r)
      : ~ (x < ' r) -> locates_right l' ltqr.
    Proof.
      intros nltxr.
      apply stable.
      assert (f := locates_right_false l' ltqr).
      exact (not_contrapositive f nltxr).
    Qed.

    Lemma ltrx_locates_right {q r : Q} (l' : locator' x) (ltqr : q < r)
      : 'r < x -> locates_right l' ltqr.
    Proof.
      intros ltrx. apply nltxr_locates_right.
      apply lt_flip; assumption.
    Qed.

  End logic2.

  Local Open Scope mc_scope.

  Local Notation nQ := (naturals_to_semiring nat Q).

  Definition locator_minus {x : F} (l : locator x) : locator (-x).
  Proof.
    intros q r ltqr.
    destruct (l (- r) (- q) (snd (flip_lt_negate q r) ltqr)) as [ltrx|ltxq].
    - right; apply char_minus_left; rewrite <- preserves_negate; exact ltrx.
    - left; apply char_minus_right; rewrite <- preserves_negate; exact ltxq.
  Qed.

  (** ** Rational bounds *)

  Section bounds.
    Context {x : F} (l : locator x).

    (** To find a rational below [x], we ask the locator to compare [x] with [- n - 1 < - n] for [n = 0, 1, 2, ...], until it places [x] above [- n - 1]. *)
    Local Definition lt_negate_nat (n : nat) : - nQ n - 1 < - nQ n
      := fst (pos_minus_lt_compat_r _ 1) lt_0_1.

    Local Definition locates_above_negate_nat (n : nat) : DHProp
      := locates_right l (lt_negate_nat n).

    (** This happens for some [n], since [x] lies above some rational, which lies above some [- n]. *)
    Local Lemma merely_locates_above_negate_nat : hexists locates_above_negate_nat.
    Proof.
      assert (lt : x - 1 < x) by apply pos_minus_lt_compat_r, lt_0_1.
      assert (h := archimedean_property Q F (x - 1) x lt).
      strip_truncations.
      destruct h as [q [_ ltqx]].
      destruct (round_up_strict Q (- q)) as [n ltqn].
      apply tr; exists n.
      apply ltrx_locates_right.
      rhs_V' exact ltqx.
      apply (strictly_order_preserving (cast Q F)), flip_lt_negate_l, ltqn.
    Qed.

    Definition lower_bound : {q : Q | ' q < x}.
    Proof.
      destruct (minimal_n locates_above_negate_nat _ merely_locates_above_negate_nat)
        as [n above].
      exact (- nQ n - 1; locates_right_true l (lt_negate_nat n) above).
    Qed.

  End bounds.

  Definition upper_bound {x : F} (l : locator x) : {r : Q | x < ' r}.
  Proof.
    destruct (lower_bound (locator_minus l)) as [q ltqx].
    exists (- q).
    rewrite (preserves_negate (f:=cast Q F)).
    apply flip_lt_negate_r, ltqx.
  Qed.

  (** ** Tight bounds *)

  Section tight_bound.
    Context {x : F} (l : locator x) (e : Qpos Q).

    (** We step through the rationals in steps of [d = e / 3], starting at [q - d] for a rational [q < x]. *)
    Local Definition d : Q := ' (e / 3).

    Local Definition start : Q := (lower_bound l).1 - d.

    Local Definition grid (k : nat) : Q := start + nQ k * d.

    Local Lemma grid_succ (k : nat) : grid (S k) = grid k + d.
    Proof.
      unfold grid; rewrite nat_to_semiring_succ, (plus_comm 1), plus_mult_distr_r, mult_1_l.
      apply plus_assoc.
    Qed.

    Local Definition lt_grid_succ (k : nat) : grid k < grid (S k).
    Proof.
      rewrite grid_succ; apply pos_plus_lt_compat_r, pos_is_pos.
    Defined.

    Local Definition locates_above_grid (k : nat) : DHProp := locates_right l (lt_grid_succ k).

    Local Lemma grid_1 : grid 1 = (lower_bound l).1.
    Proof.
      unfold grid, start; change (nQ 1) with 1; rewrite mult_1_l.
      apply minus_plus_cancel.
    Qed.

    Local Lemma lt_grid (r : Q) : {n : nat & r < grid n}.
    Proof.
      destruct (round_up_strict Q ((r - start) / d)) as [n ltn].
      exists n; unfold grid; rewrite plus_comm.
      assert (dpos : 0 < d) by apply pos_is_pos.
      apply flip_lt_minus_l, (flip_lt_mult_dec_recip_l (r - start) (nQ n) d dpos), ltn.
    Defined.

    Local Lemma locates_above_grid_0 : locates_above_grid 0.
    Proof.
      apply ltrx_locates_right; rewrite grid_1; exact (lower_bound l).2.
    Qed.

    Local Lemma not_locates_above_grid : {n : nat & ~ locates_above_grid n}.
    Proof.
      destruct (upper_bound l) as [r ltxr], (lt_grid r) as [n ltrn].
      exists n; intros above.
      assert (ltgx := locates_right_true l (lt_grid_succ n) above).
      apply (lt_flip (' grid n) x ltgx).
      lhs' exact ltxr; apply (strictly_order_preserving (cast Q F)), ltrn.
    Qed.

    (** Where the answer changes, [x] lies between [grid k] and [grid (k + 2) = grid k + 2 d < grid k + e]. *)
    Lemma tight_bound : {u : Q | ' u < x < ' (u + ' e)}.
    Proof.
      destruct (sperners_lemma_1d_nat locates_above_grid locates_above_grid_0
                  _ not_locates_above_grid.2) as [k [above below]].
      exists (grid k); split.
      - exact (locates_right_true l (lt_grid_succ k) above).
      - lhs' exact (locates_right_false l (lt_grid_succ (S k)) below).
        apply (strictly_order_preserving (cast Q F)).
        rewrite 2!grid_succ, <- plus_assoc.
        apply (strictly_order_preserving (grid k +)), qpos_two_thirds_lt.
    Qed.

  End tight_bound.

  (** ** The Archimedean structure *)

  Section arch_struct.

    Context {x y : F}
            (l : locator x)
            (m : locator y)
            (ltxy : x < y).

    Local Definition precision (n : nat) : Qpos Q := / ' (S n).

    Local Lemma precision_lt (d : Q) (dpos : 0 < d) : {n : nat & ' (precision n) < d}.
    Proof.
      destruct (round_up_strict Q (/ d)) as [n ltn].
      exists n; apply flip_lt_dec_recip_l; [exact dpos|].
      change (/ d < nQ (S n)); rewrite nat_to_semiring_succ.
      lhs' exact ltn; apply pos_plus_lt_compat_l, lt_0_1.
    Qed.

    Local Definition approx (n : nat) : Q := (tight_bound l (precision n / 2)).1.

    (** We search for an [n] for which the locator for [y] places [y] above [approx n + e / 2], comparing it with [approx n + e / 2 < approx n + e]; this happens once [e] is less than [y - x]. *)
    Local Definition locates_above_approx (n : nat) : DHProp
      := locates_right m (strictly_order_preserving (approx n +)
                            (' (precision n / 2)) (' precision n)
                            (qpos_half_lt (precision n))).

    Local Lemma merely_locates_above_approx : hexists locates_above_approx.
    Proof.
      assert (ltyx : 0 < y - x) by exact (snd (flip_pos_minus x y) ltxy).
      assert (h := archimedean_property Q F 0 (y - x) ltyx).
      strip_truncations; destruct h as [d [ltd ltdyx]].
      assert (dpos : 0 < d) by apply rationals_to_field_pos_iff, ltd.
      destruct (precision_lt d dpos) as [n ltn].
      apply tr; exists n; apply ltrx_locates_right.
      apply flip_lt_minus_r in ltdyx; rhs_V' exact ltdyx.
      rewrite (preserves_plus (f:=cast Q F)), (plus_comm (' approx n)).
      apply plus_lt_compat.
      - apply (strictly_order_preserving (cast Q F)), ltn.
      - exact (fst (tight_bound l (precision n / 2)).2).
    Qed.

    Definition archimedean_structure : {q : Q | x < 'q < y}.
    Proof.
      destruct (minimal_n locates_above_approx _ merely_locates_above_approx)
        as [n above].
      exists (approx n + ' (precision n / 2)); split.
      - exact (snd (tight_bound l (precision n / 2)).2).
      - napply (locates_right_true m); exact above.
    Qed.

  End arch_struct.

  (** ** Cotransitivity *)

  Definition locator_cotransitive {x y z : F} (l : locator x) (m : locator y) (n : locator z)
    : x < y -> (x < z) + (z < y).
  Proof.
    intros ltxy.
    destruct (archimedean_structure l m ltxy) as [q [ltxq ltqy]].
    destruct (archimedean_structure (locator_left q) m ltqy) as [r [ltqr ltry]].
    destruct (n q r (strictly_order_reflecting (cast Q F) q r ltqr)) as [ltqz|ltzr].
    - exact (inl (transitivity ltxq ltqz)).
    - exact (inr (transitivity ltzr ltry)).
  Defined.

  Definition locator_cotransitive_rational {x y : F} (l : locator x) (m : locator y) (s : Q)
    : x < y -> (x < ' s) + (' s < y)
    := locator_cotransitive l m (locator_left s).

  (** ** Reciprocals *)

  Section recip_pos.
    Context {x : F} (l : locator x) (xpos : 0 < x).

    Local Definition recip_nu := positive_apart_zero x xpos.

    Local Lemma mult_dec_recip_cast (r : Q) (rpos : 0 < r) : ' r * ' (/ r) = 1.
    Proof.
      rewrite <- (preserves_mult (f:=cast Q F)), dec_recip_inverse.
      - exact (preserves_1 (f:=cast Q F)).
      - apply lt_ne_flip, rpos.
    Qed.

    Definition locator_recip_pos : locator (// (x ; recip_nu)).
    Proof.
      intros q r ltqr.
      assert (recip_pos : 0 < // (x ; recip_nu)) by apply pos_recip_compat.
      destruct (trichotomy (<) q 0) as [qneg|[qzero|qpos]].
      - left; rhs_V' exact recip_pos.
        rewrite <- (preserves_0 (f:=cast Q F)); apply (strictly_order_preserving (cast Q F)), qneg.
      - left; rewrite qzero, (preserves_0 (f:=cast Q F)); exact recip_pos.
      - assert (rpos := transitivity qpos ltqr).
        destruct (l (/ r) (/ q) (flip_lt_dec_recip r q qpos ltqr)) as [ltrx|ltxq].
        + right; apply char_recip_pos_right.
          rewrite <- (mult_dec_recip_cast r rpos).
          apply (strictly_order_preserving (' r *.)), ltrx.
        + left; apply char_recip_pos_left.
          rewrite <- (mult_dec_recip_cast q qpos).
          apply (strictly_order_preserving (' q *.)), ltxq.
    Qed.
  End recip_pos.

  Section recip_neg.
    Context {x : F} (l : locator x) (xneg : x < 0).

    Local Definition recip_neg_nu := negative_apart_zero x xneg.

    Definition locator_recip_neg : locator (// (x ; recip_neg_nu)).
    Proof.
      assert (negxpos : 0 < - x) by exact (fst (flip_neg_negate x) xneg).
      assert (l' := locator_minus (locator_recip_pos (locator_minus l) negxpos)).
      refine (transport locator _ l').
      rewrite recip_negate; apply recip_proper_alt, negate_involutive.
    Qed.
  End recip_neg.

  Definition locator_recip {x : F} (l : locator x) (nu : x ≶ 0) : locator (// (x ; nu)).
  Proof.
    destruct (fst (apart_iff_total_lt x 0) nu) as [xneg|xpos].
    - rewrite <- (recip_irrelevant x (recip_neg_nu xneg) nu).
      exact (locator_recip_neg l xneg).
    - rewrite <- (recip_irrelevant x (recip_nu xpos) nu).
      exact (locator_recip_pos l xpos).
  Qed.

  (** ** Binary operations *)

  Section binary_ops.

    Context {x y : F}
            (l : locator x)
            (m : locator y).

    Definition locator_plus : locator (x + y).
    Proof.
      intros q r ltqr.
      set (e := Qpos_diff q r ltqr / 2).
      destruct (tight_bound m e) as [u [ltuy ltyu]].
      assert (ltue : q - u < q - u + ' e) by apply pos_plus_lt_compat_r, pos_is_pos.
      destruct (l (q - u) (q - u + ' e) ltue) as [ltx|ltx].
      - left; rewrite <- (minus_plus_cancel q u), (preserves_plus (f:=cast Q F)).
        apply plus_lt_compat; [exact ltx|exact ltuy].
      - right.
        assert (p : q - u + ' e + (u + ' e) = r).
        { rewrite plus_swap_middle, minus_plus_cancel.
          rhs rapply (plus_conjugate_alt r q); apply (ap (q +)).
          exact (ap (cast (Qpos Q) Q) (pos_split2 (Qpos_diff q r ltqr)))^. }
        rewrite <- p, (preserves_plus (f:=cast Q F)).
        apply plus_lt_compat; [exact ltx|exact ltyu].
    Qed.

    Lemma locator_meet : locator (meet x y).
    Proof.
      intros q r ltqr.
      destruct (l q r ltqr, m q r ltqr) as [[ltqx|ltxr] [ltqy|ltyr]].
      - apply inl, meet_lt_l; assumption.
      - apply inr, meet_lt_r_r; assumption.
      - apply inr, meet_lt_r_l; assumption.
      - apply inr, meet_lt_r_r; assumption.
    Qed.

    Lemma locator_join : locator (join x y).
    Proof.
      intros q r ltqr.
      destruct (l q r ltqr, m q r ltqr) as [[ltqx|ltxr] [ltqy|ltyr]].
      - apply inl, join_lt_l_l; assumption.
      - apply inl, join_lt_l_l; assumption.
      - apply inl, join_lt_l_r; assumption.
      - apply inr, join_lt_r; assumption.
    Qed.

  End binary_ops.

  (** ** Approximations *)

  Definition qpos_upper_bound {x : F} (l : locator x) : {B : Qpos Q & x < ' (' B)}.
  Proof.
    destruct (upper_bound (locator_join l (locator_left 0))) as [r ltr].
    destruct (fst (char_join_right r x (' 0)) ltr) as [ltxr lt0r].
    assert (r0 : 0 < r) by (apply (strictly_order_reflecting (cast Q F)), lt0r).
    exact (mkQpos r r0; ltxr).
  Defined.

  Local Lemma lt_trisect (q r : Q) (ltqr : q < r)
    : q + ' (Qpos_diff q r ltqr / 3) < r - ' (Qpos_diff q r ltqr / 3).
  Proof.
    set (e := Qpos_diff q r ltqr / 3).
    assert (p : q + (' e + ' e + ' e) = r).
    { rhs napply (Qpos_diff_pr q r ltqr).
      exact (ap (q +) (ap (cast (Qpos Q) Q) (pos_split3 (Qpos_diff q r ltqr))))^. }
    apply (snd (flip_lt_minus_r (' e) r (q + ' e))).
    rewrite <- p, !plus_assoc.
    apply pos_plus_lt_compat_r, pos_is_pos.
  Qed.

  (** We work in a reflective subuniverse [O] so that this also applies to Dedekind cuts: for the identity modality and the predicates [' q < x] and [x < ' r], the conclusion is a locator for [x], and for the propositional truncation it is the locatedness of a cut. *)
  Definition located_from_approximations (O : ReflectiveSubuniverse) {L U : Q -> Type}
    (La Ua : Qpos Q -> Q -> Type) (loc : forall e q r, q < r -> O (La e q + Ua e r))
    (lower : forall e q, La e (q + ' e) -> L q) (upper : forall e r, Ua e (r - ' e) -> U r)
    (q r : Q) (ltqr : q < r)
    : O (L q + U r)
    := let e := Qpos_diff q r ltqr / 3 in
       O_functor O (functor_sum (lower e q) (upper e r))
         (loc e (q + ' e) (r - ' e) (lt_trisect q r ltqr)).

  Definition locator_close {z : F}
    (approx : forall e : Qpos Q, {y : F & prod (locator y) (y - ' (' e) < z < y + ' (' e))})
    : locator z.
  Proof.
    srapply (located_from_approximations purely (fun e q => ' q < (approx e).1)
               (fun e r => (approx e).1 < ' r)).
    - exact (fun e => fst (approx e).2).
    - intros e q lt; cbv beta in lt |- *.
      rewrite (preserves_plus (f:=cast Q F)) in lt.
      rhs_V' exact (fst (snd (approx e).2)).
      apply flip_lt_minus_r, lt.
    - intros e r lt; cbv beta in lt |- *.
      rewrite (preserves_minus (f:=cast Q F)) in lt.
      lhs' exact (snd (snd (approx e).2)).
      apply flip_lt_minus_r, lt.
  Defined.

  Definition locator_from_approx {z : F}
    (approx : forall e : Qpos Q, {p : Q | ' (p - ' e) < z < ' (p + ' e)})
    : locator z.
  Proof.
    apply locator_close; intros e.
    destruct (approx e) as [p [lo hi]].
    exists (' p); split; [apply locator_left|].
    rewrite <- (preserves_minus (f:=cast Q F)), <- (preserves_plus (f:=cast Q F)).
    exact (lo, hi).
  Defined.

  (** ** Multiplication *)

  Section times.

    Local Definition mult_precision (Z : Q) (Zpos : 0 < Z) (e : Qpos Q)
      : {d : Q & prod (prod (0 < d) (d < 1)) (d * (Z + Z + 1) < ' e)}.
    Proof.
      assert (Z1pos : 0 < Z + Z + 1).
      { apply pos_plus_compat; [apply pos_plus_compat; assumption|exact lt_0_1]. }
      set (K := ' e + (Z + Z + 1)).
      assert (Kpos : 0 < K) by (apply pos_plus_compat; [apply e|exact Z1pos]).
      set (d := ' e / K).
      assert (dpos : 0 < d) by (apply pos_mult; [apply e|apply pos_dec_recip_compat, Kpos]).
      assert (dK : d * K = ' e) by (apply dec_recip_mult_cancel_r, lt_ne_flip, Kpos).
      exists d; refine ((dpos, _), _).
      - apply (strictly_order_reflecting (.* K)).
        rewrite dK, mult_1_l.
        apply pos_plus_lt_compat_r, Z1pos.
      - rewrite <- dK; unfold K.
        rewrite (plus_mult_distr_l d (' e) (Z + Z + 1)), (commutativity (d * ' e)).
        apply pos_plus_lt_compat_r, pos_mult; [exact dpos|apply pos_is_pos].
    Defined.

    Local Lemma lt_bound_tight {u v d : F} (dpos : 0 < d) (ltuv : u < v) (ltvu : v < u + d)
      : - d < v - u < d.
    Proof.
      apply between_iff_lt_minus; split; [|exact ltvu].
      exact (transitivity (fst (pos_minus_lt_compat_r u d) dpos) ltuv).
    Qed.

    Local Lemma lt_bound_tight_succ {u v d Z : F} (d1 : d < 1) (ltuv : u < v) (ltvu : v < u + d)
      (ltZv : - Z < v < Z)
      : - (Z + 1) < u < Z + 1.
    Proof.
      split.
      - rewrite negate_plus_distr.
        apply flip_lt_minus_l in ltvu; rhs_V' exact ltvu.
        apply plus_lt_compat; [apply ltZv|].
        apply (snd (flip_lt_negate d 1)), d1.
      - lhs' exact ltuv; lhs' exact (snd ltZv).
        apply pos_plus_lt_compat_r, lt_0_1.
    Qed.

    Local Lemma mult_tight_bound {x y a c d Z : F} (ltZx : - Z < x < Z) (ltZy : - Z < y < Z)
      (dpos : 0 < d) (d1 : d < 1) (ltxa : a < x < a + d) (ltyc : c < y < c + d)
      : - (d * (Z + Z + 1)) < x * y - a * c < d * (Z + Z + 1).
    Proof.
      assert (p : Z * d + d * (Z + 1) = d * (Z + Z + 1)).
      { rewrite (mult_comm Z d), <- plus_mult_distr_l, plus_assoc; reflexivity. }
      rewrite <- p.
      apply (mult_minus_mult_lt_bound x y a c Z (Z + 1) d ltZx).
      - exact (lt_bound_tight_succ d1 (fst ltyc) (snd ltyc) ltZy).
      - exact (lt_bound_tight dpos (fst ltxa) (snd ltxa)).
      - exact (lt_bound_tight dpos (fst ltyc) (snd ltyc)).
    Qed.

    Context {x y : F}
            (l : locator x)
            (m : locator y).

    (** We bound [x] and [y] by a positive rational [Z]. For a precision [e], we choose [d] as in [mult_precision] and rationals [a < x < a + d] and [c < y < c + d]; then [x y] is within [d (2 Z + 1) < e] of [a c]. *)
    Definition locator_times : locator (x * y).
    Proof.
      pose (lJ := locator_join (locator_join l (locator_minus l))
                    (locator_join m (locator_minus m))).
      destruct (qpos_upper_bound lJ) as [[Z Zpos] ltJZ].
      destruct (between_join_negate x y (' Z) ltJZ) as [ltZx ltZy].
      apply locator_from_approx; intros e.
      destruct (mult_precision Z Zpos e) as [d [[dpos ltd1] ltdZe]].
      destruct (tight_bound l (mkQpos d dpos)) as [a ltxa].
      destruct (tight_bound m (mkQpos d dpos)) as [c ltyc].
      exists (a * c).
      rewrite (preserves_plus (f:=cast Q F)) in ltxa, ltyc.
      change (' (mkQpos d dpos)) with d in ltxa, ltyc.
      assert (dpos' : 0 < ' d) by exact (fst (rationals_to_field_pos_iff d) dpos).
      assert (ltd1' : ' d < 1).
      { rewrite <- (preserves_1 (f:=cast Q F)).
        apply (strictly_order_preserving (cast Q F)), ltd1. }
      assert (lte : ' d * (' Z + ' Z + 1) < ' (' e)).
      { apply (strictly_order_preserving (cast Q F)) in ltdZe.
        rewrite (preserves_mult (f:=cast Q F)), 2!(preserves_plus (f:=cast Q F)),
          (preserves_1 (f:=cast Q F)) in ltdZe.
        exact ltdZe. }
      rewrite (preserves_minus (f:=cast Q F) (a * c) (' e)),
        (preserves_plus (f:=cast Q F) (a * c) (' e)), (preserves_mult (f:=cast Q F) a c).
      apply between_iff_lt_minus.
      rapply between_weaken; [exact (mult_tight_bound ltZx ltZy dpos' ltd1' ltxa ltyc)|exact lte].
    Defined.

  End times.

  Section limit.

    Context {xs : nat -> F}.
    Context {M} {M_ismod : CauchyModulus Q F xs M}.
    Context (ls : forall n, locator (xs n)).

    Lemma locator_limit {l} : IsLimit _ _ xs l -> locator l.
    Proof.
      intros islim; apply locator_close; intros e.
      exists (xs (M (e / 2))); split.
      - apply ls.
      - exact (modulus_close_limit Q F xs islim e).
    Qed.

  End limit.

End locator.
