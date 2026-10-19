From HoTT Require Import
  Basics DProp Misc.BoundedSearch Spaces.Finite.Fin ExcludedMiddle
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
      : ~ (' q < x) -> ~ locates_right l' ltqr.
    Proof.
      assert (f := locates_right_true l' ltqr).
      exact (not_contrapositive f).
    Qed.

    Lemma ltxq_locates_left {q r : Q} (l' : locator' x) (ltqr : q < r)
      : x < ' q -> ~ locates_right l' ltqr.
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

  Definition locator_minus {x : F} (l : locator x) : locator (-x).
  Proof.
    intros q r ltqr.
    assert (ltnrnq := snd (flip_lt_negate q r) ltqr : -r < -q).
    destruct (l _ _ ltnrnq) as [ltnrx|ltxnq].
    - apply inr. apply char_minus_left. rewrite <- preserves_negate. assumption.
    - apply inl. apply char_minus_right. rewrite <- preserves_negate. assumption.
  Qed.

  (** Given a real with a locator, we can find integer bounds: we search for the least [n : nat] for which the locator places [x] above [- n - 1] when comparing it with [- n - 1 < - n]. *)
  Definition lower_bound {x : F} (l : locator x) : {q : Q | ' q < x}.
  Proof.
    pose (P n := locates_right l
                   (fst (pos_minus_lt_compat_r (- naturals_to_semiring nat Q n) 1) lt_0_1)).
    assert (inhab : hexists P).
    { refine (Trunc_functor _ _ (archimedean_property Q F (x - 1) x
                                   (fst (pos_minus_lt_compat_r x 1) lt_0_1))).
      intros [q [_ ltqx]].
      destruct (round_up_strict Q (- q)) as [n ltqn].
      exists n; apply ltrx_locates_right.
      rhs_V' exact ltqx.
      apply (strictly_order_preserving _), flip_lt_negate_l, ltqn. }
    destruct (minimal_n P _ inhab) as [n Pn].
    eexists; exact (locates_right_true l _ Pn).
  Qed.

  Definition upper_bound {x : F} (l : locator x) : {r : Q | x < ' r}.
  Proof.
    destruct (lower_bound (locator_minus l)) as [q ltqx].
    exists (- q).
    rewrite (preserves_negate (f:=cast Q F)).
    apply flip_lt_negate_r, ltqx.
  Qed.

  Section bounds.
    Context {x : F}
            (l : locator x).

    Instance inc_N_Q : Cast nat Q := naturals_to_semiring nat Q.

    Instance inc_fin_N {n} : Cast (Fin n) nat := fin_to_nat.

    Lemma tight_bound (epsilon : Qpos Q) : {u : Q | ' u < x < ' (u + ' epsilon)}.
    Proof.
      destruct
        (lower_bound l) as [q ltqx]
      , (upper_bound l) as [r ltxr]
      , (round_up_strict Q ((3/'epsilon)*(r-q))) as [n lt3rqn].
      assert (lt0 : 0 < 'epsilon / 3).
      {
        apply pos_mult.
        - apply epsilon.
        - apply pos_dec_recip_compat, lt_0_3.
      }
      assert (lt0' : 0 < 3 / ' epsilon).
      {
        apply pos_mult.
        - exact lt_0_3.
        - apply pos_dec_recip_compat, epsilon.
      }
      assert (ap30 : (3 : Q) <> 0)
        by apply lt_ne_flip, lt_0_3.
      clear - l q ltqx r ltxr n lt3rqn lt0' ap30 Qtriv Qdec_paths.
      assert (ltn3eps : r < q + ' n * ' epsilon / 3).
      {
        rewrite (commutativity q (' n * ' epsilon / 3)).
        apply flip_lt_minus_l.
        apply (pos_mult_reflect_r (3 / ' epsilon) lt0').
        rewrite (commutativity (r-q) (3 / ' epsilon)).
        rewrite <- (associativity ('n) ('epsilon) (/3)).
        rewrite <- (associativity ('n) (' epsilon / 3) (3 / ' epsilon)).
        rewrite <- (associativity ('epsilon) (/3) (3/'epsilon)).
        rewrite (associativity (/3) 3 (/'epsilon)).
        rewrite (commutativity (/3) 3).
        rewrite (dec_recip_inverse 3 ap30).
        rewrite mult_1_l.
        assert (apepsilon0 : 'epsilon <> 0)
          by apply lt_ne_flip, epsilon.
        rewrite (dec_recip_inverse ('epsilon) apepsilon0).
        rewrite mult_1_r.
        assumption.
      }
      set (grid (k : Fin n.+3) := q + (' (' k) - 1)*('epsilon/3) : Q).
      assert (lt_grid : forall k : Fin _, grid (fin_incl k) < grid (fsucc k)).
      {
        intros k. unfold grid.
        change (' fin_incl k) with (fin_to_nat (fin_incl k));
          rewrite path_nat_fin_incl.
        change (' fsucc k) with (fin_to_nat (fsucc k));
          rewrite path_nat_fsucc.
        assert (' (S (' k)) = (' (' k) + 1)) as ->.
        {
          rewrite S_nat_plus_1.
          rewrite (preserves_plus (' k) 1).
          rewrite preserves_1.
          reflexivity.
        }
        assert (' (' k) + 1 - 1 = ' (' k) - 1 + 1) as ->.
        {
          rewrite <- (associativity _ 1 (-1)).
          rewrite (commutativity 1 (-1)).
          rewrite (associativity _ (-1) 1).
          reflexivity.
        }
        assert (lt1 : ' (' k) - 1 < ' (' k) - 1 + 1)
          by apply pos_plus_lt_compat_r, lt_0_1.
        assert (lt2 : (' (' k) - 1) * (' epsilon / 3) < (' (' k) - 1 + 1) * (' epsilon / 3)).
        {
          nrefine (pos_mult_lt_r ('epsilon/3) _ (' (' k) - 1) (' (' k) - 1 + 1) _); try exact _.
          exact lt1.
        }
        apply pseudo_srorder_plus.
        exact lt2.
      }
      set (P k := locates_right l (lt_grid k)).
      assert (left_true : P fin_zero).
      {
        apply ltrx_locates_right.
        unfold grid.
        change (' fsucc fin_zero) with (fin_to_nat (@fsucc (S n) fin_zero)).
        rewrite path_nat_fsucc, path_nat_fin_zero.
        rewrite (@preserves_1 nat Q _ _ _ _ _ _ _ _ _ _).
        rewrite plus_negate_r.
        rewrite mult_0_l.
        rewrite plus_0_r.
        assumption.
      }
      assert (right_false : ~ P fin_last).
      {
        apply ltxq_locates_left.
        unfold grid.
        change (' fin_incl fin_last) with (fin_to_nat (@fin_incl (S (S n)) fin_last)).
        rewrite path_nat_fin_incl, path_nat_fin_last.
        rewrite S_nat_plus_1.
        rewrite (preserves_plus n 1).
        rewrite (@preserves_1 nat Q _ _ _ _ _ _ _ _ _ _).
        rewrite <- (associativity (' n) 1 (-1)).
        rewrite plus_negate_r.
        rewrite plus_0_r.
        rewrite (associativity ('n) ('epsilon) (/3)).
        transitivity ('r).
        - exact ltxr.
        - rapply strictly_order_preserving; exact ltn3eps.
      }
      destruct (sperners_lemma_1d P left_true right_false) as [u [Pltux Pltxueps]].
      exists (grid (fin_incl (fin_incl u))).
      unfold P in Pltux, Pltxueps.
      split.
      - exact (locates_right_true l (lt_grid (fin_incl u)) Pltux).
      - clear - Pltxueps Qtriv Qdec_paths ap30.
        set (ltxbla := locates_right_false l (lt_grid (fsucc u)) Pltxueps).
        unfold grid in *.
        change (' fin_incl (fin_incl u)) with (fin_to_nat (fin_incl (fin_incl u))).
        rewrite path_nat_fin_incl, path_nat_fin_incl.
        change (' fsucc (fsucc u)) with (fin_to_nat (fsucc (fsucc u))) in ltxbla.
        rewrite path_nat_fsucc, path_nat_fsucc in ltxbla.
        rewrite S_nat_plus_1, S_nat_plus_1 in ltxbla.
        rewrite (preserves_plus (fin_to_nat u + 1) 1) in ltxbla.
        rewrite (preserves_plus (fin_to_nat u) 1) in ltxbla.
        rewrite preserves_1 in ltxbla.
        rewrite <- (associativity (' fin_to_nat u) 1 1) in ltxbla.
        rewrite <- (associativity (' fin_to_nat u) 2 (-1)) in ltxbla.
        rewrite (commutativity 2 (-1)) in ltxbla.
        rewrite (associativity (' fin_to_nat u) (-1) 2) in ltxbla.
        rewrite plus_mult_distr_r in ltxbla.
        rewrite (associativity q ((' fin_to_nat u - 1) * (' epsilon / 3)) (2 * (' epsilon / 3))) in ltxbla.
        refine (transitivity ltxbla _).
        apply strictly_order_preserving; try apply _.
        apply pseudo_srorder_plus.
        rewrite (associativity 2 ('epsilon) (/3)).
        rewrite (commutativity 2 ('epsilon)).
        rewrite <- (mult_1_r ('epsilon)).
        rewrite <- (associativity ('epsilon) 1 2).
        rewrite (mult_1_l 2).
        rewrite <- (associativity ('epsilon) 2 (/3)).
        apply pos_mult_lt_l.
        + apply epsilon.
        + nrefine (pos_mult_reflect_r (3 : Q) lt_0_3 _ _ _); try exact _.
          rewrite <- (associativity 2 (/3) 3).
          rewrite (commutativity (/3) 3).
          rewrite (dec_recip_inverse (3 : Q) ap30).
          rewrite (mult_1_r 2).
          rewrite (mult_1_l 3).
          exact lt_2_3.
    Qed.

  End bounds.

  Section arch_struct.

    Context {x y : F}
            (l : locator x)
            (m : locator y)
            (ltxy : x < y).

    (** The precision [1 / (n + 1)], which drops below every positive rational. *)
    Local Definition precision (n : nat) : Qpos Q := / ' (S n).

    Local Lemma precision_lt (d : Q) (dpos : 0 < d) : {n : nat & ' (precision n) < d}.
    Proof.
      destruct (round_up_strict Q (/ d)) as [n ltn].
      exists n; apply flip_lt_dec_recip_l; [exact dpos|].
      change (/ d < naturals_to_semiring nat Q (S n)).
      rewrite S_nat_plus_1, (preserves_plus n 1), preserves_1.
      lhs' exact ltn.
      apply pos_plus_lt_compat_r, lt_0_1.
    Qed.

    (** We search for the least [n] such that, for [e] the [n]-th precision and [u < x < u + e / 2], the locator of [y] places [y] above [u + e / 2] when comparing it with [u + e / 2 < u + e]. *)
    Definition archimedean_structure : {q : Q | x < 'q < y}.
    Proof.
      pose (u n := (tight_bound l (precision n / 2)).1).
      pose (P n := locates_right m
                     (fst (pos_plus_lt_compat_r (u n + ' (precision n / 2)) (' (precision n / 2)))
                        (pos_is_pos _))).
      assert (inhab : hexists P).
      { refine (Trunc_functor _ _ (archimedean_property Q F 0 (y - x)
                                     (snd (flip_pos_minus _ _) ltxy))).
        intros [d [ltd ltdyx]].
        destruct (precision_lt d) as [n ltn].
        { apply (strictly_order_reflecting (cast Q F)).
          rewrite (preserves_0 (f:=cast Q F)); exact ltd. }
        exists n; apply ltrx_locates_right.
        rewrite <- plus_assoc.
        change (' (precision n / 2) + ' (precision n / 2))
          with (' (precision n / 2 + precision n / 2) : Q).
        rewrite <- pos_split2.
        rewrite (preserves_plus (f:=cast Q F)), (plus_comm (' u n)).
        rhs_V' exact (fst (flip_lt_minus_r _ _ _) ltdyx).
        apply plus_lt_compat.
        - apply (strictly_order_preserving _), ltn.
        - exact (fst (tight_bound l _).2). }
      destruct (minimal_n P _ inhab) as [n Pn].
      exists (u n + ' (precision n / 2)); split.
      - exact (snd (tight_bound l _).2).
      - exact (locates_right_true m _ Pn).
    Qed.

  End arch_struct.

  (** For reals [x] and [y] with locators and a rational [s], if [x < y] then we can choose between [x < s] and [s < y]. *)
  Definition locator_cotransitive_rational {x y : F} (l : locator x) (m : locator y) (s : Q)
    : x < y -> (x < ' s) + (' s < y).
  Proof.
    intros ltxy.
    destruct (archimedean_structure l m ltxy) as [q [ltxq ltqy]].
    destruct (trichotomy _ q s) as [ltqs|[eqqs|ltsq]].
    - apply inl; lhs' exact ltxq.
      rapply strictly_order_preserving; assumption.
    - apply inl; rewrite <- eqqs; assumption.
    - apply inr; rhs_V' exact ltqy.
      rapply strictly_order_preserving; assumption.
  Defined.

  (** Strong cotransitivity: for reals [x < y] with locators and a real [z] with a locator, we can choose between [x < z] and [z < y]. *)
  Definition locator_cotransitive {x y z : F} (l : locator x) (m : locator y) (n : locator z)
    : x < y -> (x < z) + (z < y).
  Proof.
    intros ltxy.
    destruct (archimedean_structure l m ltxy) as [q [ltxq ltqy]].
    destruct (archimedean_structure (locator_left q) m ltqy) as [r [ltqr ltry]].
    destruct (n q r (strictly_order_reflecting _ _ _ ltqr)) as [ltqz|ltzr].
    - exact (inl (transitivity ltxq ltqz)).
    - exact (inr (transitivity ltzr ltry)).
  Defined.

  Section unary_ops.

    Context {x : F}
            (l : locator x).

    Section recip_pos.
      Context (xpos : 0 < x).

      Local Definition recip_nu := positive_apart_zero x xpos.

      Definition locator_recip_pos : locator (// (x ; recip_nu)).
      Proof.
        assert (recippos : 0 < // (x ; recip_nu))
          by apply pos_recip_compat.
        intros q r ltqr. destruct (trichotomy _ q 0) as [qneg|[qzero|qpos]].
        + apply inl. refine (transitivity _ _).
          * apply (strictly_order_preserving _). exact qneg.
          * rewrite preserves_0; assumption.
        + apply inl. rewrite qzero, preserves_0; assumption.
        + assert (qap0 : q ≶ 0)
            by exact (pseudo_order_lt_apart_flip _ _ qpos).
          assert (rap0 : r ≶ 0).
          {
            refine (pseudo_order_lt_apart_flip _ _ _).
            exact (transitivity qpos ltqr).
          }
          assert (ltrrrq : / r < / q)
            by (apply flip_lt_dec_recip; assumption).
          destruct (l (/r) (/q) ltrrrq) as [ltrrx|ltxrq].
          * apply inr.
            assert (rpos : 0 < r)
              by (transitivity q; assumption).
            assert (rpos' : 0 < ' r).
            {
              rewrite <- (@preserves_0 Q F _ _ _ _ _ _ _ _ _ _).
              apply strictly_order_preserving; try exact _; assumption.
            }
            rewrite (dec_recip_to_recip r (positive_apart_zero ('r) rpos')) in ltrrx.
            assert (ltxrr := flip_lt_recip_l x ('r) rpos' ltrrx).
            cbn in ltxrr.
            rewrite
              (recip_irrelevant
                 x
                 (positive_apart_zero
                    x
                    (transitivity (pos_recip_compat (' r) rpos') ltrrx)) recip_nu) in ltxrr.
            exact ltxrr.
          * apply inl.
            assert (qpos' : 0 < ' q).
            {
              rewrite <- (@preserves_0 Q F _ _ _ _ _ _ _ _ _ _).
              apply strictly_order_preserving; try exact _; assumption.
            }
            rewrite (dec_recip_to_recip q (positive_apart_zero ('q) qpos')) in ltxrq.
            assert (ltrqx := flip_lt_recip_r ('q) x qpos' xpos ltxrq).
            rewrite (recip_irrelevant x (positive_apart_zero x xpos) recip_nu) in ltrqx.
            exact ltrqx.
      Qed.
    End recip_pos.

  End unary_ops.

  Section recip_neg.
    Context {x : F}
            (l : locator x)
            (xneg : x < 0).

    Local Definition recip_neg_nu := negative_apart_zero x xneg.

    Definition locator_recip_neg : locator (// (x ; recip_neg_nu)).
    Proof.
      assert (negxpos : 0 < (-x))
        by (apply flip_neg_negate; assumption).
      assert (l' := locator_minus (locator_recip_pos (locator_minus l) negxpos)).
      rewrite (recip_negate (-x)) in l'.
      unfold negate_apart in l'.
      rewrite
        (recip_proper_alt
           (- - x)
           x
           (apart_negate (- x) (positive_apart_zero (- x) negxpos)) recip_neg_nu)
        in l'.
      - assumption.
      - apply negate_involutive.
    Qed.

  End recip_neg.

  Section unary_ops2.

    Context {x : F}
            (l : locator x)
            (nu : x ≶ 0).

    Definition locator_recip : locator (// (x ; nu)).
    Proof.
      destruct (fst (apart_iff_total_lt x 0) nu) as [xneg|xpos].
      - set (l' := locator_recip_neg l xneg).
        rewrite (recip_proper_alt x x (negative_apart_zero x xneg) nu) in l';
          try reflexivity; exact l'.
      - set (l' := locator_recip_pos l xpos).
        rewrite (recip_proper_alt x x (positive_apart_zero x xpos) nu) in l';
          try reflexivity; exact l'.
    Qed.

  End unary_ops2.

  Section binary_ops.

    Context {x y : F}
            (l : locator x)
            (m : locator y).

    Definition locator_plus : locator (x + y).
    Proof.
      intros q r ltqr.
      set (epsilon := (Qpos_diff q r ltqr) / 2).
      assert (q+'epsilon=r-'epsilon)
        by (rewrite path_avg_split_diff_l, path_avg_split_diff_r; reflexivity).
      destruct (tight_bound m epsilon) as [u [ltuy ltyuepsilon]].
      set (s := q-u).
      assert (qsltx : 'q-'s<y).
      {
        unfold s.
        rewrite (preserves_plus q (-u)).
        rewrite negate_plus_distr.
        rewrite (associativity ('q) (-'q) (-'(-u))).
        rewrite plus_negate_r.
        rewrite plus_0_l.
        rewrite (preserves_negate u).
        rewrite negate_involutive.
        assumption.
      }
      assert (sltseps : s<s+' epsilon)
        by apply pos_plus_lt_compat_r, pos_is_pos.
      destruct (l s (s+' epsilon) sltseps) as [ltsx|ltxseps].
      - apply inl. apply char_plus_left. apply tr; exists s; split; try assumption.
        rewrite preserves_minus; assumption.
      - apply inr. apply char_plus_right. apply tr.
        set (t := s + ' epsilon); exists t.
        split; try assumption.
        assert (r-(q-u+(r-q)/2)=u+'epsilon) as ->.
        {
          change ((r - q) / 2) with ('epsilon).
          rewrite negate_plus_distr.
          rewrite <- negate_swap_l.
          rewrite (plus_comm (-q) u).
          rewrite (plus_assoc r (u-q) (-'epsilon)).
          rewrite (plus_assoc r u (-q)).
          rewrite (plus_comm r u).
          rewrite <- (plus_assoc u r (-q)).
          rewrite <- (plus_assoc u (r-q) (-'epsilon)).
          rewrite (plus_comm r (-q)).
          rewrite <- (plus_assoc (-q) r (-'epsilon)).
          rewrite path_avg_split_diff_r.
          rewrite <- path_avg_split_diff_l.
          rewrite (plus_assoc (-q) q ((r-q)/2)).
          rewrite (plus_negate_l q).
          rewrite (plus_0_l _).
          reflexivity.
        }
        assumption.
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

  (** A real number that has rational approximations of any precision has a locator. *)
  Definition locator_from_approx {z : F}
    (approx : forall e : Qpos Q, {p : Q | ' (p - ' e) < z < ' (p + ' e)})
    : locator z.
  Proof.
    intros q r ltqr.
    set (e := (Qpos_diff q r ltqr) / 2).
    assert (qeer : q + ' e + ' e = r).
    { assert (p : q + ' e = r - ' e)
        by (rewrite path_avg_split_diff_l, path_avg_split_diff_r; reflexivity).
      rewrite p, <- plus_assoc, plus_negate_l, plus_0_r; reflexivity. }
    destruct (approx e) as [p [ltpz ltzp]].
    destruct (trichotomy _ (q + ' e) p) as [ltqep|[eqqep|ltpqe]].
    - apply inl. rhs_V' exact ltpz.
      apply (strictly_order_preserving _), flip_lt_minus_r; assumption.
    - apply inl. rewrite <- eqqep, <- plus_assoc, plus_negate_r, plus_0_r in ltpz.
      exact ltpz.
    - apply inr. lhs' exact ltzp.
      rapply strictly_order_preserving.
      rewrite <- qeer.
      apply (strictly_order_preserving (+ ' e)); assumption.
  Defined.

  Section times.

    (** For positive rationals [Z] and [e], a rational [0 < d < 1] with [d (2 Z + 1) < e]: we take [d = e / (e + 2 Z + 1)]. *)
    Local Definition mult_precision (Z : Q) (Zpos : 0 < Z) (e : Qpos Q)
      : {d : Q & prod (prod (0 < d) (d < 1)) (d * (Z + Z + 1) < ' e)}.
    Proof.
      assert (Z1pos : 0 < Z + Z + 1).
      { apply pos_plus_compat; [apply pos_plus_compat; assumption|exact lt_0_1]. }
      set (K := ' e + (Z + Z + 1)).
      assert (Kpos : 0 < K) by (apply pos_plus_compat; [apply e|exact Z1pos]).
      set (d := ' e / K).
      assert (dpos : 0 < d)
        by (apply pos_mult; [apply e|apply pos_dec_recip_compat, Kpos]).
      assert (dK : d * K = ' e).
      { unfold d. rewrite <- (associativity (' e)), (commutativity (/ K)).
        rewrite dec_recip_inverse; [apply mult_1_r|].
        apply lt_ne_flip, Kpos. }
      exists d; refine ((dpos, _), _).
      - apply (strictly_order_reflecting (.* K)).
        rewrite dK, mult_1_l.
        exact (fst (pos_plus_lt_compat_r _ _) Z1pos).
      - rewrite <- dK. unfold K.
        rewrite (plus_mult_distr_l d (' e) (Z + Z + 1)), (commutativity (d * ' e)).
        apply (fst (pos_plus_lt_compat_r _ _)), pos_mult; [assumption|apply e].
    Defined.

    (** If [u < v < u + d], then [v] is within [d] of [u]. *)
    Local Lemma lt_bound_tight {u v d : F} (dpos : 0 < d) (ltuv : u < v) (ltvu : v < u + d)
      : - d < v - u < d.
    Proof.
      split.
      - rhs_V' exact (snd (flip_pos_minus _ _) ltuv).
        apply flip_pos_negate, dpos.
      - apply flip_lt_minus_l; rewrite (commutativity d); assumption.
    Qed.

    (** If moreover [- Z < v < Z] and [d < 1], then [- (Z + 1) < u < Z + 1]. *)
    Local Lemma lt_bound_tight_succ {u v d Z : F} (d1 : d < 1) (ltuv : u < v) (ltvu : v < u + d)
      (ltZv : - Z < v < Z)
      : - (Z + 1) < u < Z + 1.
    Proof.
      split.
      - rewrite negate_plus_distr.
        rhs_V' exact (snd (flip_lt_minus_l _ _ _) ltvu).
        apply plus_lt_compat; [apply ltZv|].
        apply (snd (flip_lt_negate _ _)); assumption.
      - refine (transitivity ltuv (transitivity (snd ltZv) _)).
        apply (fst (pos_plus_lt_compat_r _ _)), lt_0_1.
    Qed.

    Context {x y : F}
            (l : locator x)
            (m : locator y).

    (** If [x] and [y] have locators, then so does [x * y]. *)
    Definition locator_times : locator (x * y).
    Proof.
      (* The absolute values of [x] and [y], and hence their maximum, have locators. This gives a rational bound [Z]. *)
      destruct (upper_bound (locator_join (locator_join l (locator_minus l))
                                          (locator_join m (locator_minus m))))
        as [Z ltJZ].
      destruct (between_join_negate x y (' Z) ltJZ) as [ltZx ltZy].
      assert (Zpos : 0 < Z).
      { apply (strictly_order_reflecting qinc).
        rewrite preserves_0.
        exact (pos_between_negate _ _ ltZx). }
      apply locator_from_approx; intros e.
      (* We approximate [x] and [y] up to [d], so that [x y] is approximated up to [Z d + d (Z + 1) < e]. *)
      destruct (mult_precision Z Zpos e) as [d [[dpos ltd1] ltdZe]].
      destruct (tight_bound l (mkQpos d dpos)) as [a [ltax ltxa]].
      destruct (tight_bound m (mkQpos d dpos)) as [c [ltcy ltyc]].
      exists (a * c).
      rewrite (preserves_plus (f:=cast Q F)) in ltxa, ltyc.
      change (' (mkQpos d dpos)) with d in ltxa, ltyc.
      assert (dpos' : (0 : F) < ' d).
      { rewrite <- (preserves_0 (f:=cast Q F)); apply (strictly_order_preserving _), dpos. }
      assert (ltd1' : ' d < (1 : F)).
      { rewrite <- (preserves_1 (f:=cast Q F)); apply (strictly_order_preserving _), ltd1. }
      destruct (mult_minus_mult_lt_bound x y (' a) (' c) (' Z) (' Z + 1) (' d)
                  ltZx (lt_bound_tight_succ ltd1' ltcy ltyc ltZy)
                  (lt_bound_tight dpos' ltax ltxa) (lt_bound_tight dpos' ltcy ltyc))
        as [lo hi].
      assert (ltbound : ' Z * ' d + ' d * (' Z + 1) < ' (' e)).
      { assert (p : ' Z * ' d + ' d * (' Z + 1) = ' (d * (Z + Z + 1))).
        { rewrite (preserves_mult (f:=cast Q F)), 2!(preserves_plus (f:=cast Q F)),
            (preserves_1 (f:=cast Q F)).
          rewrite (commutativity (' Z) (' d)), <- plus_mult_distr_l, plus_assoc.
          reflexivity. }
        rewrite p; apply (strictly_order_preserving _), ltdZe. }
      rewrite (preserves_minus (f:=cast Q F) (a * c) (' e)),
        (preserves_plus (f:=cast Q F) (a * c) (' e)), (preserves_mult (f:=cast Q F) a c).
      split.
      - rewrite (commutativity (' a * ' c)).
        apply flip_lt_minus_r.
        exact (transitivity (snd (flip_lt_negate _ _) ltbound) lo).
      - rewrite (commutativity (' a * ' c)).
        apply flip_lt_minus_l.
        exact (transitivity hi ltbound).
    Defined.

  End times.

  Section limit.

    Context {xs : nat -> F}.
    Context {M} {M_ismod : CauchyModulus Q F xs M}.
    Context (ls : forall n, locator (xs n)).

    Lemma locator_limit {l} : IsLimit _ _ xs l -> locator l.
    Proof.
      intros islim.
      intros q r ltqr.
      set (epsilon := (Qpos_diff q r ltqr) / 3).
      (* TODO we are doing trisection so we have the inequality: *)
      assert (ltqepsreps : q + ' epsilon < r - ' epsilon).
      {
        apply (strictly_order_reflecting (+'epsilon)).
        rewrite <- (plus_assoc r (-'epsilon) ('epsilon)).
        rewrite plus_negate_l.
        rewrite plus_0_r.
        rewrite <- (plus_assoc q ('epsilon) ('epsilon)).
        apply (strictly_order_reflecting ((-q)+)).
        rewrite (plus_assoc (-q) q _).
        rewrite plus_negate_l, plus_0_l.
        rewrite (plus_comm (-q) r).
        rewrite <- (mult_1_r ('epsilon)).
        rewrite <- plus_mult_distr_l.
        unfold epsilon, cast, Qpos_diff; cbn.
        rewrite <- (mult_assoc (r-q) (/3) 2).
        pattern (r-q) at 2.
        rewrite <- (mult_1_r (r-q)).
        assert (rqpos : 0 < r-q) by apply (Qpos_diff q r ltqr).
        apply (strictly_order_preserving ((r-q)*.)).
        apply (strictly_order_reflecting (3*.)).
        rewrite (mult_assoc 3 (/3) 2).
        rewrite (dec_recip_inverse 3).
        - rewrite mult_1_r, mult_1_l. exact lt_2_3.
        - apply apart_ne, positive_apart_zero, lt_0_3.
      }
      destruct (ls (M (epsilon / 2)) (q + ' epsilon) (r - ' epsilon) ltqepsreps)
        as [ltqepsxs|ltxsreps].
      + apply inl.
        rewrite preserves_plus in ltqepsxs.
        assert (ltqxseps : ' q < xs (M (epsilon / 2)) - ' (' epsilon))
          by (apply flip_lt_minus_r; assumption).
        refine (transitivity ltqxseps _).
        apply (modulus_close_limit _ _ _ _ _).
      + apply inr.
        rewrite (preserves_plus r (-'epsilon)) in ltxsreps.
        rewrite (preserves_negate ('epsilon)) in ltxsreps.
        assert (ltxsepsr : xs (M (epsilon / 2)) + ' (' epsilon) < ' r)
          by (apply flip_lt_minus_r; assumption).
        refine (transitivity _ ltxsepsr).
        apply (modulus_close_limit _ _ _ _ _).
    Qed.

  End limit.

End locator.
