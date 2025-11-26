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

  Context `{Funext} `{Univalence}.

  (* Assume we have enumerations of the rationals, and of pairs of ordered rationals. *)
  Context (Q_eq : nat <~> Q).
  Context (QQpos_eq : nat <~> Q * Qpos Q).

  Instance qinc : Cast Q F := rationals_to_field Q F.
  (* TODO The following two instances should probably come from the `Rationals` instance. *)
  Context (cast_pres_ordering : StrictlyOrderPreserving qinc)
          (qinc_strong_presving : IsSemiRingStrongPreserving qinc).
  Existing Instance cast_pres_ordering.
  Existing Instance qinc_strong_presving.

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

  Definition locates_left {x : F} (l : locator' x) {q r : Q} : q < r -> DHProp :=
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

    Context {x : F}.

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

  Local Definition ltQnegQ (q : Q) (eps : Qpos Q) : q - 'eps < q.
  Proof.
    apply (pos_minus_lt_compat_r q ('eps)), eps.
  Qed.
  
  Local Open Scope mc_scope.

  Local Definition ltQposQ (q : Q) (eps : Qpos Q) : q < q + 'eps.
  Proof.
    apply (pos_plus_lt_compat_r q ('eps)), eps.
  Qed.

  Section bounds.
    (* Given a real with a locator, we can find (integer) bounds. *)
    Context {x : F}
            (l : locator x).

    Local Definition ltN1 (q : Q) : q - 1 < q := ltQnegQ q 1.

    Local Definition P_lower (q : Q) : Type := locates_right l (ltN1 q).

    Definition P_lower_prop {k} : IsHProp (P_lower k).
    Proof.
      apply _.
    Qed.

    Local Definition ltxN1 : x - 1 < x := (fst (pos_minus_lt_compat_r x 1) lt_0_1).

    Local Definition P_lower_inhab : hexists (fun q => P_lower q).
    Proof.
      assert (hqlt : hexists (fun q => ' q < x)).
      {
        assert (hex := archimedean_property Q F (x-1) x ltxN1).
        refine (Trunc_rec _ hex); intros hex'.
        apply tr.
        destruct hex' as [q [ltx1q ltqx]]; exists q; assumption.
      }
      refine (Trunc_rec _ hqlt); intros hqlt'.
      induction hqlt' as [q lt].
      apply tr.
      exists q.
      unfold P_lower.
      apply ltrx_locates_right; assumption.
    Qed.

    Definition lower_bound : {q : Q | ' q < x}.
    Proof.
      assert (qP_lower : {q : Q | P_lower q})
        by exact (minimal_n_alt_type Q Q_eq P_lower _ P_lower_inhab).
      destruct qP_lower as [q Pq].
      exists (q - 1).
      unfold P_lower in Pq. simpl in *.
      exact (un_inl _ Pq).
    Qed.

    Local Definition lt1N (r : Q) : r < r + 1 := ltQposQ r 1.

    Local Definition P_upper (r : Q) : DHProp := locates_left l (lt1N r).

    Definition P_upper_prop {k} : IsHProp (P_upper k).
    Proof.
      apply _.
    Qed.

    Local Definition ltx1N : x < x + 1 := (fst (pos_plus_lt_compat_r x 1) lt_0_1).

    Local Definition P_upper_inhab : hexists (fun r => P_upper r).
    Proof.
      assert (hqlt : hexists (fun r => x < ' r)).
      {
        assert (hex := archimedean_property Q F x (x+1) ltx1N).
        refine (Trunc_rec _ hex); intros hex'.
        apply tr.
        destruct hex' as [r [ltxr ltrx1]]; exists r; assumption.
      }
      refine (Trunc_rec _ hqlt); intros hqlt'.
      induction hqlt' as [r lt].
      apply tr.
      exists r.
      unfold P_upper.
      apply ltxq_locates_left; assumption.
    Qed.

    Definition upper_bound : {r : Q | x < ' r}.
    Proof.
      assert (rP_upper : {r : Q | P_upper r})
        by exact (minimal_n_alt_type Q Q_eq P_upper _ P_upper_inhab).
      destruct rP_upper as [r Pr].
      exists (r + 1).
      unfold P_upper in Pr. simpl in *.
      destruct (l r (r + 1) (lt1N r)).
      - simpl in Pr. destruct (Pr tt).
      - assumption.
    Qed.

    Instance inc_N_Q : Cast nat Q := naturals_to_semiring nat Q.

    Instance inc_fin_N {n} : Cast (Fin n) nat := fin_to_nat.

    Lemma tight_bound (epsilon : Qpos Q) : {u : Q | ' u < x < ' (u + ' epsilon)}.
    Proof.
      destruct
        lower_bound as [q ltqx]
      , upper_bound as [r ltxr]
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
      clear - l q ltqx r ltxr n lt3rqn lt0' ap30 Qtriv Qdec_paths H cast_pres_ordering.
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
        - apply strictly_order_preserving; try trivial.
      }
      destruct (sperners_lemma_1d P left_true right_false) as [u [Pltux Pltxueps]].
      exists (grid (fin_incl (fin_incl u))).
      unfold P in Pltux, Pltxueps.
      split.
      - exact (locates_right_true l (lt_grid (fin_incl u)) Pltux).
      - clear - Pltxueps Qtriv Qdec_paths ap30 cast_pres_ordering.
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

    Local Definition P (qeps' : Q * Qpos Q) : Type :=
      match qeps' with
      | (q' , eps') =>
        (prod
           (locates_left l (ltQnegQ q' eps'))
           (locates_right m (ltQposQ q' eps')))
      end.

    Local Definition P_isHProp qeps' : IsHProp (P qeps').
    Proof.
      destruct qeps' as [q eps'].
      exact istrunc_prod.
    Qed.

    Local Definition P_dec qeps' : Decidable (P qeps').
    Proof.
      destruct qeps' as [q eps'].
      unfold P.
      exact _.
    Qed.

    Local Definition P_inhab : hexists P.
    Proof.
      assert (hs := (archimedean_property Q F x y ltxy)).
      refine (Trunc_ind _ _ hs); intros [s [ltxs ltsy]].
      assert (ht := (archimedean_property Q F ('s) y ltsy)).
      refine (Trunc_ind _ _ ht); intros [t [ltst' ltty]].
      set (q := (t + s) / 2).
      assert (ltst : s < t).
      {
        Existing Instance full_pseudo_order_reflecting.
        exact (strictly_order_reflecting _ _ _ ltst').
      }
      set (epsilon := (Qpos_diff s t ltst) / 2).
      apply tr.
      exists (q, epsilon).
      unfold P; split.
      - apply ltxq_locates_left.
        assert (q - ' epsilon = s) as ->.
        {
          unfold q; cbn.
          rewrite <- path_avg_split_diff_l.
          rewrite <- (plus_assoc s ((t-s)/2) (-((t-s)/2))).
          rewrite plus_negate_r.
          rewrite plus_0_r.
          reflexivity.
        }
        assumption.
      - apply ltrx_locates_right.
        assert (q + ' epsilon = t) as ->.
        {
          unfold q; cbn.
          rewrite <- path_avg_split_diff_r.
          rewrite <- (plus_assoc t (-((t-s)/2)) ((t-s)/2)).
          rewrite plus_negate_l.
          rewrite plus_0_r.
          reflexivity.
        }
        assumption.
    Qed.

    Definition archimedean_structure : {q : Q | x < 'q < y}.
    Proof.
      assert (R : sig P).
      {
        apply minimal_n_alt_type.
        - exact QQpos_eq.
        - exact P_dec.
        - exact P_inhab.
      }
      unfold P in R.
      destruct R as [[q eps] [lleft mright]].
      exists q; split.
      - exact (locates_right_false l _ lleft).
      - exact (locates_right_true  m _ mright).
    Qed.

  End arch_struct.

  Section unary_ops.

    Context {x : F}
            (l : locator x).

    Definition locator_minus : locator (-x).
    Proof.
      intros q r ltqr.
      assert (ltnrnq := snd (flip_lt_negate q r) ltqr : -r < -q).
      destruct (l _ _ ltnrnq) as [ltnrx|ltxnq].
      - apply inr. apply char_minus_left. rewrite <- preserves_negate. assumption.
      - apply inl. apply char_minus_right. rewrite <- preserves_negate. assumption.
    Qed.

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

    (** TODO the following two should be proven in Classes/orders/archimedean.v *)
    Context (char_plus_left : forall (q : Q) (x y : F),
                ' q < x + y <-> hexists (fun s : Q => (' s < x) /\ (' (q - s) < y)))
            (char_plus_right : forall (r : Q) (x y : F),
                x + y < ' r <-> hexists (fun t : Q => (x < ' t) /\ (y < ' (r - t)))).

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
        by apply ltQposQ.
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

    (* TODO construct locators for multiplications. *)
    Lemma locator_times : locator (x * y).
    Proof. Abort.

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
