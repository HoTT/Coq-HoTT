Require Import
        HoTT.Basics
        HoTT.DProp
        HoTT.BoundedSearch
        HoTT.Types.Universe
        HoTT.Types.Sum
        HoTT.Types.Arrow
        HoTT.Spaces.Finite
        HoTT.ExcludedMiddle
        HoTT.Todo.

Require Import
        HoTT.Classes.interfaces.abstract_algebra
        HoTT.Classes.interfaces.orders
        HoTT.Classes.interfaces.integers
        HoTT.Classes.interfaces.rationals
        HoTT.Classes.interfaces.naturals
        HoTT.Classes.interfaces.cauchy
        HoTT.Classes.interfaces.archimedean
        HoTT.Classes.interfaces.round
        HoTT.Classes.interfaces.naturals
        HoTT.Classes.implementations.peano_naturals
        HoTT.Classes.orders.orders
        HoTT.Classes.orders.archimedean
        HoTT.Classes.orders.rings
        HoTT.Classes.orders.dec_fields
        HoTT.Classes.orders.semirings
        HoTT.Classes.orders.lattices
        HoTT.Classes.theory.rings
        HoTT.Classes.theory.rationals.

Section locator.
  Generalizable Variables Qap Qplus Qmult Qzero Qone Qneg Qrecip Qle Qlt Qrats_to_field.
  Generalizable Variables Fap Fplus Fmult Fzero Fone Fneg Frecip Fle Flt Fjoin Fmeet.
  Context (Q : Type).
  Context `{Qrats : @Rationals Q Qap Qplus Qmult Qzero Qone Qneg Qrecip Qle Qlt Qrats_to_field}.
  Context {Qdec_paths : DecidablePaths Q}.
  Context {Qtriv : @TrivialApart Q Qap}.
  Context `{!Trichotomy (<)}.
  Context (F : Type).
  Context `{Forderedfield : @OrderedField F Flt Fle Fap Fzero Fone Fplus Fneg Fmult Fap Fzero Frecip Fjoin Fmeet}.
  Context {Fabs : Abs F}.
  Context {Farchimedean : ArchimedeanProperty Q F}.
  Context {Fcomplete : IsComplete Q F}.
  Context {Qroundup : @RoundUpStrict Q _ _ _ _ _ _ _ _ _ _ _}.

  Context `{Funext} `{Univalence}.

  (* Assume we have an enumeration of the rationals. *)
  Axiom Q_eq : nat <~> Q.

  Section rats_inclusion.

    Definition qinc : Cast Q F := rationals_to_field Q F.

    Axiom cast_pres_ordering : StrictlyOrderPreserving qinc.

  End rats_inclusion.

  Existing Instance qinc.
  Existing Instance cast_pres_ordering.

  (* Definition of a locator for a fixed real number. *)
  Definition locator (x : F) := forall q r : Q, q < r -> (' q < x) + (x < ' r).

  Record locator' (x : F) :=
    { locates_right : forall q r : Q, q < r -> DHProp
    ; locates_right_true : forall q r : Q, forall nu : q < r, locates_right q r nu -> ' q < x
    ; locates_right_false : forall q r : Q, forall nu : q < r, ~ locates_right q r nu -> x < ' r
    }.

  Arguments locates_right       [x] _ [q] [r] _.
  Arguments locates_right_true  [x] _ [q] [r] _.
  Arguments locates_right_false [x] _ [q] [r] _.
  Check (locates_right : forall x : F, locator' x -> forall q r : Q, q < r -> DHProp).
  Context `{Funext}.
  Definition locates_left {x : F} (l : locator' x) {q r : Q} : q < r -> DHProp :=
    fun nu => Build_DHProp (BuildhProp (~ (locates_right l nu))) _.

  Section classical.
    Context `{ExcludedMiddle}.

    Lemma all_reals_locators (x : F) : locator x.
    Proof.
      intros q r ltqr.
      case (LEM (' q < x)).
      - refine _.
      - exact inl.
      - intros notlt.
        refine (inr _).
        assert (ltqr' : ' q < ' r) by auto.
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
    Defined.

    Definition locator_second : locator (' s).
    Proof.
      intros q r ltqr.
      destruct (trichotomy _ s r) as [ltsr|[eqsr|ltrs]].
      - apply inr, (strictly_order_preserving _); assumption.
      - rewrite <- eqsr in ltqr. apply inl, (strictly_order_preserving _); assumption.
      - apply inl, (strictly_order_preserving _), (transitivity ltqr ltrs).
    Defined.

  End rational.

  Section logic.

    Context {x : F}.

    Definition locator_locator' : locator x -> locator' x.
    Proof.
      intros l.
      refine (Build_locator' x (fun q r nu => Build_DHProp (BuildhProp (is_inl (l q r nu))) _) _ _).
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
    Defined.

    Let locsig : _ <~> locator' x := ltac:(issig).
    Lemma locator'_locator_locator' (l' : locator' x): locator_locator' (locator'_locator l') = l'.
    Proof.
      enough (p : locsig ^-1 (locator_locator' (locator'_locator l')) = locsig ^-1 l').
      - refine (equiv_inj (locsig ^-1) p).
      - unfold locsig; clear locsig; simpl.
        destruct l'; unfold locator'_locator, locator_locator'; simpl.
        apply path_sigma_hprop; simpl.
        apply path_forall; intro q;
          apply path_forall; intro r;
            apply path_arrow; intro nu.
        apply equiv_path_dhprop; simpl.
        rewrite (path_dec (locates_right0 q r nu)).
        destruct (dec (locates_right0 q r nu)); auto.
    Defined.

    (* TODO build the equivalence object *)

    Lemma nltqx_locates_left {q r : Q} (l' : locator' x) (ltqr : q < r) : ~ ' q < x -> locates_left l' ltqr.
    Proof.
      assert (f := locates_right_true l' ltqr).
      assert (contra := functor_arrow f (@id Empty)).
      assumption.
    Qed.

    Lemma ltxq_locates_left {q r : Q} (l' : locator' x) (ltqr : q < r) : x < ' q -> locates_left l' ltqr.
    Proof.
      intros ltxq. apply nltqx_locates_left.
      apply lt_flip; assumption.
    Qed.

    Lemma nltxr_locates_right {q r : Q} (l' : locator' x) (ltqr : q < r) : ~ x < ' r -> locates_right l' ltqr.
    Proof.
      intros nltxr.
      destruct (dec (locates_right l' ltqr)) as [yes|no].
      - assumption.
      - assert (f := locates_right_false l' ltqr).
        assert (contra := functor_arrow f (@id Empty)).
        assert (nono := contra nltxr).
        destruct (nono no).
    Qed.

    Lemma ltrx_locates_right {q r : Q} (l' : locator' x) (ltqr : q < r) : 'r < x -> locates_right l' ltqr.
    Proof.
      intros ltrx. apply nltxr_locates_right.
      apply lt_flip; assumption.
    Qed.

  End logic2.

  Section bounds.
    (* Given a real with a locator, we can find (integer) bounds. *)
    Context {x : F}
            (l : locator x).

    Axiom ltN1 : forall q : Q, q - 1 < q.
    Let P_lower (q : Q) : Type := locates_right l (ltN1 q).
    Definition P_lower_prop {k} : IsHProp (P_lower k).
    Proof.
      apply _.
    Qed.
    Axiom ltxN1 : x - 1 < x.
    Let P_lower_inhab : hexists (fun q => P_lower q).
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
      assert (qP_lower : {q : Q | P_lower q}) by refine (minimal_n_alt_type Q Q_eq P_lower _ P_lower_inhab).
      destruct qP_lower as [q Pq].
      exists (q - 1).
      unfold P_lower in Pq. simpl in *.
      apply (un_inl _ Pq).
    Defined.

    Axiom lt1N : forall r : Q, r < r + 1.
    (* Assume we have an enumeration of the rationals. *)
    Let P_upper (r : Q) : DHProp := locates_left l (lt1N r).
    Definition P_upper_prop {k} : IsHProp (P_upper k).
    Proof.
      apply _.
    Qed.
    Axiom ltx1N : x < x + 1.
    Let P_upper_inhab : hexists (fun r => P_upper r).
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
      assert (rP_upper : {r : Q | P_upper r}) by refine (minimal_n_alt_type Q Q_eq P_upper _ P_upper_inhab).
      destruct rP_upper as [r Pr].
      exists (r + 1).
      unfold P_upper in Pr. simpl in *.
      destruct (l r (r + 1) (lt1N r)).
      - simpl in Pr. destruct (Pr tt).
      - assumption.
    Defined.

    Instance inc_N_Q : Cast nat Q := naturals_to_semiring nat Q.

    Instance inc_fin_N {n} : Cast (Fin n) nat := fin_to_nat.

    Lemma tight_bound (epsilon : Qpos Q) : {u : Q | ' u < x < ' (u + ' epsilon)}.
    Proof.
      destruct lower_bound as [q ltqx], upper_bound as [r ltxr].
      destruct (round_up_strict Q ((3/'epsilon)*(r-q))) as [n lt3rqn].
      assert (lt0 : 0 < 'epsilon / 3).
      {
        apply pos_mult.
        - apply epsilon.
        - apply pos_dec_recip_compat.
          apply lt_0_3.
      }
      assert (lt0' : 0 < 3 / ' epsilon).
      {
        apply pos_mult.
        - apply lt_0_3.
        - apply pos_dec_recip_compat, epsilon.
      }
      assert (ap30 : (3 : Q) <> 0).
      {
        apply lt_ne_flip. apply lt_0_3.
      }
      assert (ltn3eps : r < q + ' n * ' epsilon / 3).
      {
        rewrite (commutativity q (' n * ' epsilon / 3)).
        apply flip_lt_minus_l.
        apply (pos_mult_reflect_r (3 / ' epsilon) lt0').
        rewrite (commutativity (r-q) (3 / ' epsilon)).
        rewrite <- (associativity ('n) ('epsilon) (/3)).
        rewrite <- (associativity ('n) (' epsilon / 3) (3 / ' epsilon)).
        rewrite <- (associativity ('epsilon) (/3) (3/'epsilon)).
        rewrite (@associativity Q Q Q Q Q Q mult mult mult mult _ (/3) 3 (/'epsilon)).
        rewrite (commutativity (/3) 3).
        rewrite (dec_recip_inverse 3 ap30).
        rewrite mult_1_l.
        assert (apepsilon0 : 'epsilon <> 0).
        {
          apply lt_ne_flip. apply epsilon.
        }
        rewrite (dec_recip_inverse ('epsilon) apepsilon0).
        rewrite mult_1_r.
        assumption.
      }
      set (grid (k : Fin n.+3) := q + (' (' k) - 1)*('epsilon/3) : Q).
      assert (lt_grid : forall k : Fin _, grid (fin_incl k) < grid (fsucc k)).
      {
        intros k. unfold grid.
        change (' fin_incl k) with (fin_to_nat (fin_incl k)); rewrite path_nat_fin_incl.
        change (' fsucc k) with (fin_to_nat (fsucc k)); rewrite path_nat_fsucc.
        assert (eq1 : ' (S (' k)) = (' (' k) + 1)).
        {
          rewrite S_nat_plus_1.
          rewrite (preserves_plus (' k) 1).
          rewrite preserves_1.
          reflexivity.
        }
        rewrite eq1.
        assert (eq2 : ' (' k) + 1 - 1 = ' (' k) - 1 + 1).
        {
          rewrite <- (associativity _ 1 (-1)).
          rewrite (commutativity 1 (-1)).
          rewrite (associativity _ (-1) 1).
          reflexivity.
        }
        rewrite eq2.
        assert (lt1 : ' (' k) - 1 < ' (' k) - 1 + 1).
        {
          apply pos_plus_lt_compat_r.
          apply lt_0_1.
        }
        assert (lt2 : (' (' k) - 1) * (' epsilon / 3) < (' (' k) - 1 + 1) * (' epsilon / 3)).
        {
          nrefine (pos_mult_lt_r ('epsilon/3) _ (' (' k) - 1) (' (' k) - 1 + 1) _); try apply _.
          apply lt1.
        }
        apply pseudo_srorder_plus.
        exact lt2.
      }
      (* set (P k := Build_DHProp (BuildhProp (locates_right l (lt_grid (fin_incl k)) *)
      (*                                       /\ locates_left l (lt_grid (fsucc k)))) _). *)
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
        - apply (@strictly_order_preserving Q F _ _ _ cast_pres_ordering).
          exact ltn3eps.
      }
      destruct (sperners_lemma_1d P left_true right_false) as [u [Pltux Pltxueps]].
      exists (grid (fin_incl (fin_incl u))).
      unfold P in Pltux, Pltxueps.
      split.
      - apply (locates_right_true l (lt_grid (fin_incl u)) Pltux).
      - set (ltxbla := locates_right_false l (lt_grid (fsucc u)) Pltxueps).
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
        apply (@strictly_order_preserving Q F _ _ _ cast_pres_ordering).
        apply pseudo_srorder_plus.
        rewrite (associativity 2 ('epsilon) (/3)).
        rewrite (commutativity 2 ('epsilon)).
        rewrite <- (mult_1_r ('epsilon)).
        rewrite <- (associativity ('epsilon) 1 2).
        rewrite (mult_1_l 2).
        rewrite <- (associativity ('epsilon) 2 (/3)).
        apply pos_mult_lt_l.
        + apply epsilon.
        + nrefine (@pos_mult_reflect_r Q Qap Qplus Qmult Qzero Qone Qlt _ _ (3 : Q) lt_0_3 _ _ _); try apply _.
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

    (* TODO since 0 < eps, we have q - eps < q < q + eps *)
    Axiom ltQnegQ : forall q : Q, forall eps : Qpos Q, q - 'eps < q.
    Axiom ltQposQ : forall q : Q, forall eps : Qpos Q, q < q + 'eps.
    Let P (qeps' : Q * Qpos Q) : Type :=
      match qeps' with
      | (q' , eps') =>
        (prod
           (locates_left l (ltQnegQ q' eps'))
           (locates_right m (ltQposQ q' eps')))
      end.
    Let P_isHProp qeps' : IsHProp (P qeps').
    Proof.
      destruct qeps' as [q eps'].
      apply trunc_prod.
    Qed.
    Let P_dec qeps' : Decidable (P qeps').
    Proof.
      destruct qeps' as [q eps'].
      unfold P.
      apply _.
    Qed.
    Let P_inhab : hexists P.
    Proof.
      assert (hs := (archimedean_property Q F x y ltxy)).
      refine (Trunc_ind _ _ hs); intros [s [ltxs ltsy]].
      assert (ht := (archimedean_property Q F ('s) y ltsy)).
      refine (Trunc_ind _ _ ht); intros [t [ltst' ltty]].
      set (q := (t + s) / 2).
      assert (ltst : s < t).
      {
        Existing Instance full_pseudo_order_reflecting.
        refine (strictly_order_reflecting _ _ _ ltst').
      }
      set (epsilon := (Qpos_diff s t ltst) / 2).
      apply tr.
      exists (q, epsilon).
      unfold P; split.
      - apply ltxq_locates_left.
        (* TODO we took some averages; show some basic algebra. *)
        assert (xeq : q - ' epsilon = s) by admit.
        rewrite xeq; assumption.
      - apply ltrx_locates_right.
        (* TODO we took some averages; show some basic algebra. *)
        assert (yeq : q + ' epsilon = t) by admit.
        rewrite yeq; assumption.
    Admitted.
    (* TODO enumerate pairs of ordered rationals *)
    Axiom QQpos_eq : nat <~> Q * Qpos Q.
    Definition archimedean_structure : {q : Q | x < 'q < y}.
    Proof.
      assert (R : sigT P).
      {
        apply minimal_n_alt_type.
        - apply QQpos_eq.
        - apply P_isHProp.
        - apply P_dec.
        - apply P_inhab.
      }
      unfold P in R.
      destruct R as [[q eps] [lleft mright]].
      exists q; split.
      - refine (locates_right_false l _ lleft).
      - refine (locates_right_true  m _ mright).
    Defined.

  End arch_struct.

  Section unary_ops.

    Context {x : F}
            (l : locator x).

    Definition minus : locator (-x).
    Proof.
      intros q r ltqr.
      assert (ltnrnq := snd (flip_lt_negate q r) ltqr : -r < -q).
      destruct (l _ _ ltnrnq) as [ltnrx|ltxnq].
      - apply inr. apply char_minus_left. rewrite <- preserves_negate. assumption.
      - apply inl. apply char_minus_right. rewrite <- preserves_negate. assumption.
    Defined.

    Context (nu : x ≶ 0).

    (* TODO somehow obtain this instance from the DecRecip Q *)
    Axiom qrecip : Recip Q.
    Existing Instance qrecip.

    Definition recip : locator (recip (x ; nu)).
    Proof.
      destruct (apart_total_lt x 0 nu) as [xneg | xpos].
      - admit. (* TODO prove the case `x < 0` *)
      - (* In case `0 < x`: *)
        intros q r ltqr. destruct (trichotomy _ q 0) as [qneg|[qzero|qpos]].
        + apply inl. refine (transitivity _ _).
          * apply (strictly_order_preserving _). exact qneg.
          * rewrite preserves_0.
            (* TODO if 0 < x then 0 < 1/x *)
            todo (0 < // (x ; nu)).
        + apply inl. rewrite qzero, preserves_0.
          (* TODO if 0 < x then 0 < 1/x *)
          todo (0 < // (x ; nu)).
        + assert (qap0 : q ≶ 0) by apply (pseudo_order_lt_apart_flip _ _ qpos).
          assert (rap0 : r ≶ 0).
          {
            refine (pseudo_order_lt_apart_flip _ _ _).
            apply (transitivity qpos ltqr).
          }
          (* TODO if 0 < q < r then 1/r < 1/q *)
          assert (ltrrrq : // (r ; rap0) < // (q ; qap0)) by admit.
          destruct (l (// (r ; rap0)) (// (q ; qap0)) ltrrrq) as [ltrrx|ltxrq].
          * apply inr.
            (* TODO if 1/r < x then 1/x < r *)
            todo (// (x ; nu) < ' r).
          * apply inl.
            (* TODO if x < 1/q then q < 1/x *)
            todo (' q < // (x ; nu)).
    Admitted.

  End unary_ops.

  Section binary_ops.

    Context {x y : F}
            (l : locator x)
            (m : locator y).

    Definition plus : locator (x + y).
    Proof.
      intros q r ltqr.
      set (epsilon := (Qpos_diff q r ltqr) / 2).
      (* TODO we took the average so we get a midpoint *)
      assert (q+'epsilon=r-'epsilon) by admit.
      destruct (tight_bound m epsilon) as [u [ltuy ltyuepsilon]].
      (* TODO simple algebra: s=q-u so q-s=u *)
      set (s := q-u). assert (qsltx : 'q-'s<y) by admit.
      (* TODO 0<epsilon so s<s+epsilon *)
      assert (sltseps : s<s+' epsilon) by admit.
      destruct (l s (s+' epsilon) sltseps) as [ltsx|ltxseps].
      - apply inl. apply char_plus_left. apply tr; exists s; split; try assumption.
        rewrite preserves_minus; assumption.
      - apply inr. apply char_plus_right. apply tr.
        set (t := s + ' epsilon); exists t.
        split; try assumption.
        (* TODO show that r-(q-u+(r-q)/2)=u+(r-q)-(r-q)/2=u+epsilon *)
        todo (y < ' (r - t)).
    Admitted.

  End binary_ops.

  Section binary_ops_todo.

    Axiom times : forall x y (l : locator x) (m : locator y),
      locator (x * y).

    Lemma meet {x y} (l : locator x) (m : locator y):
        locator (meet x y).
    Proof.
      intros q r ltqr. destruct (l q r ltqr, m q r ltqr) as [[ltqx|ltxr] [ltqy|ltyr]].
      - apply inl. apply meet_lt_l; assumption.
      - apply inr. apply meet_lt_r_r; assumption.
      - apply inr. apply meet_lt_r_l; assumption.
      - apply inr. apply meet_lt_r_r; assumption.
    Defined.

    Lemma join {x y} (l : locator x) (m : locator y):
        locator (join x y).
    Proof.
      intros q r ltqr. destruct (l q r ltqr, m q r ltqr) as [[ltqx|ltxr] [ltqy|ltyr]].
      - apply inl. apply join_lt_l_l; assumption.
      - apply inl. apply join_lt_l_l; assumption.
      - apply inl. apply join_lt_l_r; assumption.
      - apply inr. apply join_lt_r; assumption.
    Defined.

  End binary_ops_todo.

  Section limit.

    Context {xs : nat -> F}.
    Generalizable Variable M.
    Context {M} {M_ismod : CauchyModulus Q F xs M}.
    Context (ls : forall n, locator (xs n)).

    Lemma limit {l} : IsLimit _ _ xs l -> locator l.
    Proof.
      intros islim.
      intros q r ltqr.
      set (epsilon := (Qpos_diff q r ltqr) / 3).
      (* TODO we are doing trisection so we have the inequality: *)
      assert (ltqepsreps : q + ' epsilon < r - ' epsilon) by admit.
      destruct (ls (M (epsilon / 2)) (q + ' epsilon) (r - ' epsilon) ltqepsreps)
        as [ltqepsxs|ltxsreps].
      + apply inl.
        (* TODO if a + b < c then a < c - b *)
        assert (ltqxseps : ' q < xs (M (epsilon / 2)) - ' (' epsilon)) by admit.
        refine (transitivity ltqxseps _).
        apply (modulus_close_limit _ _ _ _ _).
      + apply inr.
        (* TODO if a < b - c then a + c < b *)
        assert (ltxsepsr : xs (M (epsilon / 2)) + ' (' epsilon) < ' r) by admit.
        refine (transitivity _ ltxsepsr).
        apply (modulus_close_limit _ _ _ _ _).
    Admitted.

  End limit.

End locator.
