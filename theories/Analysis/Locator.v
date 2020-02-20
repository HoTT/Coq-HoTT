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
        HoTT.Classes.interfaces.cauchy
        HoTT.Classes.interfaces.archimedean
        HoTT.Classes.orders.orders
        HoTT.Classes.orders.archimedean
        HoTT.Classes.orders.rings
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

  Context `{Funext} `{Univalence}.

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

    (* TODO prove an equality in a Record type. *)
    Axiom locator'_locator_locator' : forall (l' : locator' x), locator_locator' (locator'_locator l') = l'.

    Let locsig : _ <~> locator' x := ltac:(issig).
    Lemma locator'_locator_locator'' (l' : locator' x): locator_locator' (locator'_locator l') = l'.
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

    Lemma nltqx_locates_left {q r : Q} (l' : locator' x) (ltqr : q < r) : ~ ' q < x -> locates_left l' ltqr.
    Proof.
      assert (f := locates_right_true l' ltqr).
      assert (contra := functor_arrow f (@id Empty)).
      assumption.
    Defined.

    Lemma nltxr_locates_right {q r : Q} (l' : locator' x) (ltqr : q < r) : ~ x < ' r -> locates_right l' ltqr.
    Proof.
      intros nltxr.
      destruct (dec (locates_right l' ltqr)) as [yes|no].
      - assumption.
      - assert (f := locates_right_false l' ltqr).
        assert (contra := functor_arrow f (@id Empty)).
        assert (nono := contra nltxr).
        destruct (nono no).
    Defined.

  End logic2.

  Section bounds.
    (* Given a real with a locator, we can find (integer) bounds. *)
    Context {x : F}
            (l : locator x).

    Axiom ltN1 : forall q : Q, q - 1 < q.
    (* Assume we have an enumeration of the rationals. *)
    Axiom Q_eq : nat <~> Q.
    Let P (q : Q) : Type := locates_right l (ltN1 q).
    Definition P_prop {k} : IsHProp (P k).
    Proof.
      apply _.
    Qed.
    Axiom ltxN1 : x - 1 < x.
    Let P_inhab : hexists (fun q => P q).
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
      unfold P.
      apply nltxr_locates_right.
      apply lt_flip; assumption.
    Defined.

    Definition lower_bound : {q : Q | ' q < x}.
    Proof.
      assert (qP : {q : Q | P q}) by refine (minimal_n_alt_type Q Q_eq P _ P_inhab).
      destruct qP as [q Pq].
      exists (q - 1).
      unfold P in Pq. simpl in *.
      apply (un_inl _ Pq).
    Defined.

    (* TODO By symmetry, we get: *)
    Axiom upper_bound : forall l : locator x, {r : Q | x < ' r}.


    (* TODO prove using Sperner's Lemma *)
    Axiom tight_bound : forall (l : locator x) (epsilon : Qpos Q), {u : Q | ' u < x < ' (u + ' epsilon)}.

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
      refine (Trunc_ind _ _ ht); intros [t [ltst ltty]].
      set (q := (t + s) / 2).
      set (epsilon := (t - s) / 2).
      (* TODO since s<t, we have 0<epsilon *)
      assert (eps_pos : 0 < epsilon) by admit.
      apply tr.
      exists (q,mkQpos epsilon eps_pos).
      unfold P; split.
      - apply nltqx_locates_left.
        (* TODO we took some averages; show some basic algebra. *)
        assert (xeq : q - epsilon = s) by admit.
        rewrite xeq. apply lt_flip; assumption.
      - apply nltxr_locates_right.
        (* TODO we took some averages; show some basic algebra. *)
        assert (yeq : q + epsilon = t) by admit.
        rewrite yeq. apply lt_flip; assumption.
    Admitted.
    Definition archimedean_structure : {q : Q | x < 'q < y}.
    Proof.
      assert (R : sigT P).
      {
        apply minimal_n_alt_type.
        - (* TODO enumerate the rationals *)
          todo (nat <~> Q * Qpos Q).
        - apply P_isHProp.
        - apply P_dec.
        - apply P_inhab.
      }
      unfold P in R.
      destruct R as [[q eps] [lleft mright]].
      exists q; split.
      - refine (locates_right_false l _ lleft).
      - refine (locates_right_true  m _ mright).
    Admitted.

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
      set (epsilon' := (r-q)/2).
      (* TODO `epsilon'` is positive since q<r *)
      assert (eps_pos : 0 < epsilon') by admit.
      set (epsilon := mkQpos epsilon' eps_pos).
      (* TODO we took the average so we get a midpoint *)
      assert (q+'epsilon=r-'epsilon) by admit.
      destruct (tight_bound m epsilon) as [u [ltuy ltyuepsilon]].
      (* TODO simple algebra: s=q-u so q-s=u *)
      set (s := q-u). assert (qsltx : 'q-'s<y) by admit.
      (* TODO 0<epsilon so s<s+epsilon *)
      assert (sltseps : s<s+epsilon') by admit.
      destruct (l s (s+epsilon') sltseps) as [ltsx|ltxseps].
      - apply inl. apply char_plus_left. apply tr; exists s; split; try assumption.
        rewrite preserves_minus; assumption.
      - apply inr. apply char_plus_right. apply tr.
        set (t := s + epsilon'); exists t.
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
      set (epsilon' := (r-q)/3).
      (* TODO since q<r, epsilon is positive *)
      assert (eps_pos : 0 < epsilon') by admit.
      set (epsilon := mkQpos epsilon'  eps_pos).
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
