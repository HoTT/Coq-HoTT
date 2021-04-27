From HoTT.Classes Require Import
     interfaces.abstract_algebra
     interfaces.rationals
     interfaces.orders
     implementations.peano_naturals
     orders.rings
     orders.fields
     orders.semirings
     theory.rings
     theory.dec_fields
     theory.fields
     theory.rationals.

Section cauchy.
  Context (Q : Type).
  Context `{Rationals Q}.
  Context {Q_dec_paths : DecidablePaths Q}.
  Context {Qtriv : TrivialApart Q}.
  Context (F : Type).
  Context `{Forderedfield : OrderedField F}.
  Let qinc : Cast Q F := rationals_to_field Q F.
  Existing Instance qinc.
  (* TODO The following two instances should probably come from the
  `Rationals` instance. *)
  Context (qinc_strong_presving : IsSemiRingStrongPreserving qinc).
  Existing Instance qinc_strong_presving.

  Section sequence.
    Context (x : nat -> F).

    Class CauchyModulus (M : Qpos Q -> nat) :=
      cauchy_convergence : forall epsilon : Qpos Q, forall m n,
            M epsilon <= m -> M epsilon <= n ->
            - ' (' epsilon) < (x m) - (x n) < ' (' epsilon).

    Class IsLimit (l : F) := is_limit
      : forall epsilon : Qpos Q,
          hexists (fun N : nat => forall n : nat, N <= n ->
            - ' (' epsilon) < l - x n < ' (' epsilon)).
  End sequence.

  Class IsComplete := is_complete
    : forall x : nat -> F, forall M , CauchyModulus x M -> exists l, IsLimit x l.

  Section theory.
    Context (x : nat -> F) {M} `{CauchyModulus x M}.

    Lemma modulus_close_limit
          {l}
          (islim : IsLimit x l)
          (epsilon : Qpos Q)
      : x (M (epsilon / 2)) - ' (' epsilon)
        < l
        < x (M (epsilon / 2)) + ' (' epsilon).
    Proof.
      assert (lim_close := is_limit x (epsilon / 2));
        strip_truncations.
      destruct lim_close as [N isclose'].
      set (n := Nat.max (M (epsilon / 2)) N).
      assert (leNn := le_nat_max_r (M (epsilon / 2)) N : N ≤ n).
      assert (isclose := isclose' n leNn).
      clear isclose'.
      assert (leMn := le_nat_max_l (M (epsilon / 2)) N : M (epsilon / 2) ≤ n).
      assert (leMM : M (epsilon / 2) ≤ M (epsilon / 2) ) by apply (Nat.leq_n).
      assert (x_close := cauchy_convergence x (epsilon/2) n (M (epsilon / 2)) leMn leMM).
      cbn in isclose, x_close.
      rewrite (@preserves_mult Q F _ _ _ _ _ _ _ _ _ _ _ _) in isclose, x_close.
      assert (eq22 : ' 2 = 2).
      {
        rewrite (@preserves_plus Q F _ _ _ _ _ _ _ _ _ _ _ _).
        rewrite (@preserves_1 Q F _ _ _ _ _ _ _ _ _ _).
        reflexivity.
      }
      set (ap20 := positive_apart_zero 2 lt_0_2 : 2 ≶ 0).
      assert (ap20' : ' 2 ≶ 0).
      {
        rewrite eq22; exact ap20.
      }
      rewrite (dec_recip_to_recip 2 ap20') in isclose, x_close.
      assert (eq_recip_22 : recip' (' 2) ap20' = recip' 2 ap20).
      {
        apply recip_proper_alt.
        exact eq22.
      }
      unfold recip' in eq_recip_22.
      rewrite eq_recip_22 in isclose, x_close.
      clear eq22 ap20' eq_recip_22.
      rewrite <- (field_split2 (' (' epsilon))).
      set (eps_recip_2 := (' (' epsilon) * recip' 2 ap20)).
      fold ap20.
      change (' (' epsilon) * recip' 2 ap20) with eps_recip_2.
      unfold recip' in eps_recip_2.
      set (xMeps2 := x (M (epsilon / 2))).
      fold xMeps2 in x_close.
      rewrite negate_plus_distr.
      split.
      - apply (strictly_order_reflecting (+ (- x n))).
        refine (transitivity _ (fst isclose)).
        clear isclose.
        fold eps_recip_2.
        fold eps_recip_2 in x_close.
        apply fst, flip_lt_minus_r in x_close.
        rewrite plus_comm in x_close.
        apply flip_lt_minus_l in x_close.
        rewrite plus_comm in x_close.
        apply flip_lt_minus_l in x_close.
        rewrite <-(plus_assoc xMeps2 _ (- x n)).
        rewrite (plus_comm _ (- x n)).
        rewrite (plus_assoc xMeps2 (- x n) _).
        apply (strictly_order_reflecting (+ eps_recip_2)).
        apply (strictly_order_reflecting (+ eps_recip_2)).
        rewrite plus_negate_l, plus_0_l.
        rewrite <- (plus_assoc (xMeps2 - x n) _ _).
        rewrite <- (plus_assoc (-eps_recip_2) _ _).
        rewrite plus_negate_l, plus_0_r.
        rewrite <- (plus_assoc (xMeps2 - x n) _ _).
        rewrite plus_negate_l, plus_0_r.
        assumption.
      - apply (strictly_order_reflecting (+ (- x n))).
        refine (transitivity (snd isclose) _).
        clear isclose.
        fold eps_recip_2.
        fold eps_recip_2 in x_close.
        apply snd in x_close.
        apply flip_lt_minus_l in x_close.
        rewrite plus_comm in x_close.
        apply (strictly_order_reflecting (+ x n)).
        rewrite <- (plus_assoc _ (-x n) (x n)).
        rewrite plus_negate_l, plus_0_r.
        rewrite (plus_comm eps_recip_2 (x n)).
        rewrite (plus_assoc xMeps2 _ _).
        apply (strictly_order_preserving (+ eps_recip_2)).
        assumption.
    Qed.

  End theory.

End cauchy.
