(** * Signed-digit representations *)

(** A real number with a locator can be written as an integer plus an infinite sum of signed digits, and conversely a real number with such a representation has a locator. We work in an arbitrary base [1 + d] with digits from [- d] to [d]; decimal signed digits are the case [d = 9]. Integers are taken from an arbitrary model [Z] of the interface [Integers], mapped into the rationals with [integers_to_ring], in the same way as the rationals [Q] are an arbitrary model of [Rationals]. A digit is an element of [Z] between [- d] and [d], and the infinite sum is the limit, in the sense of [IsLimit], of its partial sums in [Q]. *)

From HoTT Require Import Basics Truncations.Core Modalities.ReflectiveSubuniverse.
From HoTT.Spaces Require Import Nat.Core.
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
  implementations.natpair_integers
  theory.rings
  theory.naturals
  theory.integers
  theory.rationals
  orders.orders
  orders.maps
  orders.semirings
  orders.rings
  orders.dec_fields
  orders.nat_int
  orders.naturals
  orders.integers
  orders.rationals.
From HoTT.Analysis Require Import Locator.
From HoTT_Contrib.Analysis Require Import
  MetricSpace CauchyCompleteness BanachFixedPoint CauchyReals.

Import NatPair.Instances.

Generalizable Variables A Ale Alt Z.

(** ** Integer parts *)

(** In an ordered ring with decidable strict order in which every element is below a natural number, every element lies between consecutive integers. *)

Section floor.
  Context `{IsCRing A} `{Apart A} `{!FullPseudoSemiRingOrder (A:=A) Ale Alt}
    `{forall a b : A, Decidable (a < b)} `{!RoundUpStrict A}.

  Local Notation nA := (naturals_to_semiring nat A).

  (** A nonnegative element below a natural number [n] lies between consecutive natural numbers. *)
  Local Definition nat_floor (n : nat) (a : A) (a0 : 0 ≤ a) (ltan : a < nA n)
    : {j : nat & nA j ≤ a < nA j + 1}.
  Proof.
    induction n as [|n IH].
    - rewrite (preserves_0 (f:=nA)) in ltan.
      destruct (irreflexivity (<) a (lt_le_trans _ _ _ ltan a0)).
    - destruct (dec (a < nA n)) as [ltn|nltn].
      + exact (IH ltn).
      + exists n; split.
        * exact (not_lt_le_flip _ _ nltn).
        * rewrite plus_comm, <- nat_to_semiring_succ; exact ltan.
  Defined.

  Context `{Integers Z}.

  Local Notation zA := (integers_to_ring Z A).
  Local Notation nZ := (naturals_to_semiring nat Z).

  Definition integer_floor (a : A) : {k : Z & zA k ≤ a < zA k + 1}.
  Proof.
    destruct (round_up_strict A (- a)) as [m ltm].
    assert (a0 : 0 ≤ a + nA m).
    { rewrite plus_comm, <- (negate_involutive a).
      exact (snd (flip_nonneg_minus _ _) (lt_le _ _ ltm)). }
    destruct (round_up_strict A (a + nA m)) as [n ltn].
    destruct (nat_floor n _ a0 ltn) as [j [lej ltj]].
    exists (nZ j - nZ m).
    rewrite (preserves_minus (f:=zA)), 2!(to_semiring_twice zA nZ nA).
    split.
    - exact (snd (flip_le_minus_l _ _ _) lej).
    - rewrite <- plus_assoc, (plus_comm (- nA m)), plus_assoc.
      exact (snd (flip_lt_minus_r _ _ _) ltj).
  Defined.
End floor.

(** ** Locators and signed digits *)

Section digits.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec_paths : DecidablePaths Q} {Qtriv : TrivialApart Q}.
  Context (F : Type) `{Forderedfield : OrderedField F}.
  Context {Farchimedean : ArchimedeanProperty Q F} {Qroundup : RoundUpStrict Q}.
  Context `{Funext} `{Univalence}.
  Context (Z : Type) {Zap : Apart Z} {Zplus : Plus Z} {Zmult : Mult Z}
    {Zzero : Zero Z} {Zone : One Z} {Zneg : Negate Z} {Zle : Le Z} {Zlt : Lt Z}
    {ZtoRing : IntegersToRing Z} {Zints : Integers Z} {Ztriv : TrivialApart Z}.

  Local Existing Instance qinc.
  Local Instance zinc : Cast Z Q := integers_to_ring Z Q.
  (** Stating these instances here helps typeclass search. *)
  Local Instance strictlyorderpreserving_qinc : StrictlyOrderPreserving (qinc Q F) := _.
  Local Instance orderpreserving_qinc : OrderPreserving (qinc Q F)
    := full_pseudo_order_preserving.
  Local Instance orderembedding_zinc : OrderEmbedding (integers_to_ring Z Q).
  Proof.
    rapply (nat_morphism_order_embedding (N:=nat) (R:=Z)
              (Ale0:=Zle) (Alt0:=Zlt) (Ale1:=Qle) (Alt1:=Qlt)).
    all: try exact _.
  Defined.
  Local Notation nQ := (naturals_to_semiring nat Q).
  Local Notation nZ := (naturals_to_semiring nat Z).

  (** A real with a locator lies within distance [1] of an integer. *)
  Definition integer_bound {x : F} (l : locator Q F x)
    : {k : Z & ' (' k - 1) < x < ' (' k + 1)}.
  Proof.
    destruct (tight_bound Q F l 1) as [u [ltux ltxu]].
    destruct (integer_floor u (Z:=Z)) as [j [leju ltuj]].
    exists (j + 1).
    change (' (j + 1)) with (integers_to_ring Z Q (j + 1)).
    rewrite (preserves_plus (f:=integers_to_ring Z Q)), preserves_1.
    rewrite <- (plus_assoc _ 1 (-1)), plus_negate_r, plus_0_r.
    split.
    - refine (le_lt_trans _ _ _ _ ltux).
      exact (order_preserving _ _ _ leju).
    - lhs' exact ltxu.
      apply (strictly_order_preserving _), (strictly_order_preserving (+ 1)), ltuj.
  Defined.

  (** From now on we work in base [1 + d]. *)
  Context (d : nat).

  Local Lemma close_negate (e u v : Q) : - e < u - v < e -> - e < v - u < e.
  Proof.
    intros [lo hi]; rewrite (negate_swap_r v u); split.
    - exact (snd (flip_lt_negate _ _) hi).
    - apply flip_lt_negate_l; exact lo.
  Qed.

  Local Lemma nZ_to_rationals : ' nZ d = nQ d.
  Proof.
    exact (to_semiring_twice _ _ _ d).
  Qed.

  (** The weight [(1 + d)^(- n)] of the [n]th position. *)
  Definition digit_weight (n : nat) : Q := nat_iter n (mult (/ (1 + nQ d))) 1.

  Local Lemma base_pos : 0 < 1 + nQ d.
  Proof.
    rewrite <- nat_to_semiring_succ; apply nat_to_semiring_succ_pos.
  Qed.

  Lemma digit_weight_pos (n : nat) : 0 < digit_weight n.
  Proof.
    induction n as [|n IH].
    - exact lt_0_1.
    - apply pos_mult; [apply pos_dec_recip_compat, base_pos|exact IH].
  Qed.

  Lemma digit_weight_succ (n : nat)
    : digit_weight n = digit_weight (S n) + nQ d * digit_weight (S n).
  Proof.
    transitivity ((1 + nQ d) * digit_weight (S n)).
    - change (digit_weight (S n)) with (/ (1 + nQ d) * digit_weight n).
      rewrite mult_assoc, dec_recip_inverse, mult_1_l; [reflexivity|].
      apply lt_ne_flip, base_pos.
    - rewrite plus_mult_distr_r, mult_1_l; reflexivity.
  Qed.

  (** The partial sums [k + sum_(i < n) a i (1 + d)^(- i - 1)]. *)
  Fixpoint digit_sum (k : Z) (a : nat -> Z) (n : nat) : Q
    := match n with
       | O => ' k
       | S n => digit_sum k a n + ' a n * digit_weight (S n)
       end.

  (** A signed-digit representation of [x] in base [1 + d]: an integer [k] and digits [a n] between [- d] and [d], such that [x] is the limit of the partial sums of [k + sum_n a n (1 + d)^(- n - 1)]. *)
  Record SignedDigits (x : F) := {
    sd_integer : Z;
    sd_digit : nat -> Z;
    sd_digit_bound : forall n, - nZ d ≤ sd_digit n ≤ nZ d;
    sd_islimit : IsLimit Q F (fun n => ' digit_sum sd_integer sd_digit n) x
  }.

  (** For the partial sums to converge, the base must be at least [2]. *)
  Context (dpos : (0 < d)%nat).

  Local Lemma recip_base_pos : 0 < / (1 + nQ d).
  Proof.
    apply pos_dec_recip_compat, base_pos.
  Qed.

  Local Lemma recip_base_lt_1 : / (1 + nQ d) < 1.
  Proof.
    pose proof base_pos.
    apply (strictly_order_reflecting ((1 + nQ d) *.)).
    rewrite dec_recip_inverse, mult_1_r; [|apply lt_ne_flip, base_pos].
    apply pos_plus_lt_compat_r.
    exact (nat_to_semiring_pos d dpos).
  Qed.

  (** The weights become arbitrarily small, which gives a modulus of Cauchy convergence for the partial sums. *)
  Definition digit_modulus (e : Qpos Q) : nat
    := (rational_log (/ (1 + nQ d)) recip_base_pos recip_base_lt_1 e).1.

  Lemma digit_weight_modulus (e : Qpos Q) (n : nat)
    : (digit_modulus e <= n)%nat -> digit_weight n < ' e.
  Proof.
    intro le.
    refine (le_lt_trans _ _ _ _ (rational_log _ recip_base_pos recip_base_lt_1 e).2).
    exact (power_antitone _ _ _ (lt_le _ _ recip_base_pos) (lt_le _ _ recip_base_lt_1) le).
  Qed.

  Section bounds.
    Context (k : Z) (a : nat -> Z) (abound : forall n, - nZ d ≤ a n ≤ nZ d).

    Local Notation s := (digit_sum k a).
    Local Notation w := digit_weight.

    Local Lemma abound_Q (n : nat) : - nQ d ≤ ' a n ≤ nQ d.
    Proof.
      rewrite <- nZ_to_rationals, <- (preserves_negate (f:=integers_to_ring Z Q)).
      split; apply (order_preserving _), abound.
    Qed.

    Local Lemma lower_step (n : nat) : s n - w n ≤ s (S n) - w (S n).
    Proof.
      change (s (S n)) with (s n + ' a n * w (S n)).
      rewrite (digit_weight_succ n), <- plus_assoc.
      apply (order_preserving (s n +)).
      rewrite negate_plus_distr, plus_comm.
      apply (order_preserving (+ (- w (S n)))).
      rewrite negate_mult_distr_l.
      pose proof (lt_le _ _ (digit_weight_pos (S n))).
      apply (order_preserving (.* w (S n))), abound_Q.
    Qed.

    Local Lemma upper_step (n : nat) : s (S n) + w (S n) ≤ s n + w n.
    Proof.
      change (s (S n)) with (s n + ' a n * w (S n)).
      rewrite (digit_weight_succ n), <- plus_assoc.
      apply (order_preserving (s n +)).
      rewrite (plus_comm (w (S n))).
      apply (order_preserving (+ w (S n))).
      pose proof (lt_le _ _ (digit_weight_pos (S n))).
      apply (order_preserving (.* w (S n))), abound_Q.
    Qed.

    (** The intervals with centre [s n] and radius [w n] are nested. *)
    Lemma digit_sum_lower (n m : nat) : (n <= m)%nat -> s n - w n ≤ s m - w m.
    Proof.
      intro le; induction le as [|m le IH].
      - reflexivity.
      - exact (transitivity IH (lower_step m)).
    Qed.

    Lemma digit_sum_upper (n m : nat) : (n <= m)%nat -> s m + w m ≤ s n + w n.
    Proof.
      intro le; induction le as [|m le IH].
      - reflexivity.
      - exact (transitivity (upper_step m) IH).
    Qed.

    (** Hence the partial sums from [n] on stay within [w n] of [s n]. *)
    Lemma digit_sum_close (n m : nat) : (n <= m)%nat -> - w n < s m - s n < w n.
    Proof.
      intro le; split.
      - apply flip_lt_minus_r; rewrite plus_comm.
        refine (le_lt_trans _ _ _ (digit_sum_lower n m le) _).
        apply flip_lt_minus_l, pos_plus_lt_compat_r, digit_weight_pos.
      - apply flip_lt_minus_l; rewrite plus_comm.
        refine (lt_le_trans _ _ _ _ (digit_sum_upper n m le)).
        apply pos_plus_lt_compat_r, digit_weight_pos.
    Qed.

    Lemma digit_sum_rational_modulus : MetricCauchyModulus Q (rational_close Q) s digit_modulus.
    Proof.
      intros e m n lem len.
      destruct (leq_dichotomy n m) as [le|lt].
      - exact (between_weaken _ _ _ (digit_sum_close n m le) (digit_weight_modulus e n len)).
      - apply close_negate.
        exact (between_weaken _ _ _ (digit_sum_close m n (leq_lt lt)) (digit_weight_modulus e m lem)).
    Qed.

    #[export] Instance digit_sum_modulus : CauchyModulus Q F (fun n => ' s n) digit_modulus
      := fun e m n lem len
           => field_close_rationals Q e _ _ (digit_sum_rational_modulus e m n lem len).
  End bounds.

  (** A real with a signed-digit representation has a locator. *)
  Definition locator_signed_digits {x : F} (sd : SignedDigits x) : locator Q F x
    := locator_limit Q F (M_ismod:=digit_sum_modulus _ _ (sd_digit_bound _ sd))
         (fun n => locator_left Q F _) (sd_islimit _ sd).

  Section scan.
    Context {x : F} (l : locator Q F x) (G : Z -> Q) (Ginc : forall j, G j < G (j + 1)).

    (** Using a locator for [x] on consecutive points of an increasing grid [G], we find a point [b] with [G (b - 1) < x < G (b + 1)]. *)
    Definition locator_scan (N : nat) (a : Z)
      (lta : ' G (a - 1) < x) (ltx : x < ' G (a + nZ N + 1))
      : {b : Z & prod (a ≤ b ≤ a + nZ N) (' G (b - 1) < x < ' G (b + 1))}.
    Proof.
      revert a lta ltx; induction N as [|N IH]; intros a lta ltx.
      - assert (p : a + nZ 0%nat = a) by exact (ap (a +) (preserves_0 (f:=nZ)) @ plus_0_r a).
        rewrite p in ltx.
        exists a; split; [split; [reflexivity|rewrite p; reflexivity]|exact (lta, ltx)].
      - assert (pS : a + nZ (S N) = a + 1 + nZ N).
        { rewrite <- plus_assoc; apply ap.
          exact (preserves_plus (f:=nZ) 1%nat N @ ap (+ nZ N) preserves_1). }
        destruct (l (G a) (G (a + 1)) (Ginc a)) as [ltGa|ltxG].
        + destruct (IH (a + 1)) as [b [[le1 le2] bounds]].
          * rewrite <- plus_assoc, plus_negate_r, plus_0_r; exact ltGa.
          * rewrite <- pS; exact ltx.
          * exists b; refine (_, bounds); split.
            -- rhs_V' exact le1.
               apply nonneg_plus_le_compat_r, le_0_1.
            -- rewrite pS; exact le2.
        + exists a; refine (_, (lta, ltxG)); split; [reflexivity|].
          apply nonneg_plus_le_compat_r, nat_to_semiring_nonneg.
    Defined.
  End scan.

  Local Notation w := digit_weight.

  (** The grid [c + j w (S n)] for integers [j], on which we choose the next digit. *)
  Section grid.
    Context (n : nat) (c : Q).

    Local Definition digit_grid (j : Z) : Q := c + ' j * w (S n).

    Local Lemma digit_grid_succ (j : Z) : digit_grid (j + 1) = digit_grid j + w (S n).
    Proof.
      unfold digit_grid.
      rewrite (preserves_plus (f:=cast Z Q)), preserves_1.
      rewrite plus_mult_distr_r, mult_1_l, plus_assoc; reflexivity.
    Qed.

    Local Lemma digit_grid_pred (j : Z) : digit_grid (j - 1) = digit_grid j - w (S n).
    Proof.
      unfold digit_grid.
      rewrite (preserves_minus (f:=cast Z Q)), preserves_1.
      rewrite plus_mult_distr_r, <- negate_mult_distr_l, mult_1_l, plus_assoc; reflexivity.
    Qed.

    (** This is used as an argument of a locator, so we keep it transparent. *)
    Local Definition digit_grid_lt (j : Z) : digit_grid j < digit_grid (j + 1).
    Proof.
      rewrite digit_grid_succ; apply pos_plus_lt_compat_r, digit_weight_pos.
    Defined.

    Local Lemma nZ_double : - nZ d + nZ (d + d) = nZ d.
    Proof.
      rewrite (preserves_plus (f:=nZ)), plus_assoc, plus_negate_l, plus_0_l; reflexivity.
    Qed.

    (** The grid points [- d - 1] and [d + 1] are [c - w n] and [c + w n]. *)
    Local Lemma digit_grid_lower : digit_grid (- nZ d - 1) = c - w n.
    Proof.
      rewrite digit_grid_pred; unfold digit_grid.
      rewrite (preserves_negate (f:=cast Z Q)), nZ_to_rationals, (digit_weight_succ n).
      rewrite <- negate_mult_distr_l, <- plus_assoc, <- negate_plus_distr.
      rewrite (plus_comm (nQ d * w (S n))); reflexivity.
    Qed.

    Local Lemma digit_grid_upper : digit_grid (- nZ d + nZ (d + d) + 1) = c + w n.
    Proof.
      rewrite nZ_double, digit_grid_succ; unfold digit_grid.
      rewrite nZ_to_rationals, (digit_weight_succ n), (plus_comm (w (S n))), plus_assoc.
      reflexivity.
    Qed.
  End grid.

  Section from_locator.
    Context {x : F} (l : locator Q F x).

    (** If [x] lies within [w n] of [c], then we can find a digit [b] such that [x] lies within [w (S n)] of [c + b w (S n)]. *)
    Definition digit_step (n : nat) (c : Q) (h : ' (c - w n) < x < ' (c + w n))
      : {b : Z & prod (- nZ d ≤ b ≤ nZ d)
                   (' (c + ' b * w (S n) - w (S n)) < x < ' (c + ' b * w (S n) + w (S n)))}.
    Proof.
      destruct h as [ltcx ltxc].
      rewrite <- digit_grid_lower in ltcx; rewrite <- digit_grid_upper in ltxc.
      destruct (locator_scan l (digit_grid n c) (digit_grid_lt n c) (d + d) (- nZ d) ltcx ltxc)
        as [b [[lb ub] [ltb ltb']]].
      exists b; split; [split|split].
      - exact lb.
      - rewrite <- nZ_double; exact ub.
      - rewrite digit_grid_pred in ltb; exact ltb.
      - rewrite digit_grid_succ in ltb'; exact ltb'.
    Defined.

    (** Successive rational approximations of [x], the [n]th within [w n] of [x]. *)
    Fixpoint digit_approx (n : nat) : {c : Q & ' (c - w n) < x < ' (c + w n)}
      := match n with
         | O => exist (fun c : Q => ' (c - w 0) < x < ' (c + w 0))
                  (' (integer_bound l).1) (integer_bound l).2
         | S n => let c := digit_approx n in
                  let b := digit_step n c.1 c.2 in
                  (c.1 + ' b.1 * w (S n); snd b.2)
         end.

    (** The digits of [x] produced by the locator; the integer part is the one given by [integer_bound]. *)
    Definition locator_digit (n : nat) : Z
      := (digit_step n (digit_approx n).1 (digit_approx n).2).1.

    Local Lemma digit_sum_approx (n : nat)
      : digit_sum (integer_bound l).1 locator_digit n = (digit_approx n).1.
    Proof.
      induction n as [|n IH].
      - reflexivity.
      - change (digit_sum (integer_bound l).1 locator_digit n + ' locator_digit n * w (S n)
                = (digit_approx n).1 + ' locator_digit n * w (S n)).
        rewrite IH; reflexivity.
    Qed.

    (** A real with a locator has a signed-digit representation. *)
    Definition signed_digits_locator : SignedDigits x.
    Proof.
      snrefine {| sd_integer := (integer_bound l).1; sd_digit := locator_digit |}.
      - intro n; exact (fst (digit_step n (digit_approx n).1 (digit_approx n).2).2).
      - intro e; apply tr; exists (digit_modulus e); intros n len.
        rewrite digit_sum_approx.
        destruct (digit_approx n) as [c [ltcx ltxc]]; cbn [pr1].
        assert (ltwe : ' w n < (' (' e) : F))
          by exact (strictly_order_preserving _ _ _ (digit_weight_modulus e n len)).
        rewrite (preserves_minus (f:=cast Q F)) in ltcx.
        rewrite (preserves_plus (f:=cast Q F)) in ltxc.
        split.
        + apply flip_lt_minus_r; rewrite plus_comm.
          rhs_V' exact ltcx.
          apply (strictly_order_preserving (' c +)), (snd (flip_lt_negate _ _) ltwe).
        + apply flip_lt_minus_l; rewrite plus_comm.
          lhs' exact ltxc.
          apply (strictly_order_preserving (' c +)), ltwe.
    Defined.
  End from_locator.

  (** ** Cauchy reals *)

  (** A signed-digit representation of [x] gives a rational sequence with a modulus converging to [x]. *)
  Definition cauchy_sequence_signed_digits {x : F} (sd : SignedDigits x)
    : {s : CauchySequence Q & IsLimit Q F (fun n => ' s n) x}
    := ({| cauchy_seq := digit_sum (sd_integer _ sd) (sd_digit _ sd);
           cauchy_modulus := digit_modulus;
           cauchy_ismodulus := digit_sum_rational_modulus _ _ (sd_digit_bound _ sd) |};
        sd_islimit _ sd).

  (** Merely having a locator, merely having a signed-digit representation and merely being the limit of a rational sequence with a modulus are equivalent; by [iscauchyreal_iff_limit], so is being a Cauchy real. *)
  Lemma merely_locator_iff_signed_digits (x : F)
    : merely (locator Q F x) <-> merely (SignedDigits x).
  Proof.
    split; apply Trunc_functor.
    - exact signed_digits_locator.
    - exact locator_signed_digits.
  Qed.

End digits.

Section limits.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec_paths : DecidablePaths Q} {Qtriv : TrivialApart Q}.
  Context (F : Type) `{Forderedfield : OrderedField F}.
  Context {Farchimedean : ArchimedeanProperty Q F} {Qroundup : RoundUpStrict Q}.
  Context `{Funext} `{Univalence}.

  Local Existing Instance qinc.

  (** The limit of a rational sequence with a modulus has a locator. *)
  Definition locator_cauchy_sequence {x : F} (s : CauchySequence Q)
    (islim : IsLimit Q F (fun n => ' s n) x)
    : locator Q F x
    := locator_limit Q F (M_ismod:=cauchymodulus_cauchy_sequence Q F s)
         (fun n => locator_left Q F _) islim.

  Lemma merely_locator_iff_limit (x : F)
    : merely (locator Q F x)
      <-> hexists (fun s : CauchySequence Q => IsLimit Q F (fun n => ' s n) x).
  Proof.
    split; apply Trunc_functor.
    - intro l.
      (* Go through signed digits in base [2], with the integers implemented as pairs of naturals. *)
      exact (cauchy_sequence_signed_digits Q F (NatPair.Z nat) 1 _
               (signed_digits_locator Q F (NatPair.Z nat) 1 _ l)).
    - intros [s islim]; exact (locator_cauchy_sequence s islim).
  Qed.

  (** A locator can be truncated as a whole, pointwise, or in its values. Merely having a locator implies the pointwise truncation. *)
  Lemma merely_locator_pointwise (x : F) (l : merely (locator Q F x)) (q r : Q)
    : merely (q < r -> (' q < x) + (x < ' r)).
  Proof.
    exact (Trunc_functor _ (fun l' => l' q r) l).
  Qed.

  (** Since the order on [Q] is decidable, the pointwise truncation is equivalent to the truncation of the values, which holds for every [x] by cotransitivity. *)
  Lemma pointwise_locator_iff_located (x : F)
    : (forall q r : Q, merely (q < r -> (' q < x) + (x < ' r)))
      <-> (forall q r : Q, q < r -> hor (' q < x) (x < ' r)).
  Proof.
    split.
    - intros h q r ltqr; exact (Trunc_functor _ (fun f => f ltqr) (h q r)).
    - intros h q r; exact (O_decidable_arrow (Tr (-1)) _ _ (h q r)).
  Qed.
End limits.
