(** * The inclusion of the rationals into an ordered field *)

From HoTT Require Import Basics Types.Sigma Truncations.Core HSet.
From HoTT.Spaces.Nat Require Import Core.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.rationals
  interfaces.naturals
  implementations.peano_naturals
  theory.apartness
  theory.rings
  theory.fields
  theory.dec_fields
  orders.semirings
  orders.rings
  orders.naturals.

Generalizable Variables F Q R Rle Rlt.

(** For rationals [Q] and an ordered field [F], the map [rationals_to_field Q F] is the unique semiring morphism [Q -> F].  We show that it preserves the strict order and is injective, and that it reflects the strict order when [1] is apart from [0] in [Q] (for instance when the apartness of [Q] is trivial).  The key step is that every rational [q] satisfies [q * d + b = a] with [a], [b] and [d] images of natural numbers and [d] positive.  We obtain this by initiality of [Q]: the elements of [F] of this form make up a subfield of [F]. *)

(** Compare two natural numbers by the difference between them. *)
Local Definition nat_add_cases (a b : nat)
  : {c : nat & (c + b)%nat = a} + {c : nat & (S c + a)%nat = b}.
Proof.
  destruct (leq_dichotomy b a) as [l|l].
  - left; exact (equiv_leq_add b a l).
  - right; destruct (equiv_leq_add (S a) b l) as [c p].
    exact (c; (nat_add_succ_r c a)^ @ p).
Defined.

(** In an ordered ring, if [y * (m + 1) + b = a] for natural numbers [a], [b] and [m], then [y] is positive exactly when [a = c + 1 + b] for a natural number [c]. *)
Section nat_quotient_sign.
  Context `{IsCRing R} `{Apart R} `{!FullPseudoSemiRingOrder (A:=R) Rle Rlt}
    `{!PropHolds ((1 : R) ≶ 0)}.

  Local Notation nR := (naturals_to_semiring nat R).

  Context (y : R) (a b m : nat) (E : y * nR (S m) + nR b = nR a).

  Local Lemma nat_quotient_pos_succ (ypos : 0 < y) : {c : nat & (S c + b)%nat = a}.
  Proof.
    destruct (nat_add_cases a b) as [[c p]|[c p]]; destruct p.
    - assert (E' : y * nR (S m) = nR c).
      { apply (right_cancellation (+) (nR b)).
        rewrite E, (preserves_plus (f:=nR)); reflexivity. }
      destruct c as [|c]; [|exact (c; idpath)].
      destruct (irreflexivity (<) (0 : R)).
      exact (transport (fun z => 0 < z) E'
               (pos_mult_compat _ _ ypos (nat_to_semiring_succ_pos m))).
    - destruct (irreflexivity (<) (0 : R)).
      refine (transport (fun z => 0 < z) _
                (pos_plus_compat _ _
                   (pos_mult_compat _ _ ypos (nat_to_semiring_succ_pos m))
                   (nat_to_semiring_succ_pos c))).
      apply (right_cancellation (+) (nR a)).
      rewrite plus_0_l, <- plus_assoc, <- (preserves_plus (f:=nR)).
      exact E.
  Qed.

  Local Lemma nat_quotient_succ_pos (c : {c : nat & (S c + b)%nat = a}) : 0 < y.
  Proof.
    destruct c as [c p]; destruct p.
    assert (E' : y * nR (S m) = nR (S c)).
    { apply (right_cancellation (+) (nR b)).
      rewrite E, (preserves_plus (f:=nR)); reflexivity. }
    apply (pos_mult_rev_l _ (nR (S m))).
    - rewrite E'; apply nat_to_semiring_succ_pos.
    - apply nat_to_semiring_succ_pos.
  Qed.
End nat_quotient_sign.

Section nat_quotients.
  Context `{OrderedField F}.

  Local Notation nF := (naturals_to_semiring nat F).

  Let nF_plus (a b : nat) : nF (a + b)%nat = nF a + nF b
    := preserves_plus a b.
  Let nF_mult (a b : nat) : nF (a * b)%nat = nF a * nF b
    := preserves_mult a b.
  Let distr_r (x y z : F) : (x + y) * z = x * z + y * z
    := simple_distribute_r x y z.
  Let distr_l (x y z : F) : x * (y + z) = x * y + x * z
    := simple_distribute_l x y z.

  (** An element [y] of [F] is a quotient of natural numbers, up to sign, if [y * d + b = a] for natural numbers [a], [b] and positive [d]. *)
  Local Definition IsNatQuot (y : F) : Type
    := merely {a : nat & {b : nat & {m : nat & y * nF (S m) + nF b = nF a}}}.

  Local Lemma isnatquot_zero : IsNatQuot 0.
  Proof.
    apply tr; exists 0%nat, 0%nat, 0%nat.
    rewrite mult_0_l; apply plus_0_l.
  Qed.

  Local Lemma isnatquot_one : IsNatQuot 1.
  Proof.
    apply tr; exists 1%nat, 0%nat, 0%nat.
    change (1 * 1 + 0 = 1 :> F).
    rewrite mult_1_l; apply plus_0_r.
  Qed.

  Local Lemma isnatquot_plus (x y : F)
    : IsNatQuot x -> IsNatQuot y -> IsNatQuot (x + y).
  Proof.
    intros qx qy; strip_truncations.
    destruct qx as [a1 [b1 [m1 E1]]], qy as [a2 [b2 [m2 E2]]].
    apply tr; exists (a1 * S m2 + a2 * S m1)%nat,
      (b1 * S m2 + b2 * S m1)%nat, (m2 + m1 * S m2)%nat.
    change (S (m2 + m1 * S m2)) with (S m1 * S m2)%nat.
    rewrite (nF_mult (S m1) (S m2)), !nF_plus, !nF_mult, <- E1, <- E2.
    set (d1 := nF (S m1)); set (d2 := nF (S m2)).
    rewrite 3!distr_r, (mult_assoc x d1 d2),
      (mult_comm d1 d2), (mult_assoc y d2 d1).
    rewrite <- 2!(plus_assoc (x * d1 * d2)); apply ap.
    rewrite 2!(plus_assoc _ _ (nF b2 * d1)), (plus_comm (y * d2 * d1)).
    reflexivity.
  Qed.

  Local Lemma isnatquot_negate (x : F) : IsNatQuot x -> IsNatQuot (- x).
  Proof.
    intros qx; strip_truncations.
    destruct qx as [a [b [m E]]].
    apply tr; exists b, a, m.
    rewrite <- E, <- negate_mult_distr_l, plus_assoc, plus_negate_l.
    apply plus_0_l.
  Qed.

  Local Lemma isnatquot_mult (x y : F)
    : IsNatQuot x -> IsNatQuot y -> IsNatQuot (x * y).
  Proof.
    intros qx qy; strip_truncations.
    destruct qx as [a1 [b1 [m1 E1]]], qy as [a2 [b2 [m2 E2]]].
    apply tr; exists (a1 * a2 + b1 * b2)%nat,
      (a1 * b2 + b1 * a2)%nat, (m2 + m1 * S m2)%nat.
    change (S (m2 + m1 * S m2)) with (S m1 * S m2)%nat.
    rewrite (nF_mult (S m1) (S m2)), !nF_plus, !nF_mult.
    rewrite <- (mult_assoc x), (mult_assoc y), (mult_comm y), <- (mult_assoc _ y),
      (mult_assoc x), <- E1, <- E2.
    set (u1 := x * nF (S m1)); set (u2 := y * nF (S m2)).
    set (c1 := nF b1); set (c2 := nF b2).
    rewrite (distr_r u1 c1 c2), (distr_r u1 c1 (u2 + c2)), (distr_l u1 u2 c2),
      (distr_l c1 u2 c2).
    rewrite <- (plus_assoc (u1 * u2) (u1 * c2)), <- (plus_assoc (u1 * u2)); apply ap.
    rewrite <- (plus_assoc (u1 * c2) (c1 * c2)), <- (plus_assoc (u1 * c2)); apply ap.
    exact (plus_comm _ _).
  Qed.

  Local Lemma isnatquot_recip (x : F) (p : x ≶ 0)
    : IsNatQuot x -> IsNatQuot (// (x; p)).
  Proof.
    intros qx; strip_truncations.
    destruct qx as [a [b [m E]]].
    apply tr.
    pose proof (nat_to_semiring_succ_pos m) as dpos.
    set (d := nF (S m)) in *.
    destruct (nat_add_cases a b) as [[c q]|[c q]]; destruct q.
    - assert (Exd : x * d = nF c).
      { apply (right_cancellation (+) (nF b)).
        rewrite E, nF_plus; reflexivity. }
      destruct c as [|c].
      + destruct (irreflexivity (≶) (0 : F)).
        exact (transport (fun z => z ≶ 0) Exd
                 (mult_apart_zero _ _ p (positive_apart_zero _ dpos))).
      + exists (S m), 0%nat, c.
        change (nF (S m)) with d.
        rewrite plus_0_r, <- Exd, mult_assoc, (mult_comm _ x), reciperse_alt.
        apply mult_1_l.
    - assert (Exd : nF (S c) = - (x * d)).
      { apply (left_cancellation (+) (x * d)).
        rewrite plus_negate_r.
        apply (right_cancellation (+) (nF a)).
        rewrite <- plus_assoc, <- nF_plus, E.
        exact (plus_0_l _)^. }
      exists 0%nat, (S m), c.
      change (nF (S m)) with d.
      rewrite Exd, <- negate_mult_distr_r, mult_assoc, (mult_comm _ x),
        reciperse_alt, mult_1_l.
      apply plus_negate_l.
  Qed.

  (** The subfield of [F] of quotients of natural numbers. *)
  Local Definition NatQuot := {y : F & IsNatQuot y}.

  Local Instance natquot_zero : Zero NatQuot := (0; isnatquot_zero).
  Local Instance natquot_one : One NatQuot := (1; isnatquot_one).
  Local Instance natquot_plus : Plus NatQuot
    := fun x y => (x.1 + y.1; isnatquot_plus _ _ x.2 y.2).
  Local Instance natquot_mult : Mult NatQuot
    := fun x y => (x.1 * y.1; isnatquot_mult _ _ x.2 y.2).
  Local Instance natquot_negate : Negate NatQuot
    := fun x => (- x.1; isnatquot_negate _ x.2).
  Local Instance natquot_apart : Apart NatQuot := fun x y => x.1 ≶ y.1.
  Local Instance natquot_recip : Recip NatQuot
    := fun x => (// (x.1.1; x.2); isnatquot_recip _ x.2 x.1.2).

  Local Instance isinjective_natquot_pr1 : IsInjective (pr1 : NatQuot -> F).
  Proof.
    intros x y p; exact (path_sigma_hprop _ _ p).
  Qed.

  Local Instance isfield_natquot : IsField NatQuot.
  Proof.
    split.
    - by rapply (projected_ring (pr1 : NatQuot -> F)).
    - rapply (projected_strong_setoid (pr1 : NatQuot -> F)).
      + intros x y; split.
        * exact (ap pr1).
        * exact (path_sigma_hprop x y).
      + intros x y; reflexivity.
    - intros x1 y1 x2 y2.
      exact (strong_binary_extensionality (+) x1.1 y1.1 x2.1 y2.1).
    - intros x1 y1 x2 y2.
      exact (strong_binary_extensionality (.*.) x1.1 y1.1 x2.1 y2.1).
    - exact (_ : PropHolds ((1 : F) ≶ 0)).
    - intros x; apply path_sigma_hprop.
      exact (recip_inverse (x.1.1; x.2)).
  Qed.

  Local Lemma natquot_pr1_iter (n : nat)
    : (nat_iter n (1 +) 0 : NatQuot).1 = nat_iter n (1 +) 0.
  Proof.
    induction n as [|n IH].
    - reflexivity.
    - exact (ap (1 +) IH).
  Qed.

  Local Instance natquot_characteristic_0 : FieldCharacteristic NatQuot 0.
  Proof.
    intros n Hn.
    unfold apart, natquot_apart.
    rewrite natquot_pr1_iter.
    exact (ordered_characteristic_0 n Hn).
  Qed.

  Local Instance natquot_pr1_preserving : IsSemiRingPreserving (pr1 : NatQuot -> F).
  Proof.
    repeat split.
  Qed.

  Context `{Rationals Q}.

  Local Existing Instance pseudo_order_apart.

  Local Notation f := (rationals_to_field Q F).
  Local Notation nQ := (naturals_to_semiring nat Q).

  Local Lemma rationals_to_field_nat (n : nat) : f (nQ n) = nF n.
  Proof.
    assert (IsSemiRingPreserving (f o nQ)) by rapply compose_sr_morphism.
    exact (toR_unique (f o nQ) n)^.
  Qed.

  #[export] Instance isinjective_rationals_to_field
    : IsInjective (rationals_to_field Q F).
  Proof.
    intros x y E. apply (fst (tight_apart x y)). intros apxy.
    assert (ne : x - y <> 0).
    { intros e. exact (apart_ne x y apxy (fst (equal_by_zero_sum x y) e)). }
    pose proof (ap f (dec_recip_inverse (x - y) ne)) as E'.
    rewrite preserves_mult, preserves_minus, E, plus_negate_r, mult_0_l,
      (preserves_1 (f:=f)) in E'.
    exact (apart_ne _ _ (_ : PropHolds ((1 : F) ≶ 0)) E'^).
  Qed.

  #[export] Instance isembedding_rationals_to_field
    : IsEmbedding (rationals_to_field Q F)
    := isembedding_isinj_hset _ _.

  Local Lemma isnatquot_rational (q : Q)
    : merely {a : nat & {b : nat & {m : nat &
        (q * nQ (S m) + nQ b = nQ a) /\ (f q * nF (S m) + nF b = nF a)}}}.
  Proof.
    assert (Hq : IsNatQuot (f q)).
    { assert (IsSemiRingPreserving (pr1 o rationals_to_field Q NatQuot))
        by rapply compose_sr_morphism.
      rewrite (rationals_initial (h := pr1 o rationals_to_field Q NatQuot) q).
      exact (rationals_to_field Q NatQuot q).2. }
    strip_truncations; destruct Hq as [a [b [m E]]].
    apply tr; exists a, b, m; refine (_, E).
    apply (injective f).
    rewrite (preserves_plus (f:=f)), (preserves_mult (f:=f)), !rationals_to_field_nat.
    exact E.
  Qed.

  (** Provided [1] is apart from [0] in [Q], a rational [q] is positive if and only if [f q] is. *)
  Local Lemma rationals_to_field_pos_iff `{!PropHolds ((1 : Q) ≶ 0)} (q : Q)
    : 0 < q <-> 0 < f q.
  Proof.
    assert (Hq := isnatquot_rational q).
    split; intros qpos; strip_truncations; destruct Hq as [a [b [m [EQ EF]]]].
    - exact (nat_quotient_succ_pos _ _ _ _ EF (nat_quotient_pos_succ _ _ _ _ EQ qpos)).
    - exact (nat_quotient_succ_pos _ _ _ _ EQ (nat_quotient_pos_succ _ _ _ _ EF qpos)).
  Qed.

  #[export] Instance strictly_order_preserving_rationals_to_field
    : StrictlyOrderPreserving (rationals_to_field Q F).
  Proof.
    intros x y E.
    apply flip_pos_minus in E; apply flip_pos_minus.
    rewrite <- preserves_minus.
    (* A positive rational shows that [1] is apart from [0] in [Q]. *)
    assert (PropHolds ((1 : Q) ≶ 0)).
    { assert (E1 : (y - x) * 1 ≶ (y - x) * 0).
      { rewrite mult_1_r, mult_0_r.
        exact (snd (apart_iff_total_lt _ 0) (inr E)). }
      pose proof (strong_binary_extensionality (.*.) _ 1 _ 0 E1) as h.
      unfold PropHolds; strip_truncations; destruct h as [h|h].
      - destruct (irreflexivity _ _ h).
      - exact h. }
    exact (fst (rationals_to_field_pos_iff _) E).
  Qed.

  #[export] Instance strictly_order_reflecting_rationals_to_field
    `{!PropHolds ((1 : Q) ≶ 0)}
    : StrictlyOrderReflecting (rationals_to_field Q F).
  Proof.
    intros x y E.
    apply flip_pos_minus in E; apply flip_pos_minus.
    rewrite <- preserves_minus in E.
    exact (snd (rationals_to_field_pos_iff _) E).
  Qed.

  #[export] Instance issemiringstrongpreserving_rationals_to_field
    `{!PropHolds ((1 : Q) ≶ 0)}
    : IsSemiRingStrongPreserving (rationals_to_field Q F).
  Proof.
    split; [exact _|].
    intros x y E.
    apply apart_iff_total_lt; apply apart_iff_total_lt in E.
    destruct E; [left | right]; apply (strictly_order_reflecting f); assumption.
  Qed.
End nat_quotients.
