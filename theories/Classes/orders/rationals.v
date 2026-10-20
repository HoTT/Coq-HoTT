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

(** ** Signs of quotients of natural numbers *)

(** Compare two natural numbers by the difference between them. *)
Local Definition nat_add_cases (a b : nat)
  : {c : nat & (c + b)%nat = a} + {c : nat & (S c + a)%nat = b}.
Proof.
  destruct (leq_dichotomy b a) as [l|l].
  - left; exact (equiv_leq_add b a l).
  - right; destruct (equiv_leq_add (S a) b l) as [c p].
    exact (c; (nat_add_succ_r c a)^ @ p).
Defined.

(** In an ordered ring, let [y * (m + 1) + b = a] for natural numbers [a], [b] and [m]. Comparing [a] and [b] determines [y * (m + 1)] as a natural number up to sign, and [y] is positive exactly when [a = c + 1 + b] for a natural number [c]. *)
Section nat_quotient_sign.
  Context `{IsCRing R} `{Apart R} `{!FullPseudoSemiRingOrder (A:=R) Rle Rlt}.

  Local Notation iR := (naturals_to_semiring nat R).

  Context (y : R) (a b m : nat) (E : y * iR (S m) + iR b = iR a).

  Local Lemma nat_quotient_eq_l (c : nat) (p : (c + b)%nat = a) : y * iR (S m) = iR c.
  Proof.
    apply (right_cancellation (+) (iR b)).
    rewrite E, <- p, (preserves_plus (f:=iR)); reflexivity.
  Qed.

  Local Lemma nat_quotient_eq_r (c : nat) (p : (S c + a)%nat = b)
    : y * iR (S m) = - iR (S c).
  Proof.
    destruct p; apply (right_cancellation (+) (iR (S c) + iR a)).
    rewrite (plus_assoc (- _)), plus_negate_l, plus_0_l.
    rewrite <- (preserves_plus (f:=iR)); exact E.
  Qed.

  Context `{!PropHolds ((1 : R) ≶ 0)}.

  Local Lemma nat_quotient_pos_succ (ypos : 0 < y) : {c : nat & (S c + b)%nat = a}.
  Proof.
    assert (dpos : 0 < y * iR (S m))
      by (apply pos_mult_compat; [exact ypos|apply nat_to_semiring_succ_pos]).
    destruct (nat_add_cases a b) as [[c p]|[c p]].
    - destruct c as [|c]; [|exact (c; p)].
      rewrite (nat_quotient_eq_l 0 p) in dpos.
      destruct (irreflexivity (<) _ dpos).
    - rewrite (nat_quotient_eq_r c p) in dpos.
      destruct (irreflexivity (<) 0).
      lhs' exact dpos; apply flip_pos_negate, nat_to_semiring_succ_pos.
  Qed.

  Local Lemma nat_quotient_succ_pos (c : {c : nat & (S c + b)%nat = a}) : 0 < y.
  Proof.
    destruct c as [c p].
    apply (pos_mult_rev_l y (iR (S m))).
    - rewrite (nat_quotient_eq_l (S c) p); apply nat_to_semiring_succ_pos.
    - apply nat_to_semiring_succ_pos.
  Qed.
End nat_quotient_sign.

(** ** The map from the rationals into an ordered field *)

Section nat_quotients.
  Context `{OrderedField F}.

  Local Notation iF := (naturals_to_semiring nat F).

  Let iF_plus (a b : nat) : iF (a + b)%nat = iF a + iF b
    := preserves_plus a b.
  Let iF_mult (a b : nat) : iF (a * b)%nat = iF a * iF b
    := preserves_mult a b.
  Let iF_mult_succ (m1 m2 : nat) : iF (S (m2 + m1 * S m2)) = iF (S m1) * iF (S m2)
    := preserves_mult (S m1) (S m2).

  (** *** The subfield of quotients of natural numbers *)

  (** An element [y] of [F] is a quotient of natural numbers, up to sign, if [y * d + b = a] for natural numbers [a], [b] and positive [d]. *)
  Local Definition IsNatQuot (y : F) : Type
    := merely {a : nat & {b : nat & {m : nat & y * iF (S m) + iF b = iF a}}}.

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

  Local Lemma plus_quotient_identity (x y d1 d2 c1 c2 : F)
    : (x + y) * (d1 * d2) + (c1 * d2 + c2 * d1) = (x * d1 + c1) * d2 + (y * d2 + c2) * d1.
  Proof.
    rewrite (plus_mult_distr_r x y), plus_swap_middle.
    rewrite (plus_mult_distr_r (x * d1)), (plus_mult_distr_r (y * d2)).
    rewrite (mult_assoc x d1 d2), (mult_comm d1 d2), (mult_assoc y d2 d1).
    reflexivity.
  Qed.

  (** If [x d1 + b1 = a1] and [y d2 + b2 = a2], then [(x + y) d1 d2 + (b1 d2 + b2 d1) = a1 d2 + a2 d1]. *)
  Local Lemma isnatquot_plus (x y : F)
    : IsNatQuot x -> IsNatQuot y -> IsNatQuot (x + y).
  Proof.
    intros qx qy; strip_truncations.
    destruct qx as [a1 [b1 [m1 E1]]], qy as [a2 [b2 [m2 E2]]].
    apply tr; exists (a1 * S m2 + a2 * S m1)%nat,
      (b1 * S m2 + b2 * S m1)%nat, (m2 + m1 * S m2)%nat.
    rewrite iF_mult_succ, !iF_plus, !iF_mult, <- E1, <- E2.
    apply plus_quotient_identity.
  Qed.

  (** If [x d + b = a], then [- x d + a = b]. *)
  Local Lemma isnatquot_negate (x : F) : IsNatQuot x -> IsNatQuot (- x).
  Proof.
    intros qx; strip_truncations.
    destruct qx as [a [b [m E]]].
    apply tr; exists b, a, m.
    rewrite <- E, <- negate_mult_distr_l, plus_assoc, plus_negate_l.
    apply plus_0_l.
  Qed.

  Local Lemma mult_quotient_identity (u1 u2 c1 c2 : F)
    : u1 * u2 + ((u1 + c1) * c2 + c1 * (u2 + c2)) = (u1 + c1) * (u2 + c2) + c1 * c2.
  Proof.
    rewrite (plus_mult_distr_r u1 c1 c2), (plus_mult_distr_l c1 u2 c2).
    rewrite (plus_mult_distr_r u1 c1), (plus_mult_distr_l u1 u2 c2), (plus_mult_distr_l c1 u2 c2).
    (* Both sides are [u1 u2 + u1 c2 + c1 u2 + c1 c2 + c1 c2], up to association and order. *)
    rewrite <- (plus_assoc (u1 * u2 + u1 * c2)), <- (plus_assoc (u1 * u2)).
    apply ap; rewrite <- !plus_assoc; apply ap.
    rewrite plus_comm, <- plus_assoc; apply ap, plus_comm.
  Qed.

  (** If [x d1 + b1 = a1] and [y d2 + b2 = a2], then [x y d1 d2 + (a1 b2 + b1 a2) = a1 a2 + b1 b2]. *)
  Local Lemma isnatquot_mult (x y : F)
    : IsNatQuot x -> IsNatQuot y -> IsNatQuot (x * y).
  Proof.
    intros qx qy; strip_truncations.
    destruct qx as [a1 [b1 [m1 E1]]], qy as [a2 [b2 [m2 E2]]].
    apply tr; exists (a1 * a2 + b1 * b2)%nat,
      (a1 * b2 + b1 * a2)%nat, (m2 + m1 * S m2)%nat.
    rewrite iF_mult_succ, !iF_plus, !iF_mult, <- E1, <- E2.
    rewrite mult_swap_middle.
    apply mult_quotient_identity.
  Qed.

  (** If [x d + b = a] with [x] apart from [0], compare [a] and [b]. If [a = c + b], then [x d = c], so [c] is positive and [(1 / x) c + 0 = d]. If [b = c + 1 + a], then [x d = - (c + 1)], so [(1 / x) (c + 1) + d = 0]. *)
  Local Lemma isnatquot_recip (x : F) (p : x ≶ 0)
    : IsNatQuot x -> IsNatQuot (// (x; p)).
  Proof.
    intros qx; strip_truncations.
    destruct qx as [a [b [m E]]].
    assert (recip_mult : forall c, x * iF (S m) = c -> // (x; p) * c = iF (S m)).
    { intros c Ec; rewrite <- Ec, mult_assoc, (mult_comm (// (x; p)) x), reciperse_alt.
      apply mult_1_l. }
    apply tr.
    destruct (nat_add_cases a b) as [[c q]|[c q]].
    - assert (Exd := nat_quotient_eq_l x a b m E c q).
      destruct c as [|c].
      + destruct (irreflexivity (≶) (0 : F)).
        change (iF 0%nat ≶ 0); rewrite <- Exd.
        apply mult_apart_zero; [exact p|].
        apply positive_apart_zero, nat_to_semiring_succ_pos.
      + exists (S m), 0%nat, c.
        rewrite plus_0_r; exact (recip_mult (iF (S c)) Exd).
    - exists 0%nat, (S m), c.
      rewrite <- (negate_involutive (iF (S c))), <- negate_mult_distr_r,
        (recip_mult (- iF (S c)) (nat_quotient_eq_r x a b m E c q)).
      apply plus_negate_l.
  Qed.

  (** The subfield of [F] of quotients of natural numbers. *)
  Local Definition NatQuot := {y : F & IsNatQuot y}.

  Local Instance natquot_zero : Zero NatQuot := (0; isnatquot_zero).
  Local Instance natquot_one : One NatQuot := (1; isnatquot_one).
  Local Instance natquot_plus : Plus NatQuot
    := fun x y => (x.1 + y.1; isnatquot_plus x.1 y.1 x.2 y.2).
  Local Instance natquot_mult : Mult NatQuot
    := fun x y => (x.1 * y.1; isnatquot_mult x.1 y.1 x.2 y.2).
  Local Instance natquot_negate : Negate NatQuot
    := fun x => (- x.1; isnatquot_negate x.1 x.2).
  Local Instance natquot_apart : Apart NatQuot := fun x y => x.1 ≶ y.1.
  Local Instance natquot_recip : Recip NatQuot
    := fun x => (// (x.1.1; x.2); isnatquot_recip x.1.1 x.2 x.1.2).

  Local Instance isinjective_natquot_pr1 : IsInjective (pr1 : NatQuot -> F).
  Proof.
    intros x y p; apply path_sigma_hprop, p.
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

  (** *** The map from the rationals *)

  Context `{Rationals Q}.

  Local Existing Instance pseudo_order_apart.

  Local Notation i := (rationals_to_field Q F).
  Local Notation iQ := (naturals_to_semiring nat Q).

  Local Lemma rationals_to_field_nat (n : nat) : i (iQ n) = iF n.
  Proof.
    assert (IsSemiRingPreserving (i o iQ)) by rapply compose_sr_morphism.
    exact (toR_unique (i o iQ) n)^.
  Qed.

  (** If [i x = i y] and [x] were apart from [y], then [1 = i ((x - y) / (x - y)) = (i x - i y) i (1 / (x - y)) = 0]. *)
  #[export] Instance isinjective_rationals_to_field
    : IsInjective (rationals_to_field Q F).
  Proof.
    intros x y E. apply (fst (tight_apart x y)). intros apxy.
    assert (ne : x - y <> 0).
    { intros e. exact (apart_ne x y apxy (fst (equal_by_zero_sum x y) e)). }
    pose proof (ap i (dec_recip_inverse (x - y) ne)) as E'.
    rewrite preserves_mult, preserves_minus, E, plus_negate_r, mult_0_l,
      (preserves_1 (f:=i)) in E'.
    apply (apart_ne (1 : F) 0); [exact _|exact E'^].
  Qed.

  #[export] Instance isembedding_rationals_to_field
    : IsEmbedding (rationals_to_field Q F)
    := isembedding_isinj_hset (rationals_to_field Q F) _.

  Local Lemma isnatquot_rational (q : Q)
    : merely {a : nat & {b : nat & {m : nat &
        (q * iQ (S m) + iQ b = iQ a) /\ (i q * iF (S m) + iF b = iF a)}}}.
  Proof.
    assert (Hq : IsNatQuot (i q)).
    { assert (IsSemiRingPreserving (pr1 o rationals_to_field Q NatQuot))
        by rapply compose_sr_morphism.
      rewrite (rationals_initial (h := pr1 o rationals_to_field Q NatQuot) q).
      exact (rationals_to_field Q NatQuot q).2. }
    strip_truncations; destruct Hq as [a [b [m E]]].
    apply tr; exists a, b, m; split; [|exact E].
    apply (injective i).
    rewrite (preserves_plus (f:=i)), (preserves_mult (f:=i)), !rationals_to_field_nat.
    exact E.
  Qed.

  (** Provided [1] is apart from [0] in [Q], a rational [q] is positive if and only if [i q] is. *)
  Lemma rationals_to_field_pos_iff `{!PropHolds ((1 : Q) ≶ 0)} (q : Q)
    : 0 < q <-> 0 < i q.
  Proof.
    assert (Hq := isnatquot_rational q).
    split; intros qpos; strip_truncations; destruct Hq as [a [b [m [EQ EF]]]].
    - exact (nat_quotient_succ_pos (i q) a b m EF (nat_quotient_pos_succ q a b m EQ qpos)).
    - exact (nat_quotient_succ_pos q a b m EQ (nat_quotient_pos_succ (i q) a b m EF qpos)).
  Qed.

  (** A positive rational shows that [1] is apart from [0] in [Q]. *)
  Local Lemma pos_apart_1_0 (q : Q) : 0 < q -> PropHolds ((1 : Q) ≶ 0).
  Proof.
    intros qpos.
    assert (E1 : q * 1 ≶ q * 0).
    { rewrite mult_1_r, mult_0_r.
      exact (snd (apart_iff_total_lt q 0) (inr qpos)). }
    pose proof (strong_binary_extensionality (.*.) q 1 q 0 E1) as h.
    unfold PropHolds; strip_truncations; destruct h as [h|h].
    - destruct (irreflexivity (≶) q h).
    - exact h.
  Qed.

  (** [x < y] iff [0 < y - x], and [i] preserves positivity. *)
  #[export] Instance strictly_order_preserving_rationals_to_field
    : StrictlyOrderPreserving (rationals_to_field Q F).
  Proof.
    intros x y E.
    apply flip_pos_minus in E; apply flip_pos_minus.
    rewrite <- preserves_minus.
    assert (PropHolds ((1 : Q) ≶ 0)) by exact (pos_apart_1_0 (y - x) E).
    exact (fst (rationals_to_field_pos_iff (y - x)) E).
  Qed.

  #[export] Instance strictly_order_reflecting_rationals_to_field
    `{!PropHolds ((1 : Q) ≶ 0)}
    : StrictlyOrderReflecting (rationals_to_field Q F).
  Proof.
    intros x y E.
    apply flip_pos_minus in E; apply flip_pos_minus.
    rewrite <- preserves_minus in E.
    exact (snd (rationals_to_field_pos_iff (y - x)) E).
  Qed.

  #[export] Instance issemiringstrongpreserving_rationals_to_field
    `{!PropHolds ((1 : Q) ≶ 0)}
    : IsSemiRingStrongPreserving (rationals_to_field Q F).
  Proof.
    split; [exact _|].
    intros x y E.
    apply apart_iff_total_lt; apply apart_iff_total_lt in E.
    destruct E; [left | right]; apply (strictly_order_reflecting i); assumption.
  Qed.
End nat_quotients.
