(** * The rationals as the field of fractions of the integers *)

(** For a model [Z] of the integers, the field of fractions [FracField.F Z] is a model of the rationals: we order it by the sign of [num * den], and show that it is initial among fields of characteristic [0].  We also show that every fraction lies below a natural number, and that the field of fractions is equivalent to the natural numbers. *)

From HoTT Require Import Basics Types.Bool Truncations.Core Spaces.Nat.Core Spaces.Nat.Enumeration
  Misc.BoundedSearch.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.naturals
  interfaces.integers
  interfaces.rationals
  interfaces.round
  implementations.peano_naturals
  implementations.field_of_fractions
  theory.apartness
  theory.rings
  theory.dec_fields
  theory.fields
  orders.rings
  orders.orders
  orders.naturals
  orders.nat_int.

Import (hints) Frac FracField.
Generalizable Variables R.

Section ring_identities.
  Context `{IsCRing R}.

  Local Lemma plus_mult_product (a b c d : R) : (a + b) * (c * d) = (a * c) * d + (b * d) * c.
  Proof.
    rewrite plus_mult_distr_r, !mult_assoc, <- (mult_assoc b), (mult_comm c d), mult_assoc.
    reflexivity.
  Qed.

  Local Lemma minus_plus_minus (p q r s : R) : (p - q) + (r - s) = (p + r) - (q + s).
  Proof.
    rewrite plus_swap_middle, negate_plus_distr; reflexivity.
  Qed.

  Local Lemma minus_mult_minus (p q r s : R) : (p - q) * (r - s) = (p * r + q * s) - (p * s + q * r).
  Proof.
    rewrite plus_mult_distr_r, !plus_mult_distr_l, negate_mult_negate.
    rewrite <- negate_mult_distr_r, <- negate_mult_distr_l, (plus_comm (- (q * r))).
    apply minus_plus_minus.
  Qed.
End ring_identities.

Section contents.
  Context `{Funext} `{Univalence}.
  Universe UZ.
  Context (Z : Type@{UZ}) `{Integers Z} `{!TrivialApart Z} {Zset : IsHSet Z}
    {Zdec : DecidablePaths Z} {Zdom : IsIntegralDomain Z} {Zprod : ZeroProduct Z}
    {Zabs : IntAbs Z nat}.

  Local Existing Instance Frac.den_ne_0.

  Local Notation Frac := (Frac.Frac Z).
  Local Notation Q := (FracField.F Z).

  Local Instance decidable_lt_int (x y : Z) : Decidable (x < y).
  Proof.
    destruct (trichotomy (<) x y) as [l|[e|l]].
    - exact (inl l).
    - right; intros l'; rewrite e in l'; exact (irreflexivity (<) y l').
    - right; intros l'; exact (irreflexivity (<) x (transitivity l' l)).
  Defined.

  Local Lemma int_pos_ge_1 (z : Z) : 0 < z -> 1 <= z.
  Proof.
    intros zpos; destruct (int_abs_sig Z nat z) as [[[|c] p]|[k p]].
    - destruct p; destruct (irreflexivity (<) _ zpos).
    - rewrite <- p, nat_to_semiring_succ.
      apply nonneg_plus_le_compat_r, nat_to_semiring_nonneg.
    - apply Empty_rec, (irreflexivity (<) (0 : Z)).
      apply (lt_le_trans _ z _ zpos).
      apply (snd (flip_nonpos_negate z)); rewrite <- p; apply nat_to_semiring_nonneg.
  Qed.


  Local Lemma den_square_pos (x : Frac) : 0 < Frac.den x * Frac.den x.
  Proof.
    apply square_pos, trivial_apart, Frac.den_ne_0.
  Qed.

  (** A fraction is positive when its numerator and denominator have the same sign.  We use a boolean, so that positivity descends to the quotient without univalence and is decidable. *)
  Definition frac_pos (x : Frac) : Bool := if dec (0 < Frac.num x * Frac.den x) then true else false.

  Lemma frac_pos_spec (x : Frac) : frac_pos x = true <-> 0 < Frac.num x * Frac.den x.
  Proof.
    unfold frac_pos; destruct (dec _) as [l|nl]; split; intro p.
    - exact l.
    - reflexivity.
    - destruct (false_ne_true p).
    - destruct (nl p).
  Qed.

  Local Lemma bool_path_iff (b c : Bool) : (b = true <-> c = true) -> b = c.
  Proof.
    destruct b, c; intros [f g]; try reflexivity.
    - exact (f idpath)^.
    - exact (g idpath).
  Qed.

  Local Lemma not_true_iff_false (b : Bool) : ~ (b = true) <-> b = false.
  Proof.
    destruct b; split; intros p.
    - destruct (p idpath).
    - destruct (true_ne_false p).
    - reflexivity.
    - exact false_ne_true.
  Qed.

  Local Lemma bool_true_or_false (b : Bool) : (b = true) + (b = false).
  Proof.
    destruct b; [left|right]; reflexivity.
  Qed.

  Local Lemma frac_pos_respect_aux (x y : Frac) (E : Frac.equiv x y)
    : 0 < Frac.num x * Frac.den x -> 0 < Frac.num y * Frac.den y.
  Proof.
    intros px.
    apply (pos_mult_rev_l _ (Frac.den x * Frac.den x)); [|apply den_square_pos].
    assert (p : (Frac.num y * Frac.den y) * (Frac.den x * Frac.den x)
                = (Frac.num x * Frac.den x) * (Frac.den y * Frac.den y)).
    { rewrite (mult_swap_middle (Frac.num y)), (mult_comm (Frac.den y) (Frac.den x)).
      rewrite <- E, (mult_swap_middle (Frac.num x)).
      reflexivity. }
    rewrite p; apply pos_mult; [exact px|apply den_square_pos].
  Qed.

  Lemma frac_pos_respect (x y : Frac) : Frac.equiv x y -> frac_pos x = frac_pos y.
  Proof.
    intros E; apply bool_path_iff.
    split; intros p; apply frac_pos_spec; apply frac_pos_spec in p.
    - exact (frac_pos_respect_aux x y E p).
    - exact (frac_pos_respect_aux y x E^ p).
  Qed.

  Definition fracfield_pos : Q -> Bool := FracField.F_rec frac_pos frac_pos_respect.

  Local Lemma plus_over_product (a b d e : Z)
    : (a * e + b * d) * (d * e) = (a * d) * (e * e) + (b * e) * (d * d).
  Proof.
    rewrite plus_mult_distr_r.
    rewrite (mult_swap_middle a e d e).
    rewrite (mult_comm d e), (mult_swap_middle b d e d).
    reflexivity.
  Qed.

  Lemma is_pos_plus (x y : Q) : fracfield_pos x = true -> fracfield_pos y = true -> fracfield_pos (x + y) = true.
  Proof.
    revert x y; srapply (FracField.F_ind2 (fun x y => _ -> _ -> _)).
    intros x y px py; apply frac_pos_spec; apply frac_pos_spec in px, py.
    cbn; rewrite plus_over_product.
    apply pos_plus_compat; apply pos_mult; trivial; apply den_square_pos.
  Qed.

  Lemma is_pos_mult (x y : Q) : fracfield_pos x = true -> fracfield_pos y = true -> fracfield_pos (x * y) = true.
  Proof.
    revert x y; srapply (FracField.F_ind2 (fun x y => _ -> _ -> _)).
    intros x y px py; apply frac_pos_spec; apply frac_pos_spec in px, py.
    cbn; rewrite mult_swap_middle.
    apply pos_mult; assumption.
  Qed.

  Lemma is_pos_negate (x : Q) : fracfield_pos x = true -> fracfield_pos (- x) = true -> Empty.
  Proof.
    revert x; srapply (FracField.F_ind (fun x => _ -> _ -> _)).
    intros x px pnx; apply frac_pos_spec in px, pnx; cbn in pnx.
    rewrite <- negate_mult_distr_l in pnx.
    apply flip_neg_negate in pnx.
    exact (irreflexivity (<) 0 (transitivity pnx px)).
  Qed.

  Lemma is_pos_zero : fracfield_pos 0 = false.
  Proof.
    apply not_true_iff_false; intros p; apply frac_pos_spec in p; cbn in p.
    rewrite mult_0_l in p; exact (irreflexivity (<) 0 p).
  Qed.

  Lemma is_pos_zero_cases (x : Q) : fracfield_pos x = false -> fracfield_pos (- x) = false -> x = 0.
  Proof.
    revert x; srapply (FracField.F_ind (fun x => _ -> _ -> _)).
    intros x px pnx.
    apply (snd (not_true_iff_false _)) in px, pnx.
    apply FracField.path; unfold Frac.equiv; cbn.
    rewrite mult_0_l, mult_1_r.
    destruct (trichotomy (<) 0 (Frac.num x * Frac.den x)) as [l|[e|l]].
    - destruct (px (snd (frac_pos_spec _) l)).
    - destruct (zero_product _ _ e^) as [n0|d0].
      + exact n0.
      + destruct (Frac.den_ne_0 x d0).
    - destruct pnx; apply frac_pos_spec; cbn.
      rewrite <- negate_mult_distr_l.
      apply flip_neg_negate, l.
  Qed.

  (** The order, and the trivial apartness, on the field of fractions. *)
  #[export] Instance fracfield_lt : Lt@{UZ UZ} Q := fun x y => fracfield_pos (y - x) = true.
  #[export] Instance fracfield_le : Le@{UZ UZ} Q := fun x y => fracfield_pos (x - y) = false.
  #[export] Instance fracfield_apart : Apart@{UZ UZ} Q := fun x y => x <> y.

  #[export] Instance trivialapart_fracfield : TrivialApart Q.
  Proof.
    split; [exact _|]. intros x y; reflexivity.
  Qed.

  Local Instance isapart_fracfield : IsApart Q := dec_strong_setoid.

  Local Lemma plus_minus_plus (x y z : Q) : (z + y) - (z + x) = y - x.
  Proof.
    rewrite negate_plus_distr, (plus_comm z y), plus_assoc.
    rewrite <- (plus_assoc y z), plus_negate_r, plus_0_r.
    reflexivity.
  Qed.

  Local Lemma is_pos_minus_zero (x : Q) : fracfield_pos (x - 0) = fracfield_pos x.
  Proof.
    rewrite negate_0, plus_0_r; reflexivity.
  Qed.

  #[export] Instance pseudoorder_fracfield : PseudoOrder fracfield_lt.
  Proof.
    split.
    - exact _.
    - exact _.
    - intros x y [ltxy ltyx]; unfold lt, fracfield_lt in *.
      rewrite negate_swap_r in ltyx.
      exact (is_pos_negate _ ltxy ltyx).
    - intros x y ltxy z; apply tr; unfold lt, fracfield_lt in *.
      destruct (bool_true_or_false (fracfield_pos (z - x))) as [pzx|pzx]; [left; exact pzx|right].
      destruct (bool_true_or_false (fracfield_pos (x - z))) as [pxz|pxz].
      + rewrite <- (plus_minus_telescope y x z); exact (is_pos_plus _ _ ltxy pxz).
      + rewrite negate_swap_r in pxz.
        rewrite (fst (equal_by_zero_sum z x) (is_pos_zero_cases _ pzx pxz)).
        exact ltxy.
    - intros x y; split.
      + intros ne; unfold lt, fracfield_lt.
        destruct (bool_true_or_false (fracfield_pos (y - x))) as [pyx|pyx]; [left; exact pyx|right].
        destruct (bool_true_or_false (fracfield_pos (x - y))) as [pxy|pxy]; [exact pxy|].
        rewrite negate_swap_r in pxy.
        destruct (ne (fst (equal_by_zero_sum y x) (is_pos_zero_cases _ pyx pxy))^).
      + intros l p; destruct p; unfold lt, fracfield_lt in l.
        rewrite plus_negate_r, is_pos_zero in l.
        destruct l as [l|l]; exact (false_ne_true l).
  Qed.

  #[export] Instance fullpseudoorder_fracfield : FullPseudoOrder fracfield_le fracfield_lt.
  Proof.
    split; [exact _|exact _|].
    intros x y; unfold le, fracfield_le, lt, fracfield_lt.
    split; apply not_true_iff_false.
  Qed.

  #[export] Instance fullpseudosemiringorder_fracfield : FullPseudoSemiRingOrder fracfield_le fracfield_lt.
  Proof.
    apply from_full_pseudo_ring_order.
    - intros z x y; unfold lt, fracfield_lt.
      rewrite plus_minus_plus; exact idmap.
    - exact (dec_strong_binary_morphism (.*.)).
    - intros x y; unfold PropHolds, lt, fracfield_lt; rewrite !is_pos_minus_zero.
      exact (is_pos_mult x y).
  Qed.

  (** ** Initiality *)

  (** The fraction [n / d] goes to [n / d] in any field of characteristic [0]: the integer [d] is apart from [0] there. *)
  Local Notation nZ := (naturals_to_semiring nat Z).

  Local Lemma nat_to_int_lt (n c : nat) : nZ n < nZ (S c + n).
  Proof.
    rewrite (preserves_plus (f:=nZ)).
    exact (pos_plus_lt_compat_l _ _ (nat_to_semiring_succ_pos c)).
  Qed.

  Local Lemma nat_to_int_injective (n m : nat) : nZ n = nZ m -> n = m.
  Proof.
    intros p; destruct (nat_trichotomy n m) as [l|[e|l]]; [|exact e|].
    - destruct (equiv_leq_add (S n) m l) as [k q]; destruct q.
      rewrite nat_add_succ_r in p.
      destruct (irreflexivity (<) (nZ n) (transport (fun z => nZ n < z) p^ (nat_to_int_lt n k))).
    - destruct (equiv_leq_add (S m) n l) as [k q]; destruct q.
      rewrite nat_add_succ_r in p.
      destruct (irreflexivity (<) (nZ m) (transport (fun z => nZ m < z) p (nat_to_int_lt m k))).
  Qed.

  Local Lemma int_difference (z : Z) : {a : nat & {b : nat & nZ a - nZ b = z}}.
  Proof.
    destruct (int_abs_sig Z nat z) as [[a p]|[a p]].
    - exists a, 0%nat; change (nZ 0%nat) with (0 : Z); rewrite negate_0, plus_0_r; exact p.
    - exists 0%nat, a; change (nZ 0%nat) with (0 : Z); rewrite plus_0_l, p; apply negate_involutive.
  Qed.

  Section to_field.
    Context {B : Type} `{IsField B} `{!FieldCharacteristic B 0}.

    Local Notation nB := (naturals_to_semiring nat B).

    Local Lemma nat_to_field_iter (n : nat) : nB n = nat_iter n (1 +) 0.
    Proof.
      induction n as [|n IH].
      - reflexivity.
      - change (nB (1 + n) = 1 + nat_iter n (1 +) 0).
        rewrite (preserves_plus (f:=nB)), preserves_1, IH; reflexivity.
    Qed.

    Local Lemma nat_to_field_apart_zero (n : nat) : n <> 0%nat -> nB n ≶ 0.
    Proof.
      intros ne; rewrite nat_to_field_iter.
      destruct n as [|n]; [destruct (ne idpath)|].
      apply (fst (field_characteristic B (S n) _)).
      intros m p; exact (neq_nat_zero_succ n p^).
    Qed.

    (** We map the integers into [B] through the natural numbers, using absolute values. *)
    Definition int_to_field (z : Z) : B
      := match int_abs_sig Z nat z with
         | inl (n; _) => nB n
         | inr (n; _) => - nB n
         end.

    Local Notation iZ := int_to_field.

    Local Lemma int_to_field_nat_minus (a b : nat) : iZ (nZ a - nZ b) = nB a - nB b.
    Proof.
      unfold int_to_field; destruct (int_abs_sig Z nat (nZ a - nZ b)) as [[k p]|[k p]].
      - assert (e : (k + b)%nat = a).
        { apply nat_to_int_injective; rewrite (preserves_plus (f:=nZ)), p.
          rewrite <- plus_assoc, plus_negate_l; apply plus_0_r. }
        rewrite <- e, (preserves_plus (f:=nB)), <- plus_assoc, plus_negate_r; symmetry; apply plus_0_r.
      - assert (e : (k + a)%nat = b).
        { apply nat_to_int_injective; rewrite (preserves_plus (f:=nZ)), p.
          rewrite <- negate_swap_l, (plus_comm (- nZ a)), <- plus_assoc, plus_negate_l; apply plus_0_r. }
        rewrite <- e, (preserves_plus (f:=nB)), negate_plus_distr, (plus_comm (- nB k)), plus_assoc.
        rewrite plus_negate_r, plus_0_l; reflexivity.
    Qed.

    Local Lemma int_to_field_nat (n : nat) : iZ (nZ n) = nB n.
    Proof.
      refine (ap iZ _ @ int_to_field_nat_minus n 0 @ _).
      - change (nZ n = nZ n - 0); rewrite negate_0; symmetry; apply plus_0_r.
      - change (nB n - 0 = nB n); rewrite negate_0; apply plus_0_r.
    Qed.

    #[export] Instance issemiringpreserving_int_to_field : IsSemiRingPreserving iZ.
    Proof.
      repeat split.
      - intros x y; change (iZ (x + y) = iZ x + iZ y).
        destruct (int_difference x) as [a [b []]], (int_difference y) as [c [d []]].
        rewrite minus_plus_minus, <- !(preserves_plus (f:=nZ)), !int_to_field_nat_minus.
        rewrite !(preserves_plus (f:=nB)); symmetry; apply minus_plus_minus.
      - exact (int_to_field_nat 0).
      - intros x y; change (iZ (x * y) = iZ x * iZ y).
        destruct (int_difference x) as [a [b []]], (int_difference y) as [c [d []]].
        rewrite minus_mult_minus, <- !(preserves_mult (f:=nZ)), <- !(preserves_plus (f:=nZ)).
        rewrite !int_to_field_nat_minus.
        rewrite (preserves_plus (f:=nB) (a * c)), (preserves_plus (f:=nB) (a * d)).
        rewrite (preserves_mult (f:=nB) a c), (preserves_mult (f:=nB) b d).
        rewrite (preserves_mult (f:=nB) a d), (preserves_mult (f:=nB) b c).
        symmetry; apply minus_mult_minus.
      - exact (int_to_field_nat 1).
    Qed.

    (** Every semiring morphism from the integers agrees with [int_to_field]. *)
    Lemma int_to_field_unique (g : Z -> B) `{!IsSemiRingPreserving g} (z : Z) : g z = iZ z.
    Proof.
      destruct (int_difference z) as [a [b []]].
      assert (IsSemiRingPreserving (g o nZ)) by rapply compose_sr_morphism.
      rewrite int_to_field_nat_minus, (preserves_minus (f:=g)).
      rewrite <- (toR_unique (g o nZ) a), <- (toR_unique (g o nZ) b); reflexivity.
    Qed.

    Lemma int_to_field_apart_zero (d : Z) : d <> 0 -> iZ d ≶ 0.
    Proof.
      intros ne.
      assert (nn : forall n : nat, (nZ n = d) + (nZ n = - d) -> n <> 0%nat).
      { intros n p q; rewrite q in p; apply ne.
        destruct p as [p|p].
        - rewrite <- p; exact preserves_0.
        - change (nZ 0%nat) with (0 : Z) in p.
          exact (fst (flip_negate_0 d) p^). }
      destruct (int_abs_sig Z nat d) as [[n p]|[n p]].
      - rewrite <- p, int_to_field_nat.
        exact (nat_to_field_apart_zero n (nn n (inl p))).
      - rewrite <- (negate_involutive d), <- p, preserves_negate, int_to_field_nat.
        exact (apart_negate _ (nat_to_field_apart_zero n (nn n (inr p)))).
    Qed.

    Local Definition den_apart (x : Frac) : ApartZero B
      := exist (fun y => y ≶ 0) (iZ (Frac.den x)) (int_to_field_apart_zero _ (Frac.den_ne_0 x)).

    Definition frac_to_field (x : Frac) : B := iZ (Frac.num x) // den_apart x.

    Lemma frac_to_field_mult_den (x : Frac) : frac_to_field x * iZ (Frac.den x) = iZ (Frac.num x).
    Proof.
      unfold frac_to_field.
      rewrite <- mult_assoc, (mult_comm (// _)), (recip_inverse (den_apart x)).
      apply mult_1_r.
    Qed.

    (** The image of a fraction is determined by its product with the image of the denominator. *)
    Lemma frac_to_field_unique (x : Frac) (y : B)
      : y * iZ (Frac.den x) = iZ (Frac.num x) -> frac_to_field x = y.
    Proof.
      intros p; unfold frac_to_field; rewrite <- p.
      rewrite <- mult_assoc, (recip_inverse (den_apart x)).
      apply mult_1_r.
    Qed.

    Lemma frac_to_field_respect (x y : Frac) : Frac.equiv x y -> frac_to_field x = frac_to_field y.
    Proof.
      intros E; apply frac_to_field_unique.
      apply (right_cancellation_ne_0 (.*.) (iZ (Frac.den y)));
        [apply apart_ne, int_to_field_apart_zero, Frac.den_ne_0|].
      rewrite <- mult_assoc, (mult_comm (iZ (Frac.den x))), mult_assoc.
      rewrite frac_to_field_mult_den, <- !(preserves_mult (f:=iZ)).
      exact (ap iZ E^).
    Qed.

    Definition rationals_to_field_frac : Q -> B
      := FracField.F_rec frac_to_field frac_to_field_respect.
    Local Notation f := rationals_to_field_frac.

    Lemma rationals_to_field_frac_plus (x y : Q) : f (x + y) = f x + f y.
    Proof.
      revert x y; srapply FracField.F_ind2; intros x y.
      napply (frac_to_field_unique (Frac.pl _ x y)).
      cbn [Frac.num Frac.den Frac.pl].
      rewrite (preserves_plus (f:=iZ) (Frac.num x * Frac.den y)), !(preserves_mult (f:=iZ)).
      rewrite plus_mult_product.
      rewrite !frac_to_field_mult_den; reflexivity.
    Qed.

    Lemma rationals_to_field_frac_mult (x y : Q) : f (x * y) = f x * f y.
    Proof.
      revert x y; srapply FracField.F_ind2; intros x y.
      napply (frac_to_field_unique (Frac.ml _ x y)).
      cbn [Frac.num Frac.den Frac.ml].
      rewrite !(preserves_mult (f:=iZ)), mult_swap_middle.
      rewrite !frac_to_field_mult_den; reflexivity.
    Qed.

    #[export] Instance issemiringpreserving_rationals_to_field_frac : IsSemiRingPreserving f.
    Proof.
      repeat split.
      - exact rationals_to_field_frac_plus.
      - apply frac_to_field_unique; cbn.
        rewrite mult_0_l; exact preserves_0^.
      - exact rationals_to_field_frac_mult.
      - apply frac_to_field_unique; cbn.
        rewrite mult_1_l; reflexivity.
    Qed.

    Lemma rationals_to_field_frac_unique (h : Q -> B) `{!IsSemiRingPreserving h} (q : Q)
      : f q = h q.
    Proof.
      revert q; srapply FracField.F_ind; intros x; apply frac_to_field_unique.
      assert (IsSemiRingPreserving (h o cast Z Q)) by rapply compose_sr_morphism.
      rewrite <- 2!(int_to_field_unique (h o cast Z Q)); unfold Compose.
      rewrite <- (preserves_mult (f:=h)); apply ap.
      apply FracField.path; unfold Frac.equiv; cbn.
      rewrite !mult_1_r; reflexivity.
    Qed.
  End to_field.

  #[export] Instance rationalstofield_fracfield : RationalsToField Q
    := fun B _ _ _ _ _ _ _ _ _ => rationals_to_field_frac.

  #[export] Instance rationals_fracfield : Rationals Q.
  Proof.
    split.
    - exact _.
    - exact _.
    - intros B ? ? ? ? ? ? ? ? ?; exact _.
    - intros B ? ? ? ? ? ? ? ? ? h ? q; exact (rationals_to_field_frac_unique h q).
  Qed.

  (** ** Rounding up *)

  Local Notation nQ := (naturals_to_semiring nat Q).

  Local Lemma nat_to_rationals_int (n : nat) : nQ n = ' (nZ n).
  Proof.
    assert (IsSemiRingPreserving (cast Z Q o nZ)) by rapply compose_sr_morphism.
    exact (toR_unique (cast Z Q o nZ) n).
  Qed.

  (** Every integer lies strictly below the image of some natural number. *)
  Local Lemma int_round_up (z : Z) : {m : nat & z < nZ m}.
  Proof.
    assert (le : {k : nat & z <= nZ k}).
    { destruct (int_abs_sig Z nat z) as [[k p]|[k p]]; exists k.
      - rewrite p; reflexivity.
      - apply (transitivity (y:=0)).
        + apply flip_nonpos_negate; rewrite <- p; apply to_semiring_nonneg.
        + apply to_semiring_nonneg. }
    destruct le as [k le]; exists (S k).
    change (z < nZ (1 + k)); rewrite (preserves_plus (f:=nZ) 1 k), preserves_1.
    apply (le_lt_trans _ (nZ k)); [exact le|].
    apply pos_plus_lt_compat_l, lt_0_1.
  Qed.

  (** Every fraction lies strictly below the image of some natural number; on the quotient we choose the least one, by bounded search. *)
  Local Lemma frac_round_up (x : Frac) : {m : nat & ' x < nQ m}.
  Proof.
    destruct (int_round_up (Frac.num x * Frac.den x)) as [m l]; exists m.
    unfold lt, fracfield_lt; rewrite nat_to_rationals_int; apply frac_pos_spec.
    cbn [Frac.num Frac.den Frac.pl Frac.neg Frac.Frac_inject].
    rewrite mult_1_r, mult_1_l, plus_mult_distr_r, <- mult_assoc, <- negate_mult_distr_l.
    apply (snd (flip_pos_minus _ _)).
    apply (lt_le_trans _ (nZ m)); [exact l|].
    apply ge_1_mult_le_compat_r; [|apply to_semiring_nonneg|reflexivity].
    apply int_pos_ge_1, den_square_pos.
  Qed.

  #[export] Instance roundupstrict_fracfield : RoundUpStrict Q.
  Proof.
    intros q; apply minimal_n; [exact _|].
    revert q; srapply FracField.F_ind; intros x.
    exact (tr (frac_round_up x)).
  Qed.
End contents.

(** ** Enumeration *)

(** The fractions [(a - b) / (c + 1)] of natural numbers cover the field of fractions, which is therefore equivalent to the natural numbers. *)
Section enumeration.
  Context `{Funext} `{Univalence}.
  Universe UZ.
  Context (Z : Type@{UZ}) `{Integers Z} `{!TrivialApart Z} {Zset : IsHSet Z}
    {Zdec : DecidablePaths Z} {Zdom : IsIntegralDomain Z} {Zprod : ZeroProduct Z}
    {Zabs : IntAbs Z nat}.

  Local Existing Instance Frac.den_ne_0.
  Local Notation Frac := (Frac.Frac Z).
  Local Notation Q := (FracField.F Z).
  Local Notation nZ := (naturals_to_semiring nat Z).
  Local Notation nQ := (naturals_to_semiring nat Q).

  Local Lemma int_succ_ne_0 (c : nat) : nZ (S c) <> 0.
  Proof.
    intros p; apply (irreflexivity (<) (0 : Z)).
    exact (transport (fun z => 0 < z) p (nat_to_semiring_succ_pos c)).
  Qed.

  (** The fraction with numerator [a - b] and denominator [c + 1]. *)
  Local Definition frac_of_nats (a b c : nat) : Frac
    := Frac.frac (nZ a - nZ b) (nZ (S c)) (int_succ_ne_0 c).

  Definition fracfield_enumerator (n : nat) : Q
    := match nat_unpair n with
       | (a, m) => match nat_unpair m with
                  | (b, c) => ' (frac_of_nats a b c)
                  end
       end.

  Local Lemma int_pos_succ (z : Z) : 0 < z -> {c : nat & nZ (S c) = z}.
  Proof.
    intros zpos.
    destruct (int_abs_sig Z nat z) as [[[|c] p]|[k p]].
    - change (nZ 0%nat) with (0 : Z) in p; destruct p; destruct (irreflexivity (<) _ zpos).
    - exact (c; p).
    - apply Empty_rec, (irreflexivity (<) (0 : Z)).
      apply (lt_le_trans _ z _ zpos).
      apply (snd (flip_nonpos_negate z)); rewrite <- p; apply nat_to_semiring_nonneg.
  Qed.

  Lemma fracfield_enumerator_hit (x : Frac) : {n : nat & fracfield_enumerator n = ' x}.
  Proof.
    destruct (int_difference Z (Frac.num x * Frac.den x)) as [a [b p]].
    destruct (int_pos_succ (Frac.den x * Frac.den x)) as [c q].
    { apply square_pos, trivial_apart, Frac.den_ne_0. }
    destruct (nat_unpair_hit b c) as [m r].
    destruct (nat_unpair_hit a m) as [n s].
    exists n; unfold fracfield_enumerator; rewrite s, r.
    apply FracField.path; unfold Frac.equiv, frac_of_nats; cbn [Frac.num Frac.den].
    rewrite p, q; symmetry; apply mult_assoc.
  Qed.

  (** Finitely many fractions lie below the image of a natural number. *)
  Local Lemma fracfield_avoid (g : nat -> Q) (n : nat) : {x : Q & forall m, (m <= n)%nat -> g m <> x}.
  Proof.
    destruct (nat_bound (fun m => (round_up_strict Q (g m)).1) n) as [k l].
    exists (nQ k); intros m lm p.
    apply (irreflexivity (<) (g m)).
    apply (lt_le_trans _ (nQ (round_up_strict Q (g m)).1)).
    - exact (round_up_strict Q (g m)).2.
    - refine (transport (fun w => _ <= w) p^ _).
      apply nat_to_semiring_le, leq_lt, l, lm.
  Qed.

  Definition equiv_nat_fracfield : nat <~> Q.
  Proof.
    apply (equiv_nat_enumeration fracfield_enumerator).
    - srapply FracField.F_ind; intros x; exact (tr (fracfield_enumerator_hit x)).
    - exact (fracfield_avoid fracfield_enumerator).
  Defined.
End enumeration.
