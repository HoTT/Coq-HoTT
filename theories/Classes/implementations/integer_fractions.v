(** * The rationals as the field of fractions of the integers *)

(** For a model [Z] of the integers, the field of fractions [FracField.F Z] is a model of the rationals: we order it by the sign of [num * den], and show that it is initial among fields of characteristic [0].  We also show that every fraction lies below a natural number. *)

From HoTT Require Import Basics Types.Bool Spaces.Nat.Core Misc.BoundedSearch.
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
  theory.integers
  theory.dec_fields
  theory.fields
  orders.rings
  orders.integers
  orders.nat_int.

Import (hints) Frac FracField.
Generalizable Variables R.

Section ring_identities.
  Context `{IsCRing R}.

  Local Lemma mult_swap_middle (a b c d : R) : (a * b) * (c * d) = (a * c) * (b * d).
  Proof.
    rewrite <- !mult_assoc; apply ap.
    rewrite !mult_assoc; apply (ap (.* d)), mult_comm.
  Qed.

  Local Lemma plus_mult_product (a b c d : R) : (a + b) * (c * d) = (a * c) * d + (b * d) * c.
  Proof.
    rewrite plus_mult_distr_r, !mult_assoc, <- (mult_assoc b), (mult_comm c d), mult_assoc.
    reflexivity.
  Qed.
End ring_identities.

Section contents.
  Context `{Funext} `{Univalence}.
  Context (Z : Type) `{Integers Z} `{!TrivialApart Z}.

  Local Existing Instance Frac.den_ne_0.

  Local Notation Frac := (Frac.Frac Z).
  Local Notation Q := (FracField.F Z).


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
  #[export] Instance fracfield_lt : Lt Q := fun x y => fracfield_pos (y - x) = true.
  #[export] Instance fracfield_le : Le Q := fun x y => fracfield_pos (x - y) = false.
  #[export] Instance fracfield_apart : Apart Q := fun x y => x <> y.

  #[export] Instance trivialapart_fracfield : TrivialApart Q.
  Proof.
    split; [exact _|]. intros x y; reflexivity.
  Qed.

  Local Instance isapart_fracfield : IsApart Q := dec_strong_setoid.

  Local Lemma minus_minus_swap (x y z : Q) : (y - x) + (x - z) = y - z.
  Proof.
    rewrite <- plus_assoc, (plus_assoc (- x)), plus_negate_l, plus_0_l.
    reflexivity.
  Qed.

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
      + rewrite <- (minus_minus_swap x y z); exact (is_pos_plus _ _ ltxy pxz).
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
  Section to_field.
    Context {B : Type} `{IsField B} `{!FieldCharacteristic B 0}.

    Local Notation iZ := (integers_to_ring Z B).
    Local Notation nB := (naturals_to_semiring nat B).
    Local Notation nZ := (naturals_to_semiring nat Z).

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

    Local Lemma int_to_field_nat (n : nat) : iZ (nZ n) = nB n.
    Proof.
      assert (IsSemiRingPreserving (iZ o nZ)) by rapply compose_sr_morphism.
      symmetry; exact (toR_unique (iZ o nZ) n).
    Qed.

    Lemma int_to_field_apart_zero (d : Z) : d <> 0 -> iZ d ≶ 0.
    Proof.
      intros ne.
      assert (nn : forall n : nat, (nZ n = d) + (nZ n = - d) -> n <> 0%nat).
      { intros n p q; rewrite q in p; apply ne.
        destruct p as [p|p].
        - rewrite <- p; exact preserves_0.
        - rewrite (preserves_0 (f:=nZ)) in p.
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
      refine (frac_to_field_unique (Frac.pl _ x y) _ _).
      cbn [Frac.num Frac.den Frac.pl].
      rewrite (preserves_plus (f:=iZ) (Frac.num x * Frac.den y)), !(preserves_mult (f:=iZ)).
      rewrite plus_mult_product.
      rewrite !frac_to_field_mult_den; reflexivity.
    Qed.

    Lemma rationals_to_field_frac_mult (x y : Q) : f (x * y) = f x * f y.
    Proof.
      revert x y; srapply FracField.F_ind2; intros x y.
      refine (frac_to_field_unique (Frac.ml _ x y) _ _).
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
      rewrite 2!(integers_initial (h:=h o cast Z Q)); unfold Compose.
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

  Local Notation nZ := (naturals_to_semiring nat Z).
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
    apply pos_ge_1, den_square_pos.
  Qed.

  #[export] Instance roundupstrict_fracfield : RoundUpStrict Q.
  Proof.
    intros q; apply minimal_n; [exact _|].
    revert q; srapply FracField.F_ind; intros x.
    exact (tr (frac_round_up x)).
  Qed.
End contents.
