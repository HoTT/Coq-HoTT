Require Import Classes.interfaces.canonical_names.
Require Import WildCat.
Require Import Modalities.ReflectiveSubuniverse.
Require Import Algebra.AbGroups.
Require Import Algebra.Rings.Ring.
Require Import Algebra.Rings.Ideal.
Require Import Algebra.Rings.QuotientRing.
Require Import Algebra.Rings.CRing.

(** * Chinese remainder theorem *)

Import Ideal.Notation.
Local Open Scope ring_scope.
Local Open Scope wc_iso_scope.

Section ChineseRemainderTheorem.

  (** We assume [Univalence] in order to work with quotients. We also need it for [Funext] in a few places.*)
  Context `{Univalence}
    (** We need two coprime ideals [I] and [J] to state the theorem. We don't introduce the coprimeness assumption as of yet in order to show something slightly stronger. *)
    {R : Ring} (I J : Ideal R).

  (** We begin with the homomorphism which will show to be a surjection. Using the first isomorphism theorem for rings we can improve this to be the isomorphism we want. *)
  (** This is the corecursion of the two quotient maps *)
  Definition rng_homo_crt : R $-> (R / I) × (R / J).
  Proof.
    apply ring_product_corec.
    1,2: apply rng_quotient_map.
  Defined.

  (** Since we are working with quotients, we make the following notation to make working with the proof somewhat easier. *)
  Local Notation "[ x ]" := (rng_quotient_map _ x).

  (** We then need to prove the following lemma. The hypotheses here can be derived by coprimality of [I] and [J]. But we don't need that here. *)
  Lemma issurjection_rng_homo_crt' (x y : R)
    (q1 : rng_homo_crt x = (0, 1)) (q2 : rng_homo_crt y = (1, 0))
    : IsSurjection rng_homo_crt.
  Proof.
    (** In order to show that [rng_homo_crt] is a surjection, we need to show that its propositional truncation of the fiber at any point is contractible. *)
    intros [a b].
    revert a; srapply QuotientRing_ind_hprop; intro a.
    revert b; srapply QuotientRing_ind_hprop; intro b.
    (** We can think of [a] and [b] as the pair [(a mod I, b mod J)]. We need to show that there merely exists some element in [R] that gets mapped by  [rng_homo_crt] to the pair. *)
    snapply Build_Contr; [|intros z; strip_truncations; apply path_ishprop].
    (** We make this choice and show it maps as desired. *)
    apply tr; exists (b * x + a * y).
    (** Finally using some simple ring laws we can show it maps to our pair. *)
    rewrite rng_homo_plus.
    rewrite 2 rng_homo_mult.
    rewrite q1, q2.
    apply path_prod.
    + change ([b] * 0 + [a] * 1 = [a] :> R / I).
      by rewrite rng_mult_one_r, rng_mult_zero_r, rng_plus_zero_l.
    + change ([b] * 1 + [a] * 0 = [b] :> R / J).
      by rewrite rng_mult_one_r, rng_mult_zero_r, rng_plus_zero_r.
  Defined.

  (** Now we show that if [x + y = 1] for [I x] and [J y] then we can satisfy the hypotheses of the previous lemma. *)
  Section rng_homo_crt_beta.

    Context (x y : R) (ix : I x) (iy : J y) (p : x + y = 1).

    Lemma rng_homo_crt_beta_left : rng_homo_crt x = (0, 1).
    Proof.
      apply rng_moveR_Mr in p.
      rewrite rng_plus_comm in p.
      apply path_prod; apply qglue.
      - change (I (-x + 0)).
        apply ideal_in_negate_plus.
        1: assumption.
        apply ideal_in_zero.
      - change (J (-x + 1)).
        rewrite rng_plus_comm.
        by rewrite <- p.
    Defined.

    Lemma rng_homo_crt_beta_right : rng_homo_crt y = (1, 0).
    Proof.
      apply rng_moveR_rM in p.
      rewrite rng_plus_comm in p.
      apply path_prod; apply qglue.
      - change (I (-y + 1)).
        by rewrite <- p.
      - change (J (-y + 0)).
        apply ideal_in_negate_plus.
        1: assumption.
        apply ideal_in_zero.
    Defined.

  End rng_homo_crt_beta.

  (** We can now show the map is surjective from coprimality of [I] and [J]. *)
  #[export] Instance issurjection_rng_homo_crt
    : Coprime I J -> IsSurjection rng_homo_crt.
  Proof.
    intros c.
    (** First we turn the coprimality assumption into an equivalent assumption about the mere existence of two elements of each ideal which sum to one. *)
    apply equiv_coprime_sum in c.
    (** Since the goal is a hprop we may strip the truncations. *)
    strip_truncations.
    (** Now we can break apart the data of this witness. *)
    destruct c as [[[x ix] [y jy]] p];
    change (x + y = 1) in p.
    (** Now we apply all our previous lemmas *)
    apply (issurjection_rng_homo_crt' x y).
    1: exact (rng_homo_crt_beta_left x y ix jy p).
    exact (rng_homo_crt_beta_right x y ix jy p).
  Defined.

  (** Now suppose [I] and [J] are coprime. *)
  Context (c : Coprime I J).

  (** The Chinese Remainder Theorem *)
  Theorem chinese_remainder : R / (I ∩ J)%ideal ≅ (R / I) × (R / J).
  Proof.
    (** We use the first isomorphism theorem. Coq can already infer which map we wish to use, so for clarity we tell it not to do so. *)
    snapply rng_first_iso'.
    1: exact rng_homo_crt.
    1: exact _.
    (** Finally we must show the ideal of this map is the intersection. *)
    apply pred_subset_antisymm.
    - intros r [i j].
      apply path_prod; apply qglue.
      1: change (I (- r + 0)).
      2: change (J (- r + 0)).
      1,2: rewrite rng_plus_comm.
      1,2: apply ideal_in_plus_negate.
      1,3: apply ideal_in_zero.
      1,2: assumption.
    - intros i p.
      apply equiv_path_prod in p.
      destruct p as [p q].
      apply ideal_in_negate'.
      rewrite <- rng_plus_zero_r.
      (** Here we need to derive the relation from paths in the quotient. This is what requires univalence. *)
      split.
      1: exact (related_quotient_paths _ _ _ p).
      1: exact (related_quotient_paths _ _ _ q).
  Defined.

End ChineseRemainderTheorem.

(** We also have the same for products of ideals when in a commutative ring. *)
Theorem chinese_remainder_prod `{Univalence}
  {R : CRing} (I J : Ideal R) (c : Coprime I J)
  : R / (I ⋅ J)%ideal ≅ (R / I) × (R / J).
Proof.
  etransitivity.
  { rapply rng_quotient_invar.
    symmetry.
    rapply ideal_intersection_is_product. }
  rapply chinese_remainder.
Defined.
