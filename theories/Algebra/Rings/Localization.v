Require Import Basics.Overture Basics.Trunc Basics.Tactics WildCat.Core
  abstract_algebra Rings.CRing Truncations.Core Nat.Core.

Local Open Scope mc_scope.

(** * Localization of commutative rings *)

(** Localization is a way to make elements in a commutative ring invertible by adding inverses, in the most minimal way possible. It generalizes the familiar operation of a field of fractions. *)

(** ** Multiplicative subsets *)

(** A multiplicative subset is formally a submonoid of the multiplicative monoid of a ring. Essentially it is a subset closed under finite products. *)

(** *** Definition *)

(** Multiplicative subsets of a ring [R] consist of: *)
Class IsMultiplicativeSubset {R : CRing} (S : R -> Type) : Type := {
  (** Contains one *)
  mss_one : S 1 ;
  (** Closed under multiplication *)
  mss_mult : forall x y, S x -> S y -> S (x * y) ;
}.

Arguments mss_one {R _ _}.
Arguments mss_mult {R _ _ _ _}.

(** *** Examples *)

(** The multiplicative subset of powers of a ring element. *)
Global Instance ismultiplicative_powers (R : CRing) (x : R)
  : IsMultiplicativeSubset (fun r => exists n, rng_power x n = r).
Proof.
  srapply Build_IsMultiplicativeSubset; cbn beta.
  1: by exists 0%nat.
  intros a b np mq.
  destruct np as [n p], mq as [m q].
  exists (n + m)%nat.
  lhs_V nrapply rng_power_mult_law.
  f_ap.
Defined.

(** Invertible elements of a ring form a multiplicative subset. *)
Global Instance ismultiplicative_isinvertible (R : CRing)
  : IsMultiplicativeSubset (@IsInvertible R) := {}.

(** TODO: Property of being a localization. *)

(** ** Construction of localization *)

Section Localization.

  (** We now construct the localization of a ring at a multiplicative subset as the following HIT:

  <<<
  HIT Localization_type (R : CRing) (S : R -> Type)
    `{IsMultiplicativeSubset R} :=
  | loc_frac (n d : R) (p : S d) : Localization R S
  | loc_frac_eq (n1 d1 n2 d2 : R) (p1 : S d1) (p2 : S d2)
      (x : R) (q : S x) (r : x * (d2 * n1 - n2 * d1) = 0)
      : loc_frac n1 d1 p1 = loc_frac n2 d2 p2
  .
  >>>
  along with the condition that this HIT be a set.

  We will implement this HIT by writing it as a set quotient.
  *)

  Context (R : CRing) (S : R -> Type) `{!IsMultiplicativeSubset S}.

  (** *** Construction of underlying Localization type *)

  (** The base type will be the type of fractions with respect to a multiplicative subset. This consists of pairs of elements of a ring [R] where the [denominator] is in the multiplicative subset [S]. *)
  Record Fraction := {
    numerator : R ;
    denominator : R ;
    in_mult_subset_denominator : S denominator ;
  }.

  (** We consider two fractions to be equal if we can rearrange the fractions as products and ask for equality upto some scaling factor from the multiplicative subset [S]. *)
  Definition fraction_eq : Relation Fraction.
  Proof.
    intros [n1 d1 ?] [n2 d2 ?].
    refine (exists (x : R), S x /\ _).
    exact (x * n1 * d2 = x * n2 * d1).
  Defined.

  (** It is convenient to produce elements of this relation specalized to when the scaling factor is [1]. *)
  Definition fraction_eq_simple f1 f2
    (p : numerator f1 * denominator f2 = numerator f2 * denominator f1)
    : fraction_eq f1 f2.
  Proof.
    exists 1.
    refine (mss_one, _).
    lhs_V nrapply rng_mult_assoc.
    rhs_V nrapply rng_mult_assoc.
    exact (ap (1 *.) p).
  Defined.

  (** Fraction equality is a reflexive relation. *)
  Definition fraction_eq_refl f1 : fraction_eq f1 f1.
  Proof.
    apply fraction_eq_simple.
    reflexivity.
  Defined.

  (** The underlying type of the localization of a commutative ring is the quotient of the type of fractions by fraction equality. *)
  Definition Localization_type : Type := Quotient fraction_eq.

  (** Given any fraction, we have an obvious inclusion into the localization type. *)
  Definition loc_frac : Fraction -> Localization_type
    := class_of fraction_eq.

  (** In order to give an equality of included fractions, it suffices to show that the fractions are equal under fraction equality. *)
  Definition loc_frac_eq {f1 f2 : Fraction} (p : fraction_eq f1 f2)
    : loc_frac f1 = loc_frac f2
    := qglue p.

  (** We can give an induction principle for the localization type. *)
  Definition Localization_type_ind (Q : Localization_type -> Type)
    `{forall x, IsHSet (Q x)}
    (frac : forall f, Q (loc_frac f))
    (eq : forall f1 f2 p, loc_frac_eq p # frac f1 = frac f2)
    : forall x, Q x
    := Quotient_ind _ Q frac eq.

  Definition Localization_type_ind_hprop (Q : Localization_type -> Type)
    `{forall x, IsHProp (Q x)} (f : forall f, Q (loc_frac f))
    : forall x, Q x
    := Quotient_ind_hprop _ Q f.

  Definition Localization_type_rec (Q : Type) `{IsHSet Q}
    (f : Fraction -> Q)
    (t : forall f1 f2, fraction_eq f1 f2 -> f f1 = f f2)
    : Localization_type -> Q
    := Quotient_rec _ Q f t.

  Arguments loc_frac : simpl never.
  Arguments loc_frac_eq : simpl never.

  (** Elements of [R] can be considered fractions. *)
  Definition frac_in : R -> Fraction
    := fun r => Build_Fraction r 1 mss_one.

  (** Now that we have defined the HIT as above, we can define the ring structure. *)

  (** *** Addition operation *)

  (** Fraction addition is the usual addition of fractions. *)
  Definition frac_add : Fraction -> Fraction -> Fraction :=
    fun '(Build_Fraction n1 d1 p1) '(Build_Fraction n2 d2 p2)
      => Build_Fraction (n1 * d2 + n2 * d1) (d1 * d2) (mss_mult p1 p2).

  (** Fraction addition is well-defined upto equality of fractions. *)

  (** It is easier to prove well-definedness as a function of both arguments at once. *)
  Definition frac_add_wd (f1 f1' f2 f2' : Fraction)
    (p : fraction_eq f1 f1') (q : fraction_eq f2 f2')
    : fraction_eq (frac_add f1 f2) (frac_add f1' f2').
  Proof.
    destruct f1 as [a s ss], f1' as [a' s' ss'],
      f2 as [b t st], f2' as [b' t' st'],
      p as [x [sx p]], q as [y [sy q]].
    refine (x * y ; (mss_mult sx sy, _)).
    simpl.
    rewrite 2 rng_dist_l, 2 rng_dist_r.
    snrapply (ap011 (+)). 
    - rewrite 4 rng_mult_assoc.
      rewrite 8 (rng_mult_permute_2_3 _ y).
      apply (ap (.* y)).
      rewrite 2 (rng_mult_permute_2_3 _ t).
      apply (ap (.* t)).
      rewrite (rng_mult_permute_2_3 _ t').
      f_ap.
    - do 2 lhs_V nrapply rng_mult_assoc.
      do 2 rhs_V nrapply rng_mult_assoc.
      f_ap.
      rewrite 6 rng_mult_assoc.
      rewrite 2 (rng_mult_permute_2_3 _ _ t').
      rewrite 2 (rng_mult_permute_2_3 _ _ t).
      lhs_V nrapply rng_mult_assoc.
      rhs_V nrapply rng_mult_assoc.
      f_ap; apply rng_mult_comm.
  Defined.

  Definition frac_add_wd_l (f1 f1' f2 : Fraction) (p : fraction_eq f1 f1')
    : fraction_eq (frac_add f1 f2) (frac_add f1' f2).
  Proof.
    pose (fraction_eq_refl f2).
    by apply frac_add_wd.
  Defined.

  Definition frac_add_wd_r (f1 f2 f2' : Fraction) (p : fraction_eq f2 f2')
    : fraction_eq (frac_add f1 f2) (frac_add f1 f2').
  Proof.
    pose (fraction_eq_refl f1).
    by apply frac_add_wd.
  Defined.

  (** The addition operation on the localization is induced from the addition operation for fractions. *)
  Instance plus_localization_type : Plus Localization_type.
  Proof.
    srapply Quotient_rec2.
    - rapply fraction_eq_refl.
    - cbn.
      intros f1 f2.
      exact (loc_frac (frac_add f1 f2)).
    - cbn beta.
      intros f1 f1' p f2 f2' q.
      by apply loc_frac_eq, frac_add_wd.
  Defined.

  (** *** Multiplication operation *)

  Definition frac_mult : Fraction -> Fraction -> Fraction :=
    fun '(Build_Fraction n1 d1 p1) '(Build_Fraction n2 d2 p2)
      => Build_Fraction (n1 * n2) (d1 * d2) (mss_mult p1 p2).

  Definition frac_mult_wd_l f1 f1' f2 (p : fraction_eq f1 f1')
    : fraction_eq (frac_mult f1 f2) (frac_mult f1' f2).
  Proof.
    destruct p as [x [s p]].
    refine (x; (s, _)); simpl.
    rewrite 4 rng_mult_assoc.
    rewrite (rng_mult_permute_2_3 _ _ (denominator f1')).
    rewrite (rng_mult_permute_2_3 _ _ (denominator f1)).
    lhs_V nrapply rng_mult_assoc.
    rhs_V nrapply rng_mult_assoc.
    f_ap.
  Defined.

  Definition frac_mult_wd_r f1 f2 f2' (p : fraction_eq f2 f2')
    : fraction_eq (frac_mult f1 f2) (frac_mult f1 f2').
  Proof.
    destruct p as [x [s p]].
    refine (x; (s, _)); simpl.
    rewrite 4 rng_mult_assoc.
    rewrite (rng_mult_permute_2_3 _ _ (numerator f2)).
    rewrite 2 (rng_mult_permute_2_3 _ _ (denominator f2')).
    rewrite (rng_mult_permute_2_3 _ _ (numerator f2')).
    rewrite 2 (rng_mult_permute_2_3 _ _ (denominator f2)).
    lhs_V nrapply rng_mult_assoc.
    rhs_V nrapply rng_mult_assoc.
    f_ap.
  Defined.

  Instance mult_localization_type : Mult Localization_type.
  Proof.
    srapply Quotient_rec2.
    - rapply fraction_eq_refl.
    - cbn.
      intros f1 f2.
      exact (loc_frac (frac_mult f1 f2)).
    - cbn beta.
      intros f1 f1' p f2 f2' q.
      transitivity (loc_frac (frac_mult f1' f2)).
      + by apply loc_frac_eq, frac_mult_wd_l.
      + by apply loc_frac_eq, frac_mult_wd_r.
  Defined.

  (** *** Zero element *)

  Instance zero_localization_type : Zero Localization_type
    := loc_frac (Build_Fraction 0 1 mss_one).

  (** *** One element *)

  Instance one_localization_type : One Localization_type
    := loc_frac (Build_Fraction 1 1 mss_one).

  (** *** Negation operation *)

  Definition frac_negate : Fraction -> Fraction
    :=  fun '(Build_Fraction n d p) => Build_Fraction (- n) d p.

  Definition frac_negate_wd f1 f2 (p : fraction_eq f1 f2)
    : fraction_eq (frac_negate f1) (frac_negate f2).
  Proof.
    destruct p as [x [s p]].
    refine (x; (s,_)); simpl.
    rewrite 2 rng_mult_negate_r, 2 rng_mult_negate_l.
    f_ap.
  Defined.

  Instance negate_localization_type : Negate Localization_type.
  Proof.
    srapply Localization_type_rec.
    - intros f.
      apply loc_frac.
      exact (frac_negate f).
    - intros f1 f2 p.
      by apply loc_frac_eq, frac_negate_wd.
  Defined.

  (** *** Ring laws *)
  
  (** Commutativity of addition *)
  Instance commutative_plus_localization_type
    : Commutative plus_localization_type.
  Proof.
    intros x; srapply Localization_type_ind_hprop; intros y; revert x.
    srapply Localization_type_ind_hprop; intros x.
    apply loc_frac_eq, fraction_eq_simple; simpl.
    rewrite (rng_mult_comm (denominator y) (denominator x)).
    f_ap; apply rng_plus_comm.
  Defined.

  (** Left additive identity *)
  Instance leftidentity_plus_localization_type
    : LeftIdentity plus_localization_type zero_localization_type.
  Proof.
    srapply Localization_type_ind_hprop; intros f.
    apply loc_frac_eq, fraction_eq_simple; simpl.
    f_ap.
    - rewrite rng_mult_zero_l.
      rewrite rng_plus_zero_l.
      apply rng_mult_one_r.
    - symmetry.
      apply rng_mult_one_l.
  Defined.

  Instance leftinverse_plus_localization_type
    : LeftInverse plus_localization_type negate_localization_type zero_localization_type.
  Proof.
    srapply Localization_type_ind_hprop; intros f.
    apply loc_frac_eq, fraction_eq_simple; simpl.
    refine (rng_mult_one_r _ @ _).
    refine (_ @ (rng_mult_zero_l _)^).
    rewrite rng_mult_negate_l.
    apply rng_plus_negate_l.
  Defined.

  Instance associative_plus_localization_type
    : Associative plus_localization_type.
  Proof.
    intros x y; srapply Localization_type_ind_hprop; intros z; revert y.
    srapply Localization_type_ind_hprop; intros y; revert x.
    srapply Localization_type_ind_hprop; intros x.
    apply loc_frac_eq, fraction_eq_simple.
    simpl.
    rewrite ? rng_dist_r.
    rewrite ? rng_mult_assoc.
    rewrite ? rng_plus_assoc.
    do 4 f_ap.
    all: rewrite <- ? rng_mult_assoc.
    all: f_ap.
    2: apply rng_mult_comm.
    rewrite rng_mult_assoc.
    apply rng_mult_comm.
  Defined.

  Instance leftidentity_mult_localization_type
    : LeftIdentity mult_localization_type one_localization_type.
  Proof.
    srapply Localization_type_ind_hprop; intros f.
    apply loc_frac_eq, fraction_eq_simple; simpl.
    f_ap; [|symmetry]; apply rng_mult_one_l.
  Defined.

  Instance associative_mult_localization_type
    : Associative mult_localization_type.
  Proof.
    intros x y; srapply Localization_type_ind_hprop; intros z; revert y.
    srapply Localization_type_ind_hprop; intros y; revert x.
    srapply Localization_type_ind_hprop; intros x.
    apply loc_frac_eq, fraction_eq_simple.
    f_ap; [|symmetry]; apply rng_mult_assoc.
  Defined.

  Instance commutative_mult_localization_type
    : Commutative mult_localization_type.
  Proof.
    intros x; srapply Localization_type_ind_hprop; intros y; revert x.
    srapply Localization_type_ind_hprop; intros x.
    apply loc_frac_eq, fraction_eq_simple; simpl.
    f_ap; rapply rng_mult_comm.
  Defined.

  Instance leftdistribute_localization_type
    : LeftDistribute mult_localization_type plus_localization_type.
  Proof.
    intros x y; srapply Localization_type_ind_hprop; intros z; revert y.
    srapply Localization_type_ind_hprop; intros y; revert x.
    srapply Localization_type_ind_hprop; intros x.
    apply loc_frac_eq, fraction_eq_simple.
    simpl.
    rewrite ? rng_dist_l, ? rng_dist_r.
    rewrite ? rng_mult_assoc.
    do 2 f_ap.
    all: rewrite <- ? rng_mult_assoc.
    all: do 2 f_ap.
    all: rewrite ? rng_mult_assoc.
    all: rewrite (rng_mult_comm (_ x)).
    all: rewrite <- ? rng_mult_assoc.
    all: f_ap.
    all: rewrite (rng_mult_comm _ (_ y)).
    all: rewrite <- ? rng_mult_assoc.
    all: f_ap.
  Defined.

  Definition rng_localization : CRing.
  Proof.
    snrapply Build_CRing'.
    1: rapply (Build_AbGroup' Localization_type).
    all: exact _.
  Defined.

  Definition loc_in : R $-> rng_localization.
  Proof.
    snrapply Build_RingHomomorphism.
    1: exact (loc_frac o frac_in).
    snrapply Build_IsSemiRingPreserving.
    - snrapply Build_IsMonoidPreserving.
      + intros x y.
        snrapply loc_frac_eq.
        apply fraction_eq_simple.
        by simpl; rewrite 5 rng_mult_one_r.
      + reflexivity.
    - snrapply Build_IsMonoidPreserving.
      + intros x y.
        snrapply loc_frac_eq.
        apply fraction_eq_simple.
        by simpl; rewrite 3 rng_mult_one_r.
      + reflexivity.
  Defined.
  
  Section Rec.

    Context (T : CRing) (f : R $-> T)
      (H : forall x, IsInvertible T (f x)).

    Definition rng_localization_rec_map : rng_localization -> T.
    Proof.
      srapply Localization_type_rec.
      - exact (fun x => f (numerator x) * inverse_elem (f (denominator x))).
      - simpl.
        intros x y z.
        apply rng_inv_moveR_rV.
        rhs_V nrapply rng_mult_move_left_assoc.
        rhs_V nrapply rng_mult_assoc.
        apply rng_inv_moveL_Vr.
        lhs_V nrapply rng_homo_mult.
        rhs_V nrapply rng_homo_mult.
        apply (equiv_ap (f z.1 *.)).
        lhs_V nrapply rng_homo_mult.
        rhs_V nrapply rng_homo_mult.
        lhs nrapply ap.
        1: lhs nrapply rng_mult_assoc.
        1: nrapply rng_mult_permute_2_3.
        rhs nrapply ap.
        2: nrapply rng_mult_assoc.
        exact (ap f (snd z.2)).
    Defined.

    Instance issemiringpreserving_rng_localization_rec_map
      : IsSemiRingPreserving rng_localization_rec_map.
    Proof.
      snrapply Build_IsSemiRingPreserving.
      - snrapply Build_IsMonoidPreserving.
        + intros x; rapply Localization_type_ind_hprop.
          intros y; revert x; rapply Localization_type_ind_hprop; intros x.
          simpl.
          apply rng_inv_moveR_rV.
          rhs nrapply rng_dist_r.
          rewrite rng_homo_plus.
          rewrite 3 rng_homo_mult.
          f_ap.
          1,2: rhs_V nrapply rng_mult_assoc.
          1,2: f_ap.
          1,2: lhs_V nrapply rng_mult_one_l.
          1,2: rhs nrapply rng_mult_assoc.
          2: rhs nrapply rng_mult_comm.
          2: rhs nrapply rng_mult_assoc.
          1,2: f_ap.
          1,2: symmetry.
          * apply rng_inv_l.
          * apply rng_inv_r. 
        + hnf; simpl; rewrite rng_homo_zero.
          nrapply rng_mult_zero_l.
      - snrapply Build_IsMonoidPreserving.
        + intros x; rapply Localization_type_ind_hprop.
          intros y; revert x; rapply Localization_type_ind_hprop; intros x.
          simpl.
          apply rng_inv_moveR_rV.
          lhs nrapply rng_homo_mult.
          rhs_V nrapply rng_mult_assoc.
          rhs_V nrapply rng_mult_assoc.
          apply ap.
          apply rng_inv_moveL_Vr.
          lhs nrapply rng_mult_comm.
          rhs_V nrapply rng_mult_assoc.
          apply ap.
          apply rng_inv_moveL_Vr.
          symmetry.
          rhs nrapply rng_mult_comm.
          nrapply rng_homo_mult.
        + apply rng_inv_moveR_rV; symmetry.
          apply rng_mult_one_l.
    Defined.

    Definition rng_localization_rec : rng_localization $-> T
      := Build_RingHomomorphism rng_localization_rec_map _.
    
    Definition rng_localization_rec_beta
      : rng_localization_rec $o loc_in $== f.
    Proof.
      intros x; simpl.   
      apply rng_inv_moveR_rV.
      lhs_V nrapply rng_mult_one_r.
      nrapply ap; symmetry.
      apply rng_homo_one.
    Defined.
  
  End Rec.
  
  (** Elements belonging to the multiplicative subset [S] of [R] become invertible in [rng_localization R S]. *)
  Global Instance isinvertible_rng_localization (x : R) (Sx : S x)
    : IsInvertible rng_localization (loc_in x).
  Proof.
    snrapply isinvertible_cring.
    - exact (loc_frac (Build_Fraction 1 x Sx)).
    - apply loc_frac_eq, fraction_eq_simple.
      exact (rng_mult_assoc _ _ _)^.
  Defined.
  
  (** As a special case, any denominator of a fraction must necessarily be invertible. *)
  Global Instance isinvertible_denominator (f : Fraction)
    : IsInvertible rng_localization (loc_in (denominator f)).
  Proof.
    snrapply isinvertible_rng_localization.
    exact (in_mult_subset_denominator f).
  Defined.
  
  (** We can factor any fraction as the multiplication of the numerator and the inverse of the denominator. *)
  Definition fraction_decompose (f : Fraction)
    : loc_frac f
      = loc_in (numerator f) * inverse_elem (loc_in (denominator f)).
  Proof.
    apply loc_frac_eq, fraction_eq_simple.
    nrapply rng_mult_assoc.
  Defined.

  Definition rng_localization_ind
    (P : rng_localization -> Type)
    (H : forall x, IsHProp (P x))
    (Hin : forall x, P (loc_in x))
    (Hinv : forall x (H : IsInvertible rng_localization x),
      P x -> P (inverse_elem x))
    (Hmul : forall x y, P x -> P y -> P (x * y))
    : forall x, P x.
  Proof.
    srapply Localization_type_ind.
    - intros f.
      refine (transport P (fraction_decompose f)^ _).
      apply Hmul.
      + apply Hin.
      + apply Hinv, Hin.
    - intros f1 f2 p.
      apply path_ishprop.
  Defined.
  
  Definition rng_localization_ind_homotopy {T : CRing}
    {f g : rng_localization $-> T}
    (p : f $o loc_in $== g $o loc_in)
    : f $== g.
  Proof.
    srapply rng_localization_ind.
    - exact p.
    - hnf; intros x H q.
      change (inverse_elem (f x) = inverse_elem (g x)).
      apply equiv_path_inverse_elem.
      exact q.
    - hnf; intros x y q r.
      lhs nrapply rng_homo_mult.
      rhs nrapply rng_homo_mult.
      f_ap.
  Defined.

End Localization.

(** TODO: Show construction is a localization. *)
