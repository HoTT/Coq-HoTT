From HoTT Require Import Basics.
Require Import Types.
Require Import HSet.
Require Import Spaces.Nat.Core Spaces.Nat.Factorial.
Require Import HFiber.
Require Import Factorization.
Require Import Truncations.
Require Import Colimits.Quotient.
Require Import Projective.
Require Import Fin.

Local Open Scope path_scope.
Local Open Scope nat_scope.

(** ** Definition of general finite sets *)

Class Finite (X : Type) :=
  { fcard : nat ;
    merely_equiv_fin : merely (X <~> Fin fcard) }.

Arguments fcard X {_}.
Arguments merely_equiv_fin X {_}.

Definition issig_finite X
: { n : nat & merely (X <~> Fin n) } <~> Finite X.
Proof.
  issig.
Defined.

(** Note that the sigma over cardinalities is not truncated.  Nevertheless, because canonical finite sets of different cardinalities are not isomorphic, being finite is still an hprop.  (Thus, we could have truncated the sigma and gotten an equivalent definition, but it would be less convenient to reason about.) *)
Instance ishprop_finite X
: IsHProp (Finite X).
Proof.
  refine (istrunc_equiv_istrunc _ (issig_finite X)).
  apply ishprop_sigma_disjoint; intros n m Hn Hm.
  strip_truncations.
  exact (nat_eq_fin_equiv n m (Hm oE Hn^-1)).
Defined.

(** ** Preservation of finiteness by equivalences *)

Definition finite_equiv X {Y} (e : X -> Y) `{IsEquiv X Y e}
: Finite X -> Finite Y.
Proof.
  intros ?.
  refine (Build_Finite Y (fcard X) _).
  assert (f := merely_equiv_fin X); strip_truncations.
  apply tr.
  exact (equiv_compose f e^-1).
Defined.

Definition finite_equiv' X {Y} (e : X <~> Y)
: Finite X -> Finite Y
  := finite_equiv X e.

Corollary finite_equiv_equiv X Y
: (X <~> Y) -> (Finite X <~> Finite Y).
Proof.
  intros ?; apply equiv_iff_hprop; apply finite_equiv';
    [ assumption | symmetry; assumption ].
Defined.

Definition fcard_equiv {X Y} (e : X -> Y) `{IsEquiv X Y e}
           `{Finite X} `{Finite Y}
: fcard X = fcard Y.
Proof.
  transitivity (@fcard Y (finite_equiv X e _)).
  - reflexivity.
  - exact (ap (@fcard Y) (path_ishprop _ _)).
Defined.

Definition fcard_equiv' {X Y} (e : X <~> Y)
           `{Finite X} `{Finite Y}
: fcard X = fcard Y
  := fcard_equiv e.

(** ** Simple examples of finite sets *)

(** Canonical finite sets are finite *)
Instance finite_fin n : Finite (Fin n)
  := Build_Finite _ n (tr (equiv_idmap _)).

(** This includes the empty set. *)
Instance finite_empty : Finite Empty
  := finite_fin 0.

(** The unit type is finite, since it's equivalent to [Fin 1]. *)
Instance finite_unit : Finite Unit.
Proof.
  refine (finite_equiv' (Fin 1) _ _); simpl.
  apply sum_empty_l.
Defined.

(** Thus, any contractible type is finite. *)
Instance finite_contr X `{Contr X} : Finite X
  := finite_equiv Unit equiv_contr_unit^-1 _.

(** Any decidable hprop is finite, since it must be equivalent to [Empty] or [Unit]. *)
Definition finite_decidable_hprop X `{IsHProp X} `{Decidable X}
: Finite X.
Proof.
  destruct (dec X) as [x|nx].
  - apply finite_contr.
    by apply contr_inhabited_hprop.
  - refine (finite_equiv Empty nx^-1 _).
Defined.

#[export]
Hint Immediate finite_decidable_hprop : typeclass_instances.

(** It follows that the propositional truncation of any finite set is finite. *)
Instance finite_merely X {fX : Finite X}
: Finite (merely X).
Proof.
  (** As in decidable_finite_hprop, we case on cardinality first to avoid needing funext. *)
  destruct fX as [[|n] e]; refine (finite_decidable_hprop _).
  - right.
    intros x; strip_truncations; exact (e x).
  - left.
    strip_truncations; exact (tr (e^-1 (inr tt))).
Defined.

(** Finite sets are closed under path-spaces. *)
Instance finite_paths {X} `{Finite X} (x y : X)
: Finite (x = y).
Proof.
  (** If we assume [Funext], then typeclass inference produces this automatically, since [X] has decidable equality and (hence) is a set, so [x=y] is a decidable hprop.  But we can also deduce it without funext, since [Finite] is an hprop even without funext. *)
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (finite_equiv _ (ap e)^-1 _).
  apply finite_decidable_hprop; exact _.
Defined.

(** Finite sets are also closed under successors. *)

Instance finite_succ X `{Finite X} : Finite (X + Unit).
Proof.
  refine (Build_Finite _ (fcard X).+1 _).
  pose proof (merely_equiv_fin X).
  strip_truncations; apply tr.
  refine (_ +E 1); assumption.
Defined.

Definition fcard_succ X `{Finite X}
: fcard (X + Unit) = (fcard X).+1
  := 1.

(** ** Decidability *)		

(** Like canonical finite sets, finite sets have decidable equality. *)
Instance decidablepaths_finite `{Funext} X `{Finite X}
: DecidablePaths X.
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  exact (decidablepaths_equiv _ e^-1 _).
Defined.

(** However, contrary to what you might expect, we cannot assert that "every finite set is decidable"!  That would be claiming a *uniform* way to select an element from every nonempty finite set, which contradicts univalence. *)

(** One thing we can prove is that any finite hprop is decidable. *)
Instance decidable_finite_hprop X `{IsHProp X} {fX : Finite X}
: Decidable X.
Proof.
  (** To avoid having to use [Funext], we case on the cardinality of [X] before stripping the truncation from its equivalence to [Fin n]; if we did things in the other order then we'd have to know that [Decidable X] is an hprop, which requires funext. *)
  destruct fX as [[|n] e].
  - right; intros x.
    strip_truncations; exact (e x).
  - left.
    strip_truncations; exact (e^-1 (inr tt)).
Defined.

(** It follows that if [X] is finite, then its propositional truncation is decidable. *)
Definition decidable_merely_finite X {fX : Finite X}
  : Decidable (merely X)
  := _.

(** From this, it follows that any finite set is *merely* decidable. *)
Definition merely_decidable_finite X `{Finite X}
: merely (Decidable X).
Proof.
  apply O_decidable; exact _.
Defined.

(** ** Induction over finite sets *)

(** Most concrete applications of this don't actually require univalence, but the general version does.  For this reason the general statement is less useful (and less used in the sequel) than it might be. *)
Definition finite_ind_hprop `{Univalence}
           (P : forall X, Finite X -> Type)
           `{forall X (fX:Finite X), IsHProp (P X _)}
           (f0 : P Empty _)
           (fs : forall X (fX:Finite X), P X _ -> P (X + Unit)%type _)
           (X : Type) `{Finite X}
: P X _.
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  assert (p := transportD Finite P (path_universe e^-1) _).
  refine (transport (P X) (path_ishprop _ _) (p _)).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - exact f0.
  - exact (transport (P (Fin n.+1)) (path_ishprop _ _) (fs _ _ IH)).
Defined.

(** ** The finite axiom of choice, and projectivity *)

Definition finite_choice {X} `{Finite X} : HasChoice X.
Proof.
  intros P oP f; clear oP.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  set (P' := P o e^-1).
  assert (f' := (fun x => f (e^-1 x)) : forall x, merely (P' x)).
  refine (Trunc_functor (X := forall x:Fin (fcard X), P' x) (-1) _ _).
  - intros g x; exact (eissect e x # g (e x)).
  - clearbody P'; clear f P e.
    generalize dependent (fcard X); intros n P f.
    induction n as [|n IH].
    + exact (tr (Empty_ind P)).
    + specialize (IH (P o inl) (f o inl)).
      assert (e := f (inr tt)).
      strip_truncations.
      exact (tr (sum_ind P IH (Unit_ind e))).
Defined.

Corollary isprojective_fin_n (n : nat) : IsProjective (Fin n).
Proof.
  apply (iff_isoprojective_hasochoice _ (Fin n)).
  exact finite_choice.
Defined.

(** ** Constructions on finite sets *)

(** Finite sets are closed under sums, products, function spaces, and equivalence spaces.  There are multiple choices we could make regarding how to prove these facts.  Since we know what the cardinalities ought to be in all cases (since we know how to add, multiply, exponentiate, and take factorials of natural numbers), we could specify those off the bat, and then reduce to the case of canonical finite sets.  However, it's more amusing to instead prove finiteness of these constructions by "finite-set induction", and then *deduce* that their cardinalities are given by the corresponding operations on natural numbers (because they satisfy the same recurrences). *)

(** *** Binary sums *)

Instance finite_sum X Y `{Finite X} `{Finite Y}
: Finite (X + Y).
Proof.
  assert (e := merely_equiv_fin Y).
  strip_truncations.
  refine (finite_equiv _ (functor_sum idmap e^-1) _).
  generalize (fcard Y); intros n.
  induction n as [|n IH].
  - exact (finite_equiv _ (sum_empty_r X)^-1 _).
  - exact (finite_equiv _ (equiv_sum_assoc X _ Unit) _).
Defined.

(** Note that the cardinality function [fcard] actually computes.  The same will be true of all the other proofs in this section, though we don't always verify it. *)
Goal fcard (Fin 3 + Fin 4) = 7.
  reflexivity.
Abort.

Definition fcard_sum X Y `{Finite X} `{Finite Y}
: fcard (X + Y) = (fcard X + fcard Y).
Proof.
  refine (_ @ nat_add_comm _ _).
  assert (e := merely_equiv_fin Y).
  strip_truncations.
  refine (fcard_equiv' (1 +E e) @ _).
  refine (_ @ ap (fun y => (y + fcard X)) (fcard_equiv e^-1)).
  generalize (fcard Y); intros n.
  induction n as [|n IH].
  - exact (fcard_equiv (sum_empty_r X)^-1).
  - refine (fcard_equiv (equiv_sum_assoc _ _ _)^-1 @ _).
    exact (ap S IH).
Defined.

(** *** Binary products *)

Instance finite_prod X Y `{Finite X} `{Finite Y}
: Finite (X * Y).
Proof.
  assert (e := merely_equiv_fin Y).
  strip_truncations.
  refine (finite_equiv _ (functor_prod idmap e^-1) _).
  generalize (fcard Y); intros n.
  induction n as [|n IH].
  - refine (finite_equiv _ (prod_empty_r X)^-1 _).
  - refine (finite_equiv _ (sum_distrib_l X _ Unit)^-1 (finite_sum _ _)).
    refine (finite_equiv _ (prod_unit_r X)^-1 _).
Defined.

Definition fcard_prod X Y `{Finite X} `{Finite Y}
: fcard (X * Y) = fcard X * fcard Y.
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (fcard_equiv' (e *E 1) @ _).
  refine (_ @ ap (fun x => x * fcard Y) (fcard_equiv e^-1)).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - refine (fcard_equiv (prod_empty_l Y)).
  - refine (fcard_equiv (sum_distrib_r Y (Fin n) Unit) @ _).
    refine (fcard_sum _ _ @ _).
    simpl.
    refine (_ @ nat_add_comm _ _).
    refine (ap011 nat_add _ _).
    + exact IH.
    + apply fcard_equiv', prod_unit_l.
  Defined.

(** *** Function types *)

(** Finite sets are closed under function types, and even dependent function types. *)

Instance finite_forall `{Funext} {X} (Y : X -> Type)
       `{Finite X} `{forall x, Finite (Y x)}
: Finite (forall x:X, Y x).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  simple refine (finite_equiv' _
            (equiv_functor_forall' (P := fun x => Y (e^-1 x)) e _) _); try exact _.
  { intros x; refine (equiv_transport _ (eissect e x)). }
  set (Y' := Y o e^-1); change (Finite (forall x, Y' x)).
  assert (forall x, Finite (Y' x)) by exact _; clearbody Y'; clear e.
  generalize dependent (fcard X); intros n Y' ?.
  induction n as [|n IH].
  - exact _.
  - refine (finite_equiv _ (equiv_sum_ind Y') _).
    apply finite_prod.
    + apply IH; exact _.
    + refine (finite_equiv _ (@Unit_ind (fun u => Y' (inr u))) _).
      refine (isequiv_unit_ind (Y' o inr)).
Defined.

#[local] Hint Extern 4 => progress (cbv beta iota) : typeclass_instances.

Definition fcard_arrow `{Funext} X Y `{Finite X} `{Finite Y}
: fcard (X -> Y) = nat_pow (fcard Y) (fcard X).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (fcard_equiv (functor_arrow e idmap)^-1 @ _).
  refine (_ @ ap (fun x => nat_pow (fcard Y) x) (fcard_equiv e)).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - reflexivity.
  - refine (fcard_equiv (equiv_sum_ind (fun (_:Fin n.+1) => Y))^-1 @ _).
    refine (fcard_prod _ _ @ _).
    lhs napply nat_mul_comm.
    apply (ap011 nat_mul).
    + refine (fcard_equiv (@Unit_ind (fun (_:Unit) => Y))^-1).
    + assumption.
Defined.

(** [fcard] still computes, despite the funext: *)
Goal forall fs:Funext, fcard (Fin 3 -> Fin 4) = 64.
  reflexivity.
Abort.

(** *** Automorphism types (i.e. symmetric groups) *)

Instance finite_aut `{Funext} X `{Finite X}
: Finite (X <~> X).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (finite_equiv _
            (equiv_functor_equiv e^-1 e^-1) _).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - exact _.
  - refine (finite_equiv _ (equiv_fin_equiv n n) _).
Defined.

Definition fcard_aut `{Funext} X `{Finite X}
: fcard (X <~> X) = factorial (fcard X).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (fcard_equiv
            (equiv_functor_equiv e^-1 e^-1)^-1 @ _).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - reflexivity.
  - refine (fcard_equiv (equiv_fin_equiv n n)^-1 @ _).
    refine (fcard_prod _ _ @ _).
    apply ap011.
    + reflexivity.
    + assumption.
Defined.

(** [fcard] still computes: *)
Goal forall fs:Funext, fcard (Fin 4 <~> Fin 4) = 24.
  reflexivity.
Abort.

(** ** Finite sums of natural numbers *)

(** Perhaps slightly less obviously, finite sets are also closed under sigmas. *)

Instance finite_sigma {X} (Y : X -> Type)
       `{Finite X} `{forall x, Finite (Y x)}
: Finite { x:X & Y x }.
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (finite_equiv' _
            (equiv_functor_sigma (equiv_inverse e)
                                 (fun x (y:Y (e^-1 x)) => y)) _).
  (** Unfortunately, because [compose] is currently beta-expanded, [set (Y' := Y o e^-1)] doesn't change the goal. *)
  set (Y' := fun x => Y (e^-1 x)).
  assert (forall x, Finite (Y' x)) by exact _; clearbody Y'; clear e.
  generalize dependent (fcard X); intros n Y' ?.
  induction n as [|n IH].
  - exact (finite_equiv Empty pr1^-1 _).
  - refine (finite_equiv _ (equiv_sigma_sum (Fin n) Unit Y')^-1 _).
    apply finite_sum.
    + apply IH; exact _.
    + exact (finite_equiv _ (equiv_contr_sigma _)^-1 _).
Defined.

(** Amusingly, this automatically gives us a way to add up a family of natural numbers indexed by any finite set.  (We could of course also define such an operation directly, probably using [merely_ind_hset].) *)

Definition finadd {X} `{Finite X} (f : X -> nat) : nat
  := fcard { x:X & Fin (f x) }.

Definition fcard_sigma {X} (Y : X -> Type)
       `{Finite X} `{forall x, Finite (Y x)}
: fcard { x:X & Y x } = finadd (fun x => fcard (Y x)).
Proof.
  set (f := fun x => fcard (Y x)).
  set (g := fun x => merely_equiv_fin (Y x) : merely (Y x <~> Fin (f x))).
  apply finite_choice in g; [| exact _].
  strip_truncations.
  unfold finadd.
  exact (fcard_equiv' (equiv_functor_sigma_id g)).
Defined.

(** The sum of a finite constant family is the product by its cardinality. *)
Definition finadd_const X `{Finite X} n
: finadd (fun x:X => n) = fcard X * n.
Proof.
  transitivity (fcard (X * Fin n)).
  - exact (fcard_equiv' (equiv_sigma_prod0 X (Fin n))).
  - exact (fcard_prod X (Fin n)).
Defined.

(** Closure under sigmas and paths also implies closure under hfibers. *)
Definition finite_hfiber {X Y} (f : X -> Y) (y : Y)
       `{Finite X} `{Finite Y}
: Finite (hfiber f y).
Proof.
  exact _.
Defined.

(** Therefore, the cardinality of the domain of a map between finite sets is the sum of the cardinalities of its hfibers. *)
Definition fcard_domain {X Y} (f : X -> Y) `{Finite X} `{Finite Y}
: fcard X = finadd (fun y => fcard (hfiber f y)).
Proof.
  refine (_ @ fcard_sigma (hfiber f)).
  exact (fcard_equiv' (equiv_fibration_replacement f)).
Defined.

(** In particular, the image of a map between finite sets is finite. *)
Definition finite_image
       {X Y} `{Finite X} `{Finite Y} (f : X -> Y)
: Finite (himage f).
Proof.
  exact _.
Defined.

(** ** Finite products of natural numbers *)

(** Similarly, closure of finite sets under [forall] automatically gives us a way to multiply a family of natural numbers indexed by any finite set.  Of course, if we defined this explicitly, it wouldn't need funext. *)

Definition finmult `{Funext} {X} `{Finite X} (f : X -> nat) : nat
  := fcard (forall x:X, Fin (f x)).

Definition fcard_forall `{Funext} {X} (Y : X -> Type)
       `{Finite X} `{forall x, Finite (Y x)}
: fcard (forall x:X, Y x) = finmult (fun x => fcard (Y x)).
Proof.
  set (f := fun x => fcard (Y x)).
  set (g := fun x => merely_equiv_fin (Y x) : merely (Y x <~> Fin (f x))).
  apply finite_choice in g; [| exact _].
  strip_truncations.
  unfold finmult.
  exact (fcard_equiv' (equiv_functor_forall' (equiv_idmap X) g)).
Defined.

(** The product of a finite constant family is the exponential by its cardinality. *)
Definition finmult_const `{Funext} X `{Finite X} n
: finmult (fun x:X => n) = nat_pow n (fcard X).
Proof.
  exact (fcard_arrow X (Fin n)).
Defined.


(** ** Finite subsets *)

(** Closure under sigmas implies that a detachable subset of a finite set is finite. *)
Instance finite_detachable_subset {X} `{Finite X} (P : X -> Type)
       `{forall x, IsHProp (P x)} `{forall x, Decidable (P x)}
: Finite { x:X & P x }.
Proof.
  exact _.
Defined.

(** Conversely, if a subset of a finite set is finite, then it is detachable.  We show first that an embedding between finite subsets has detachable image. *)
Definition detachable_image_finite
           {X Y} `{Finite X} `{Finite Y} (f : X -> Y) `{IsEmbedding f}
: forall y, Decidable (hfiber f y).
Proof.
  intros y.
  assert (ff : Finite (hfiber f y)) by exact _.
  destruct ff as [[|n] e].
  - right; intros u; strip_truncations; exact (e u).
  - left; strip_truncations; exact (e^-1 (inr tt)).
Defined.

Definition detachable_finite_subset {X} `{Finite X}
           (P : X -> Type) `{forall x, IsHProp (P x)}
           {Pf : Finite ({ x:X & P x })}
: forall x, Decidable (P x).
Proof.
  intros x.
  nrefine (decidable_equiv' _ (hfiber_fibration x P)^-1%equiv _).
  nrefine (detachable_image_finite pr1 x).
  1,2: exact _.
  exact (mapinO_pr1 (Tr (-1))).  (** Why doesn't Coq find this? *)
Defined.

(** ** Quotients *)

(** The quotient of a finite set by a detachable equivalence relation is finite. *)

Section DecidableQuotients.
  Context `{Univalence} {X} `{Finite X}
          (R : Relation X) `{is_mere_relation X R}
          `{Reflexive _ R} `{Transitive _ R} `{Symmetric _ R}
          {Rd : forall x y, Decidable (R x y)}.

  #[export] Instance finite_quotient : Finite (Quotient R).
  Proof.
    assert (e := merely_equiv_fin X).
    strip_truncations.
    pose (R' x y := R (e^-1 x) (e^-1 y)).
    assert (is_mere_relation _ R') by exact _.
    assert (Reflexive R') by (intros ?; unfold R'; apply reflexivity).
    assert (Symmetric R') by (intros ? ?; unfold R'; apply symmetry).
    assert (Transitive R') by (intros ? ? ?; unfold R'; exact transitivity).
    assert (R'd : forall x y, Decidable (R' x y))
      by (intros ? ?; unfold R'; apply Rd).
    srefine (finite_equiv' _ (equiv_quotient_functor R' R e^-1 _) _).
    1: by try (intros; split).
    clearbody R'; clear e.
    generalize dependent (fcard X);
      intros n; induction n as [|n IH]; intros R' ? ? ? ? ?.
    - refine (finite_equiv Empty _^-1 _).
      exact (Quotient_rec R' _ Empty_rec (fun x _ _ => match x with end)).
    - pose (R'' x y := R' (inl x) (inl y)).
      assert (is_mere_relation _ R'') by exact _.
      assert (Reflexive R'') by (intros ?; unfold R''; apply reflexivity).
      assert (Symmetric R'') by (intros ? ?; unfold R''; apply symmetry).
      assert (Transitive R'') by (intros ? ? ?; unfold R''; exact transitivity).
      assert (forall x y, Decidable (R'' x y)) by (intros ? ?; unfold R''; apply R'd).
      assert (inlresp := (fun x y => idmap)
                         : forall x y, R'' x y -> R' (inl x) (inl y)).
      destruct (dec (merely {x:Fin n & R' (inl x) (inr tt)})) as [p|np].
      { strip_truncations.
        destruct p as [x r].
        refine (finite_equiv' (Quotient R'') _ _).
        refine (Build_Equiv _ _ (Quotient_functor R'' R' inl inlresp) _).
        apply isequiv_surj_emb.
        - apply BuildIsSurjection.
          refine (Quotient_ind_hprop R' _ _).
          intros [y|[]]; apply tr.
          + exists (class_of R'' y); reflexivity.
          + exists (class_of R'' x); simpl.
            apply qglue, r.
        - apply isembedding_isinj_hset; intros u.
          refine (Quotient_ind_hprop R'' _ _); intros v.
          revert u; refine (Quotient_ind_hprop R'' _ _); intros u.
          simpl; intros q.
          apply qglue; unfold R''.
          exact (related_quotient_paths R' (inl u) (inl v) q). }
      { refine (finite_equiv' (Quotient R'' + Unit) _ _).
        refine (Build_Equiv _ _ (sum_ind (fun _ => Quotient R')
                                        (Quotient_functor R'' R' inl inlresp)
                                        (fun _ => class_of R' (inr tt))) _).
        apply isequiv_surj_emb.
        - apply BuildIsSurjection.
          refine (Quotient_ind_hprop R' _ _).
          intros [y|[]]; apply tr.
          + exists (inl (class_of R'' y)); reflexivity.
          + exists (inr tt); reflexivity.
        - apply isembedding_isinj_hset; intros u.
          refine (sum_ind _ _ _).
          + refine (Quotient_ind_hprop R'' _ _); intros v.
            revert u; refine (sum_ind _ _ _).
            * refine (Quotient_ind_hprop R'' _ _); intros u.
              simpl; intros q.
              apply ap, qglue; unfold R''.
              exact (related_quotient_paths R' (inl u) (inl v) q).
            * intros []; simpl.
              intros q.
              apply related_quotient_paths in q; try exact _.
              apply symmetry in q.
              elim (np (tr (v ; q))).
          + intros []; simpl.
            destruct u as [u|[]]; simpl.
            * revert u; refine (Quotient_ind_hprop R'' _ _); intros u; simpl.
              intros q.
              apply related_quotient_paths in q; try exact _.
              elim (np (tr (u;q))).
            * intros; reflexivity. }
  Defined.

  (** Therefore, the cardinality of [X] is the sum of the cardinalities of its equivalence classes. *)
  Definition fcard_quotient
  : fcard X = finadd (fun z:Quotient R => fcard {x:X & in_class R z x}).
  Proof.
    refine (fcard_domain (class_of R) @ _).
    apply ap, path_arrow; intros z; revert z.
    refine (Quotient_ind_hprop _ _ _); intros x; simpl.
    apply fcard_equiv'; unfold hfiber.
    refine (equiv_functor_sigma_id _); intros y; simpl.
    symmetry.
    refine (path_quotient R y x oE _).
    apply equiv_iff_hprop; apply symmetry.
  Defined.

End DecidableQuotients.

(** ** Injections *)

(** An injection between finite sets induces an inequality between their cardinalities. *)
Definition leq_inj_finite {X Y} {fX : Finite X} {fY : Finite Y}
           (f : X -> Y) (i : IsEmbedding f)
: fcard X <= fcard Y.
Proof.
  assert (MapIn (Tr (-1)) f) by exact _. clear i.
  destruct fX as [n e]; simpl.
  destruct fY as [m e']; simpl.
  strip_truncations.
  pose (g := e' o f o e^-1).
  assert (MapIn (Tr (-1)) g) by (unfold g; exact _).
  clearbody g. clear e e'. generalize dependent m.
  induction n as [|n IHn].
  1: exact _.
  intros m g ?.
  assert (i : IsInjective g) by (apply isinj_embedding; exact _).
  destruct m as [|m].
  { elim (g (inr tt)). }
  pose (h := (fin_transpose_last_with m (g (inr tt)))^-1 o g).
  assert (MapIn (Tr (-1)) h) by (unfold h; exact _).
  assert (Ha : forall a:Fin n, is_inl (h (inl a))).
  { intros a.
    remember (g (inl a)) as b eqn:p.
    destruct b as [b|[]].
    - assert (q : g (inl a) <> (g (inr tt))).
      { intros r. exact (inl_ne_inr _ _ (i _ _ r)). }
      rewrite p in q; apply symmetric_neq in q.
      assert (r : h (inl a) = inl b).
      { unfold h; apply moveR_equiv_V; symmetry.
        exact (fin_transpose_last_with_rest m (g (inr tt)) b q @ p^). }
      rewrite r; exact tt.
    - assert (q : h (inl a) = g (inr tt)).
      { unfold h; apply moveR_equiv_V; symmetry.
        refine (_ @ p^); apply fin_transpose_last_with_with. }
      rewrite q.
      destruct (is_inl_or_is_inr (g (inr tt))) as [l|r]; try assumption.
      assert (s := inr_un_inr _ r).
      revert s; generalize (un_inr (g (inr tt)) r); intros [] s.
      elim (inl_ne_inr _ _ (i _ _ (p @ s))). }
  assert (Hb : forall b:Unit, is_inr (h (inr b))).
  { intros [].
    assert (q : h (inr tt) = inr tt).
    { unfold h; apply moveR_equiv_V; symmetry.
      apply fin_transpose_last_with_last. }
    rewrite q; exact tt. }
  apply leq_succ.
  exact (IHn m (unfunctor_sum_l h Ha)
             (mapinO_unfunctor_sum_l (Tr (-1)) h Ha Hb)).
Qed.

(** ** Surjections  *)
(** A surjection between finite sets induces an inequality between their cardinalities. *)
Definition geq_surj_finite  {X Y} {fX : Finite X} {fY : Finite Y}
           (f : X -> Y) (i : IsSurjection f)
  : fcard X >= fcard Y.
Proof.
  destruct fX as [n e], fY as [m e']; simpl.
  assert (k := isprojective_fin_n m).
  strip_truncations.
  pose (g := e' o f o e^-1).
  assert (k' : IsSurjection g) by exact _ .
  clearbody g; clear i f.
  assert (j := k (Fin n) _ (Fin m) _ idmap g k').
  strip_truncations.
  simpl; destruct j as [s is_section]. 
  change n with (fcard (Fin n)).
  change m with (fcard (Fin m)).
  apply (leq_inj_finite s).
  apply isembedding_isinj_hset, (isinj_section is_section).
Defined.
  
  (** ** Enumerations *)

(** A function from [nat] to a finite set must repeat itself eventually. *)
Section Enumeration.
  Context `{Funext} {X} `{Finite@{_ Set _} X} (e : nat -> X).

  Let er (n : nat) : Fin n -> X
    := fun k => e (nat_fin n k).

  Lemma finite_enumeration_stage (n : nat)
  : IsEmbedding (er n)
    + { n : nat & { k : nat & e n = e (n + k).+1 }}.
  Proof.
    induction n as [|n [IH|IH]].
    - left. intros x.
      apply hprop_inhabited_contr; intros [[] _].
    - destruct (detachable_image_finite (er n) (er n.+1 (inr tt)))
        as [[k p]|ne].
      + right.
        exists (nat_fin n k).
        exists (nat_fin_compl n k).
        rewrite nat_fin_compl_compl.
        exact p.
      + left. intros x.
        apply hprop_allpath.
        intros k l.
        apply path_sigma_hprop.
        destruct k as [[k|[]] p], l as [[l|[]] q]; simpl.
        * apply isinj_embedding in IH.
          apply ap.
          apply IH.
          unfold er in p, q. simpl in p, q.
          exact (p @ q^).
        * refine (Empty_rec (ne _)).
          exists k.
          exact (p @ q^).
        * refine (Empty_rec (ne _)).
          exists l.
          exact (q @ p^).
        * reflexivity.
    - right; exact IH.
  Defined.

  Definition finite_enumeration_repeats
  : { n : nat & { k : nat & e n = e (n + k).+1 }}.
  Proof.
    destruct (finite_enumeration_stage (fcard X).+1) as [p|?].
    - assert (q := leq_inj_finite (er (fcard X).+1) p); simpl in q.
      elim (lt_irrefl _ q).
    - assumption.
  Defined.

End Enumeration.
