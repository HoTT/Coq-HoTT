Require Import Basics.
Require Import Types.
Require Import HSet.
Require Import DProp.
Require Import Spaces.Nat.
Require Import Truncations.
Require Import Fibrations.
Require Import Factorization.
Import TrM.

Require Import Spaces.Finite.Core.
Require Import Spaces.Finite.Equiv.

Local Open Scope path_scope.
Local Open Scope nat_scope.

(** ** Definition of general finite sets *)

Class IsFinite (X : Type) := {
  fcard : nat ;
  merely_equiv_fin : merely (X <~> Fin fcard) ;
}.

Arguments fcard X {_}.
Arguments merely_equiv_fin X {_}.

(** [IsFinite] is equivalent to a sigma type *)
Definition issig_isfinite (X : Type)
  : { n : nat & merely (X <~> Fin n) } <~> IsFinite X
  := ltac:(issig).

(** Note that the sigma over cardinalities is not truncated.  Nevertheless, because canonical finite sets of different cardinalities are not isomorphic, being finite is still an hprop.  (Thus, we could have truncated the sigma and gotten an equivalent definition, but it would be less convenient to reason about.) *)
Global Instance ishprop_isfinite (X : Type)
  : IsHProp (IsFinite X).
Proof.
  refine (trunc_equiv' _ (issig_isfinite X)).
  apply ishprop_sigma_disjoint; intros n m Hn Hm.
  strip_truncations.
  refine (nat_eq_fin_equiv n m (Hm oE Hn^-1)).
Defined.

(** ** Preservation of finiteness by equivalences *)

(** If a map is an equivalence, then the domain is finite if the codomain is. *)
Definition isfinite_isequiv (X : Type) {Y : Type} (e : X -> Y) `{!IsEquiv e}
  : IsFinite X -> IsFinite Y.
Proof.
  intros ?.
  refine (Build_IsFinite Y (fcard X) _).
  assert (f := merely_equiv_fin X); strip_truncations.
  apply tr.
  exact (equiv_compose f e^-1).
Defined.

(** The domain of an equivalence is finite if the codomain is. *)
Definition isfinite_equiv (X : Type) {Y : Type} (e : X <~> Y)
  : IsFinite X -> IsFinite Y
  := isfinite_isequiv X e.

(** If two types are equivalent then so are their proofs of [IsFinite] *)
Corollary isfinite_equiv_equiv (X Y : Type)
  : (X <~> Y) -> (IsFinite X <~> IsFinite Y).
Proof.
  intros ?; apply equiv_iff_hprop; apply isfinite_equiv;
    [ assumption | symmetry; assumption ].
Defined.

(** An map between finite types that is an equivalence, induces equality between their cardinalities. *)
Definition fcard_isequiv {X Y : Type} (e : X -> Y) `{!IsEquiv e}
  `{IsFinite X} `{IsFinite Y}
  : fcard X = fcard Y.
Proof.
  transitivity (@fcard Y (isfinite_isequiv X e _)).
  - reflexivity.
  - exact (ap (@fcard Y) (path_ishprop _ _)).
Defined.

(** Equivalent finite types have equal cardinalities. *)
Definition fcard_equiv {X Y : Type} (e : X <~> Y) `{IsFinite X} `{IsFinite Y}
  : fcard X = fcard Y
  := fcard_isequiv e.

(** ** Simple examples of finite sets *)

(** Canonical finite sets are finite *)
Global Instance isfinite_fin (n : nat) : IsFinite (Fin n)
  := Build_IsFinite _ n (tr (equiv_idmap _)).

(** This includes the empty set. *)
Global Instance isfinite_empty : IsFinite Empty
  := isfinite_fin 0.

(** The unit type is finite, since it's equivalent to [Fin 1]. *)
Global Instance isfinite_unit : IsFinite Unit.
Proof.
  refine (isfinite_equiv (Fin 1) _ _); simpl.
  apply sum_empty_l.
Defined.

(** Thus, any contractible type is finite. *)
Global Instance isfinite_contr (X : Type) `{Contr X} : IsFinite X
  := isfinite_equiv Unit equiv_contr_unit^-1 _.

(** Any decidable hprop is finite, since it must be equivalent to [Empty] or [Unit]. *)
Definition isfinite_decidable_hprop (X : Type) `{IsHProp X} `{Decidable X}
  : IsFinite X.
Proof.
  destruct (dec X) as [x|nx].
  - assert (Contr X) by exact (contr_inhabited_hprop X x).
    exact _.
  - refine (isfinite_isequiv Empty nx^-1 _).
Defined.

Hint Immediate isfinite_decidable_hprop : typeclass_instances.

(** It follows that the propositional truncation of any finite set is finite. *)
Global Instance isfinite_merely (X : Type) {fX : IsFinite X}
  : IsFinite (merely X).
Proof.
  (** As in decidable_isfinite_hprop, we case on cardinality first to avoid needing funext. *)
  destruct fX as [[|n] e]; refine (isfinite_decidable_hprop _).
  - right.
    intros x; strip_truncations; exact (e x).
  - left.
    strip_truncations; exact (tr (e^-1 (inr tt))).
Defined.

(** Finite sets are closed under path-spaces. *)
Global Instance isfinite_paths {X : Type} `{IsFinite X} (x y : X)
  : IsFinite (x = y).
Proof.
  (** If we assume [Funext], then typeclass inference produces this automatically, since [X] has decidable equality and (hence) is a set, so [x=y] is a decidable hprop.  But we can also deduce it without funext, since [IsFinite] is an hprop even without funext. *)
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (isfinite_isequiv _ (ap e)^-1 _).
  apply isfinite_decidable_hprop; exact _.
Defined.

(** Finite sets are also closed under successors. *)
Global Instance isfinite_succ (X : Type) `{IsFinite X} : IsFinite (X + Unit).
Proof.
  refine (Build_IsFinite _ (fcard X).+1 _).
  pose proof (merely_equiv_fin X).
  strip_truncations; apply tr.
  refine (_ +E 1); assumption.
Defined.

(** The cardinality of the sucessor is the sucessor of the cardinality. *)
Definition fcard_succ (X : Type) `{IsFinite X}
  : fcard (X + Unit) = (fcard X).+1 := 1.

(** ** Decidability *)

(** Like canonical isfinite sets, isfinite sets have decidable equality. *)
Global Instance decidablepaths_isfinite `{Funext} (X : Type) `{IsFinite X}
  : DecidablePaths X.
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (decidablepaths_equiv _ e^-1 _).
Defined.

(** However, contrary to what you might expect, we cannot assert that "every finite set is decidable"!  That would be claiming a *uniform* way to select an element from every nonempty finite set, which contradicts univalence. *)

(** One thing we can prove is that any finite hprop is decidable. *)
Global Instance decidable_isfinite_hprop (X : Type)
  `{IsHProp X} {fX : IsFinite X}
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
Global Instance decidable_merely_isfinite (X : Type) {fX : IsFinite X}
  : Decidable (merely X) := _.

(** From this, it follows that any finite set is *merely* decidable. *)
Definition merely_decidable_isfinite X `{IsFinite X} : merely (Decidable X).
Proof.
  apply O_decidable; exact _.
Defined.

(** ** Induction over finite sets *)

(** Most concrete applications of this don't actually require univalence, but the general version does.  For this reason the general statement is less useful (and less used in the sequel) than it might be. *)
Definition isfinite_ind_hprop `{Univalence}
  (P : forall X, IsFinite X -> Type)
  `{forall X (fX:IsFinite X), IsHProp (P X _)}
  (f0 : P Empty _)
  (fs : forall X (fX:IsFinite X), P X _ -> P (X + Unit)%type _)
  (X : Type) `{IsFinite X}
  : P X _.
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  assert (p := transportD IsFinite P (path_universe e^-1) _).
  refine (transport (P X) (path_ishprop _ _) (p _)).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - exact f0.
  - refine (transport (P (Fin n.+1)) (path_ishprop _ _) (fs _ _ IH)).
Defined.

(** ** The finite axiom of choice *)

Definition finite_choice {X : Type} `{IsFinite X} (P : X -> Type)
  : (forall x, merely (P x)) -> merely (forall x, P x).
Proof.
  intros f.
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

(** ** Constructions on finite sets *)

(** Finite sets are closed under sums, products, function spaces, and equivalence spaces.  There are multiple choices we could make regarding how to prove these facts.  Since we know what the cardinalities ought to be in all cases (since we know how to add, multiply, exponentiate, and take factorials of natural numbers), we could specify those off the bat, and then reduce to the case of canonical finite sets.  However, it's more amusing to instead prove finiteness of these constructions by "finite-set induction", and then *deduce* that their cardinalities are given by the corresponding operations on natural numbers (because they satisfy the same recurrences). *)

(** *** Binary sums *)

Global Instance isfinite_sum (X Y : Type) `{IsFinite X} `{IsFinite Y}
  : IsFinite (X + Y).
Proof.
  assert (e := merely_equiv_fin Y).
  strip_truncations.
  refine (isfinite_isequiv _ (functor_sum idmap e^-1) _).
  generalize (fcard Y); intros n.
  induction n as [|n IH].
  - refine (isfinite_equiv _ (sum_empty_r X)^-1 _).
  - refine (isfinite_equiv _ (equiv_sum_assoc X _ Unit) _).
Defined.

(** Note that the cardinality function [fcard] actually computes.  The same will be true of all the other proofs in this section, though we don't always verify it. *)
Goal fcard (Fin 3 + Fin 4) = 7.
  reflexivity.
Abort.

(** The cardinality of a sum is the sum of the cardinalities. *)
Definition fcard_sum (X Y : Type) `{IsFinite X} `{IsFinite Y}
  : fcard (X + Y) = (fcard X + fcard Y).
Proof.
  refine (_ @ nat_plus_comm _ _).
  assert (e := merely_equiv_fin Y).
  strip_truncations.
  refine (fcard_equiv (1 +E e) @ _).
  refine (_ @ ap (fun y => (y + fcard X)) (fcard_equiv e^-1)).
  generalize (fcard Y); intros n.
  induction n as [|n IH].
  - refine (fcard_equiv (sum_empty_r X)^-1).
  - refine (fcard_equiv (equiv_sum_assoc _ _ _)^-1 @ _).
    exact (ap S IH).
Defined.

(** *** Binary products *)

Global Instance isfinite_prod (X Y : Type) `{IsFinite X} `{IsFinite Y}
  : IsFinite (X * Y).
Proof.
  assert (e := merely_equiv_fin Y).
  strip_truncations.
  refine (isfinite_isequiv _ (functor_prod idmap e^-1) _).
  generalize (fcard Y); intros n.
  induction n as [|n IH].
  - refine (isfinite_equiv _ (prod_empty_r X)^-1 _).
  - refine (isfinite_equiv _ (sum_distrib_l X _ Unit)^-1 (isfinite_sum _ _)).
    refine (isfinite_equiv _ (prod_unit_r X)^-1 _).
Defined.

(** The cardinality of a product is the product of cardinalities. *)
Definition fcard_prod (X Y : Type) `{IsFinite X} `{IsFinite Y}
  : fcard (X * Y) = fcard X * fcard Y.
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (fcard_equiv (e *E 1) @ _).
  refine (_ @ ap (fun x => x * fcard Y) (fcard_equiv e^-1)).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - refine (fcard_equiv (prod_empty_l Y)).
  - refine (fcard_equiv (sum_distrib_r Y (Fin n) Unit) @ _).
    refine (fcard_sum _ _ @ _).
    simpl.
    refine (_ @ nat_plus_comm _ _).
    refine (ap011 plus _ _).
    + apply IH.
    + apply fcard_equiv, prod_unit_l.
Defined.

(** *** Function types *)

(** IsFinite sets are closed under function types, and even dependent function types. *)
Global Instance isfinite_forall `{Funext} {X : Type} (Y : X -> Type)
  `{IsFinite X} `{forall x, IsFinite (Y x)}
  : IsFinite (forall (x : X), Y x).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  srefine (isfinite_equiv _ (equiv_functor_forall'
    (P := fun x => Y (e^-1 x)) e _) _); try exact _.
  1: intros x; refine (equiv_transport _ _ _ (eissect e x)).
  set (Y' := Y o e^-1); change (IsFinite (forall x, Y' x)).
  assert (forall x, IsFinite (Y' x)) by exact _; clearbody Y'; clear e.
  generalize dependent (fcard X); intros n Y' ?.
  induction n as [|n IH].
  - exact _.
  - refine (isfinite_equiv _ (equiv_sum_ind Y') _).
    apply isfinite_prod.
    + apply IH; exact _.
    + refine (isfinite_isequiv _ (@Unit_ind (fun u => Y' (inr u))) _).
      refine (isequiv_unit_ind (Y' o inr)).
Defined.

(** The cardinality of a function type is the exponential of the cardinalities *)
Definition fcard_arrow `{Funext} (X Y : Type) `{IsFinite X} `{IsFinite Y}
  : fcard (X -> Y) = nat_exp (fcard Y) (fcard X).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (fcard_isequiv (functor_arrow e idmap)^-1 @ _).
  refine (_ @ ap (fun x => nat_exp (fcard Y) x) (fcard_equiv e)).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - reflexivity.
  - refine (fcard_equiv (equiv_sum_ind (fun (_:Fin n.+1) => Y))^-1 @ _).
    refine (fcard_prod _ _ @ _).
    apply (ap011 mult).
    + assumption.
    + refine (fcard_isequiv (@Unit_ind (fun (_:Unit) => Y))^-1).
Defined.

(** [fcard] still computes, despite the funext: *)
Goal forall fs:Funext, fcard (Fin 3 -> Fin 4) = 64.
  reflexivity.
Abort.

(** *** Automorphism types (i.e. symmetric groups) *)

Global Instance isfinite_aut `{Funext} (X : Type) `{IsFinite X}
  : IsFinite (X <~> X).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (isfinite_equiv _
            (equiv_functor_equiv e^-1 e^-1) _).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - exact _.
  - refine (isfinite_equiv _ (equiv_fin_equiv n n) _).
Defined.

(** The cardinality of the automorphisms of a type is the factorial of the cardinality. *)
Definition fcard_aut `{Funext} (X : Type) `{IsFinite X}
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

(** ** IsFinite sums of natural numbers *)

(** Perhaps slightly less obviously, finite sets are also closed under sigmas. *)

Global Instance isfinite_sigma {X : Type} (Y : X -> Type) `{IsFinite X}
  `{forall x, IsFinite (Y x)}
  : IsFinite (sig Y).
(** We write [sig Y] instead of [{x:X &Y x}] since the later is an eta-expanded version of the first which coq has trouble working with. *)
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (isfinite_equiv _ (equiv_functor_sigma (equiv_inverse e)
    (fun x (y:Y (e^-1 x)) => y)) _).
  (** Unfortunately, because [compose] is currently beta-expanded, [set (Y' := Y o e^-1)] doesn't change the goal. *)
  set (Y' := fun x => Y (e^-1 x)).
  assert (forall x, IsFinite (Y' x)) by exact _; clearbody Y'; clear e.
  generalize dependent (fcard X); intros n Y' ?.
  induction n as [|n IH].
  - refine (isfinite_isequiv Empty pr1^-1 _).
  - refine (isfinite_equiv _ (equiv_sigma_sum (Fin n) Unit Y')^-1 _).
    apply isfinite_sum.
    + apply IH; exact _.
    + refine (isfinite_equiv _ (equiv_contr_sigma _)^-1 _).
Defined.

(** Amusingly, this automatically gives us a way to add up a family of natural numbers indexed by any finite set.  (We could of course also define such an operation directly, probably using [merely_ind_hset].) *)

Definition finplus {X : Type} `{IsFinite X} (f : X -> nat) : nat
  := fcard { x:X & Fin (f x) }.

Definition fcard_sigma {X : Type} (Y : X -> Type)
       `{IsFinite X} `{forall x, IsFinite (Y x)}
  : fcard { x:X & Y x } = finplus (fun x => fcard (Y x)).
Proof.
  set (f := fun x => fcard (Y x)).
  set (g := fun x => merely_equiv_fin (Y x) : merely (Y x <~> Fin (f x))).
  apply finite_choice in g.
  strip_truncations.
  unfold finplus.
  refine (fcard_equiv (equiv_functor_sigma_id g)).
Defined.

(** The sum of a finite constant family is the product by its cardinality. *)
Definition finplus_const (X : Type) `{IsFinite X} n
  : finplus (fun x:X => n) = fcard X * n.
Proof.
  transitivity (fcard (X * Fin n)).
  - exact (fcard_equiv (equiv_sigma_prod0 X (Fin n))).
  - exact (fcard_prod X (Fin n)).
Defined.

(** Closure under sigmas and paths also implies closure under hfibers. *)
Definition isfinite_hfiber {X Y : Type} (f : X -> Y) (y : Y)
  `{IsFinite X} `{IsFinite Y}
  : IsFinite (hfiber f y) := _.

(** Therefore, the cardinality of the domain of a map between finite sets is the sum of the cardinalities of its hfibers. *)
Definition fcard_domain {X Y : Type} (f : X -> Y) `{IsFinite X} `{IsFinite Y}
  : fcard X = finplus (fun y => fcard (hfiber f y)).
Proof.
  refine (_ @ fcard_sigma (hfiber f)).
  refine (fcard_equiv (equiv_fibration_replacement f)).
Defined.

(** In particular, the image of a map between finite sets is finite. *)
Definition isfinite_image {X Y : Type} `{IsFinite X} `{IsFinite Y} (f : X -> Y)
  : IsFinite (himage f) := _.

(** ** Finite products of natural numbers *)

(** Similarly, closure of finite sets under [forall] automatically gives us a way to multiply a family of natural numbers indexed by any finite set.  Of course, if we defined this explicitly, it wouldn't need funext. *)

Definition finmult `{Funext} {X : Type} `{IsFinite X} (f : X -> nat) : nat
  := fcard (forall x:X, Fin (f x)).

Definition fcard_forall `{Funext} {X : Type} (Y : X -> Type)
  `{IsFinite X} `{forall x, IsFinite (Y x)}
  : fcard (forall x:X, Y x) = finmult (fun x => fcard (Y x)).
Proof.
  set (f := fun x => fcard (Y x)).
  set (g := fun x => merely_equiv_fin (Y x) : merely (Y x <~> Fin (f x))).
  apply finite_choice in g.
  strip_truncations.
  unfold finmult.
  refine (fcard_equiv (equiv_functor_forall' (equiv_idmap X) g)).
Defined.

(** The product of a finite constant family is the exponential by its cardinality. *)
Definition finmult_const `{Funext} (X : Type) `{IsFinite X} (n : nat)
  : finmult (fun x:X => n) = nat_exp n (fcard X).
Proof.
  refine (fcard_arrow X (Fin n)).
Defined.


(** ** Finite subsets *)

(** Closure under sigmas implies that a detachable subset of a finite set is finite. *)
Global Instance isfinite_detachable_subset {X} `{IsFinite X} (P : X -> Type)
  `{forall x, IsHProp (P x)} `{forall x, Decidable (P x)}
  : IsFinite { x:X & P x }.
Proof.
  exact _.
Defined.

(** Conversely, if a subset of a finite set is finite, then it is detachable.  We show first that an embedding between finite subsets has detachable image. *)
Definition detachable_image_isfinite
  {X Y : Type} `{IsFinite X} `{IsFinite Y} (f : X -> Y) `{IsEmbedding f}
  : forall y, Decidable (hfiber f y).
Proof.
  intros y.
  assert (ff : IsFinite (hfiber f y)) by exact _.
  destruct ff as [[|n] e].
  - right; intros u; strip_truncations; exact (e u).
  - left; strip_truncations; exact (e^-1 (inr tt)).
Defined.

Definition detachable_isfinite_subset {X : Type} `{IsFinite X}
  (P : X -> Type) `{forall x, IsHProp (P x)}
  {Pf : IsFinite (sig P)}
  : forall x, Decidable (P x).
Proof.
  intros x.
  refine (decidable_equiv _ (hfiber_fibration x P)^-1 _).
  refine (detachable_image_isfinite pr1 x).
  by apply mapinO_pr1. (* Why can't Coq find this? *)
Defined.

(** ** Injections *)

(** An injection between finite sets induces an inequality between their cardinalities. *)
Definition leq_inj_finite `{Funext} {X Y : Type}
  {fX : IsFinite X} {fY : IsFinite Y} (f : X -> Y) (i : IsEmbedding f)
  : fcard X <= fcard Y.
Proof.
  assert (MapIn (-1)%trunc f) by exact _. clear i.
  destruct fX as [n e]; simpl.
  destruct fY as [m e']; simpl.
  strip_truncations.
  pose (g := e' o f o e^-1).
  assert (MapIn (-1)%trunc g) by (unfold g; exact _).
  clearbody g. clear e e'. generalize dependent m.
  induction n as [|n IHn].
  { intros; exact tt. }
  intros m g ?.
  assert (i : isinj g) by (apply isinj_embedding; exact _).
  destruct m as [|m].
  { elim (g (inr tt)). }
  pose (h := (fin_transpose_last_with m (g (inr tt)))^-1 o g).
  assert (MapIn (-1)%trunc h) by (unfold h; exact _).
  assert (Ha : forall a:Fin n, is_inl (h (inl a))).
  { intros a.
    remember (g (inl a)) as b eqn:p.
    destruct b as [b|[]].
    - assert (q : g (inl a) <> (g (inr tt))).
      { intros r. exact (inl_ne_inr _ _ (i _ _ r)). }
      rewrite p in q; apply symmetric_neq in q.
      assert (r : h (inl a) = inl b).
      { unfold h; apply moveR_equiv_V; symmetry.
        refine (fin_transpose_last_with_rest m (g (inr tt)) b q @ p^). }
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
  exact (IHn m (unfunctor_sum_l h Ha)
             (mapinO_unfunctor_sum_l (-1)%trunc h Ha Hb)).
Qed.

(** ** Enumerations *)

(** A function from [nat] to a finite set must repeat itself eventually. *)
Section Enumeration.

  Context `{Funext} {X : Type} `{IsFinite X} (e : nat -> X).

  Let er (n : nat) : Fin n -> X
    := fun k => e (nat_fin n k).

  Lemma finite_enumeration_stage (n : nat)
    : IsEmbedding (er n) + { n : nat & { k : nat & e n = e (n + k).+1 }}.
  Proof.
    induction n as [|n [IH|IH]].
    - left. intros x.
      apply hprop_inhabited_contr; intros [[] _].
    - destruct (detachable_image_isfinite (er n) (er n.+1 (inr tt)))
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
      elim (not_nltn _ q).
    - assumption.
  Defined.

End Enumeration.


