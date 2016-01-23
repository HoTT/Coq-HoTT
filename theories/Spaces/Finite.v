(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import Fibrations Factorization EquivalenceVarieties UnivalenceImpliesFunext HSet HProp DProp.
Require Import hit.Truncations hit.quotient.
Import TrM.
Require Import Spaces.Nat.

Local Open Scope path_scope.
Local Open Scope nat_scope.

(** * Finite sets *)

(** ** Canonical finite sets *)

(** A *finite set* is a type that is merely equivalent to the canonical finite set determined by some natural number.  There are many equivalent ways to define the canonical finite sets, such as [{ k : nat & k < n}]; we instead choose a recursive one. *)

Fixpoint Fin (n : nat) : Type
  := match n with
       | 0 => Empty
       | S n => Fin n + Unit
     end.

Global Instance decidable_fin (n : nat)
: Decidable (Fin n).
Proof.
  destruct n as [|n]; try exact _.
  exact (inl (inr tt)).
Defined.

Global Instance decidablepaths_fin (n : nat)
: DecidablePaths (Fin n).
Proof.
  induction n as [|n IHn]; simpl; exact _.
Defined.

Global Instance contr_fin1 : Contr (Fin 1).
Proof.
  refine (contr_equiv' Unit (sum_empty_l Unit)^-1).
Defined.

Definition fin_empty (n : nat) (f : Fin n -> Empty) : n = 0.
Proof.
  destruct n; [ reflexivity | ].
  elim (f (inr tt)).
Defined.

(** ** Transposition equivalences *)

(** To prove some basic facts about canonical finite sets, we need some standard automorphisms of them.  Here we define some transpositions and prove that they in fact do the desired things. *)

(** *** Swap the last two elements. *)

Definition fin_transpose_last_two (n : nat)
: Fin n.+2 <~> Fin n.+2
  := ((equiv_sum_assoc _ _ _)^-1)
       oE (1 +E (equiv_sum_symm _ _))
       oE (equiv_sum_assoc _ _ _).

Arguments fin_transpose_last_two : simpl nomatch.

Definition fin_transpose_last_two_last (n : nat)
: fin_transpose_last_two n (inr tt) = (inl (inr tt))
  := 1.

Definition fin_transpose_last_two_nextlast (n : nat)
: fin_transpose_last_two n (inl (inr tt)) = (inr tt)
  := 1.

Definition fin_transpose_last_two_rest (n : nat) (k : Fin n)
: fin_transpose_last_two n (inl (inl k)) = (inl (inl k))
  := 1.

(** *** Swap the last element with [k]. *)

Fixpoint fin_transpose_last_with (n : nat) (k : Fin n.+1)
: Fin n.+1 <~> Fin n.+1.
Proof.
  destruct k as [k|].
  - destruct n as [|n IH].
    + elim k.
    + destruct k as [k|].
      * refine ((fin_transpose_last_two n)
                  oE _
                  oE (fin_transpose_last_two n)).
        refine ((fin_transpose_last_with n (inl k)) +E 1).
      * apply fin_transpose_last_two.
  - exact (equiv_idmap _).
Defined.

Arguments fin_transpose_last_with : simpl nomatch.

Definition fin_transpose_last_with_last (n : nat) (k : Fin n.+1)
: fin_transpose_last_with n k (inr tt) = k.
Proof.
  destruct k as [k|].
  - induction n as [|n IH]; simpl.
    + elim k.
    + destruct k as [k|].
      * simpl. rewrite IH; reflexivity.
      * simpl. apply ap, ap, path_contr.
  - (** We have to destruct [n] since fixpoints don't reduce unless their argument is a constructor. *)
    destruct n; simpl.
    all:apply ap, path_contr.
Qed.

Definition fin_transpose_last_with_with (n : nat) (k : Fin n.+1)
: fin_transpose_last_with n k k = inr tt.
Proof.
  destruct k as [k|].
  - induction n as [|n IH]; simpl.
    + elim k.
    + destruct k as [|k]; simpl.
      * rewrite IH; reflexivity.
      * apply ap, path_contr.
  - destruct n; simpl.
    all:apply ap, path_contr.
Qed.

Definition fin_transpose_last_with_rest (n : nat)
           (k : Fin n.+1) (l : Fin n)
           (notk : k <> inl l)
: fin_transpose_last_with n k (inl l) = (inl l).
Proof.
  destruct k as [k|].
  - induction n as [|n IH]; simpl.
    1:elim k.
    destruct k as [k|]; simpl.
    { destruct l as [l|]; simpl.
      - rewrite IH.
        + reflexivity.
        + exact (fun p => notk (ap inl p)).
      - reflexivity. }
    { destruct l as [l|]; simpl.
      - reflexivity.
      - elim (notk (ap inl (ap inr (path_unit _ _)))). }
  - destruct n; reflexivity.
Qed.

Definition fin_transpose_last_with_last_other (n : nat) (k : Fin n.+1)
: fin_transpose_last_with n (inr tt) k = k.
Proof.
  destruct n; reflexivity.
Qed.

Definition fin_transpose_last_with_invol (n : nat) (k : Fin n.+1)
: fin_transpose_last_with n k o fin_transpose_last_with n k == idmap.
Proof.
  intros l.
  destruct l as [l|[]].
  - destruct k as [k|[]].
    { destruct (dec_paths k l) as [p|p].
      - rewrite p.
        rewrite fin_transpose_last_with_with.
        apply fin_transpose_last_with_last.
      - rewrite fin_transpose_last_with_rest;
          try apply fin_transpose_last_with_rest;
          exact (fun q => p (path_sum_inl _ q)). }
    + rewrite fin_transpose_last_with_last_other.
      apply fin_transpose_last_with_last_other.
  - rewrite fin_transpose_last_with_last.
    apply fin_transpose_last_with_with.
Qed.

(** ** Equivalences between canonical finite sets *)

(** To give an equivalence [Fin n.+1 <~> Fin m.+1] is equivalent to giving an element of [Fin m.+1] (the image of the last element) together with an equivalence [Fin n <~> Fin m].  More specifically, any such equivalence can be decomposed uniquely as a last-element transposition followed by an equivalence fixing the last element.  *)

(** Here is the uncurried map that constructs an equivalence [Fin n.+1 <~> Fin m.+1]. *)
Definition fin_equiv (n m : nat)
           (k : Fin m.+1) (e : Fin n <~> Fin m)
: Fin n.+1 <~> Fin m.+1
  := (fin_transpose_last_with m k)
       oE (e +E 1).

(** Here is the curried version that we will prove to be an equivalence. *)
Definition fin_equiv' (n m : nat)
: ((Fin m.+1) * (Fin n <~> Fin m)) -> (Fin n.+1 <~> Fin m.+1)
  := fun ke => fin_equiv n m (fst ke) (snd ke).

(** We construct its inverse and the two homotopies first as versions using homotopies without funext (similar to [ExtendableAlong]), then apply funext at the end. *)
Definition fin_equiv_hfiber (n m : nat) (e : Fin n.+1 <~> Fin m.+1)
: { kf : (Fin m.+1) * (Fin n <~> Fin m) & fin_equiv' n m kf == e }.
Proof.
  simpl in e.
  refine (equiv_sigma_prod _ _).
  recall (e (inr tt)) as y eqn:p.
  assert (p' := (moveL_equiv_V _ _ p)^).
  exists y.
  destruct y as [y|[]].
  + simple refine (equiv_unfunctor_sum_l
              (fin_transpose_last_with m (inl y) oE e)
              _ _ ; _).
    { intros a. ev_equiv.
      assert (q : inl y <> e (inl a))
        by exact (fun z => inl_ne_inr _ _ (equiv_inj e (z^ @ p^))).
      set (z := e (inl a)) in *.
      destruct z as [z|[]].
      - rewrite fin_transpose_last_with_rest;
        try exact tt; try assumption.
      - rewrite fin_transpose_last_with_last; exact tt. }
    { intros []. ev_equiv.
      rewrite p.
      rewrite fin_transpose_last_with_with; exact tt. }
    intros x. unfold fst, snd; ev_equiv. simpl.
    destruct x as [x|[]]; simpl.
    * rewrite unfunctor_sum_l_beta.
      apply fin_transpose_last_with_invol.
    * refine (fin_transpose_last_with_last _ _ @ p^).
  + simple refine (equiv_unfunctor_sum_l e _ _ ; _).
    { intros a.
      destruct (is_inl_or_is_inr (e (inl a))) as [l|r].
      - exact l.
      - assert (q := inr_un_inr (e (inl a)) r).
        apply moveR_equiv_V in q.
        assert (s := q^ @ ap (e^-1 o inr) (path_unit _ _) @ p').
        elim (inl_ne_inr _ _ s). }
    { intros []; exact (p^ # tt). }
    intros x. unfold fst, snd; ev_equiv. simpl.
    destruct x as [a|[]].
    * rewrite fin_transpose_last_with_last_other.
      apply unfunctor_sum_l_beta.
    * simpl.
      rewrite fin_transpose_last_with_last.
      symmetry; apply p.
Qed.

Definition fin_equiv_inv (n m : nat) (e : Fin n.+1 <~> Fin m.+1)
: (Fin m.+1) * (Fin n <~> Fin m)
  := (fin_equiv_hfiber n m e).1.

Definition fin_equiv_issect (n m : nat) (e : Fin n.+1 <~> Fin m.+1)
: fin_equiv' n m (fin_equiv_inv n m e) == e
  := (fin_equiv_hfiber n m e).2.

Definition fin_equiv_inj_fst (n m : nat)
           (k l : Fin m.+1) (e f : Fin n <~> Fin m)
: (fin_equiv n m k e == fin_equiv n m l f) -> (k = l).
Proof.
  intros p.
  refine (_ @ p (inr tt) @ _); simpl;
  rewrite fin_transpose_last_with_last; reflexivity.
Qed.

Definition fin_equiv_inj_snd (n m : nat)
           (k l : Fin m.+1) (e f : Fin n <~> Fin m)
: (fin_equiv n m k e == fin_equiv n m l f) -> (e == f).
Proof.
  intros p.
  intros x. assert (q := p (inr tt)); simpl in q.
  rewrite !fin_transpose_last_with_last in q.
  rewrite <- q in p; clear q l.
  exact (path_sum_inl _
           (equiv_inj (fin_transpose_last_with m k) (p (inl x)))).
Qed.

(** Now it's time for funext. *)
Global Instance isequiv_fin_equiv `{Funext} (n m : nat)
: IsEquiv (fin_equiv' n m).
Proof.
  refine (isequiv_pathsplit 0 _); split.
  - intros e; exists (fin_equiv_inv n m e).
    apply path_equiv, path_arrow, fin_equiv_issect.
  - intros [k e] [l f]; simpl.
    refine (_ , fun _ _ => tt).
    intros p; refine (_ ; path_ishprop _ _).
    apply (ap equiv_fun) in p.
    apply ap10 in p.
    apply path_prod'.
    + refine (fin_equiv_inj_fst n m k l e f p).
    + apply path_equiv, path_arrow.
      refine (fin_equiv_inj_snd n m k l e f p).
Qed.

Definition equiv_fin_equiv `{Funext} (n m : nat)
: ((Fin m.+1) * (Fin n <~> Fin m)) <~> (Fin n.+1 <~> Fin m.+1)
  := BuildEquiv _ _ (fin_equiv' n m) _.

(** In particular, this implies that if two canonical finite sets are equivalent, then their cardinalities are equal. *)
Definition nat_eq_fin_equiv (n m : nat)
: (Fin n <~> Fin m) -> (n = m).
Proof.
  revert m; induction n as [|n IHn]; induction m as [|m IHm]; intros e.
  - exact idpath.
  - elim (e^-1 (inr tt)).
  - elim (e (inr tt)).
  - refine (ap S (IHn m _)).
    exact (snd (fin_equiv_inv n m e)).
Qed.

(** ** Definition of general finite sets *)

Class Finite (X : Type) :=
  { fcard : nat ;
    merely_equiv_fin : merely (X <~> Fin fcard) }.

Arguments fcard X {_}.
Arguments merely_equiv_fin X {_}.

Definition issig_finite X
: { n : nat & merely (X <~> Fin n) } <~> Finite X.
Proof.
  issig (@Build_Finite X) (@fcard X) (@merely_equiv_fin X).
Defined.

(** Note that the sigma over cardinalities is not truncated.  Nevertheless, because canonical finite sets of different cardinalities are not isomorphic, being finite is still an hprop.  (Thus, we could have truncated the sigma and gotten an equivalent definition, but it would be less convenient to reason about.) *)
Global Instance ishprop_finite X
: IsHProp (Finite X).
Proof.
  refine (trunc_equiv' _ (issig_finite X)).
  apply ishprop_sigma_disjoint; intros n m Hn Hm.
  strip_truncations.
  refine (nat_eq_fin_equiv n m (Hm oE Hn^-1)).
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
Global Instance finite_fin n : Finite (Fin n)
  := Build_Finite _ n (tr (equiv_idmap _)).

(** This includes the empty set. *)
Global Instance finite_empty : Finite Empty
  := finite_fin 0.

(** The unit type is finite, since it's equivalent to [Fin 1]. *)
Global Instance finite_unit : Finite Unit.
Proof.
  refine (finite_equiv' (Fin 1) _ _); simpl.
  apply sum_empty_l.
Defined.

(** Thus, any contractible type is finite. *)
Global Instance finite_contr X `{Contr X} : Finite X
  := finite_equiv Unit equiv_contr_unit^-1 _.

(** Any decidable hprop is finite, since it must be equivalent to [Empty] or [Unit]. *)
Definition finite_decidable_hprop X `{IsHProp X} `{Decidable X}
: Finite X.
Proof.
  destruct (dec X) as [x|nx].
  - assert (Contr X) by exact (contr_inhabited_hprop X x).
    exact _.
  - refine (finite_equiv Empty nx^-1 _).
Defined.

Hint Immediate finite_decidable_hprop : typeclass_instances.

(** It follows that the propositional truncation of any finite set is finite. *)
Global Instance finite_merely X {fX : Finite X}
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
Global Instance finite_paths {X} `{Finite X} (x y : X)
: Finite (x = y).
Proof.
  (** If we assume [Funext], then typeclass inference produces this automatically, since [X] has decidable equality and (hence) is a set, so [x=y] is a decidable hprop.  But we can also deduce it without funext, since [Finite] is an hprop even without funext. *)
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (finite_equiv _ (ap e)^-1 _).
  apply finite_decidable_hprop; exact _.
Defined.

(** Finite sets are also closed under successors. *)

Global Instance finite_succ X `{Finite X} : Finite (X + Unit).
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
Global Instance decidablepaths_finite `{Funext} X `{Finite X}
: DecidablePaths X.
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (decidablepaths_equiv _ e^-1 _).
Defined.

(** However, contrary to what you might expect, we cannot assert that "every finite set is decidable"!  That would be claiming a *uniform* way to select an element from every nonempty finite set, which contradicts univalence. *)

(** One thing we can prove is that any finite hprop is decidable. *)
Global Instance decidable_finite_hprop X `{IsHProp X} {fX : Finite X}
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
Global Instance decidable_merely_finite X {fX : Finite X}
: Decidable (merely X).
Proof.
  exact _.
Defined.

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
  - refine (transport (P (Fin n.+1)) (path_ishprop _ _) (fs _ _ IH)).
Defined.

(** ** The finite axiom of choice *)

Definition finite_choice {X} `{Finite X} (P : X -> Type)
: (forall x, merely (P x)) -> merely (forall x, P x).
Proof.
  intros f.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  set (P' := P o e^-1).
  assert (f' := (fun x => f (e^-1 x)) : forall x, merely (P' x)).
  refine (Trunc_functor (X := forall x:Fin (fcard X), P' x) -1 _ _).
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

Global Instance finite_sum X Y `{Finite X} `{Finite Y}
: Finite (X + Y).
Proof.
  assert (e := merely_equiv_fin Y).
  strip_truncations.
  refine (finite_equiv _ (functor_sum idmap e^-1) _).
  generalize (fcard Y); intros n.
  induction n as [|n IH].
  - refine (finite_equiv _ (sum_empty_r X)^-1 _).
  - refine (finite_equiv _ (equiv_sum_assoc X _ Unit) _).
Defined.

(** Note that the cardinality function [fcard] actually computes.  The same will be true of all the other proofs in this section, though we don't always verify it. *)
Goal fcard (Fin 3 + Fin 4) = 7.
  reflexivity.
Abort.

Definition fcard_sum X Y `{Finite X} `{Finite Y}
: fcard (X + Y) = (fcard X + fcard Y).
Proof.
  refine (_ @ nat_plus_comm _ _).
  assert (e := merely_equiv_fin Y).
  strip_truncations.
  refine (fcard_equiv' (1 +E e) @ _).
  refine (_ @ ap (fun y => (y + fcard X)) (fcard_equiv e^-1)).
  generalize (fcard Y); intros n.
  induction n as [|n IH].
  - refine (fcard_equiv (sum_empty_r X)^-1).
  - refine (fcard_equiv (equiv_sum_assoc _ _ _)^-1 @ _).
    exact (ap S IH).
Defined.

(** *** Binary products *)

Global Instance finite_prod X Y `{Finite X} `{Finite Y}
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
    refine (_ @ nat_plus_comm _ _).
    refine (ap011 plus _ _).
    + apply IH.
    + apply fcard_equiv', prod_unit_l.
  Defined.

(** *** Function types *)

(** Finite sets are closed under function types, and even dependent function types. *)

Global Instance finite_forall `{Funext} {X} (Y : X -> Type)
       `{Finite X} `{forall x, Finite (Y x)}
: Finite (forall x:X, Y x).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  simple refine (finite_equiv' _
            (equiv_functor_forall' (P := fun x => Y (e^-1 x)) e _) _); try exact _.
  { intros x; refine (equiv_transport _ _ _ (eissect e x)). }
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

Definition fcard_arrow `{Funext} X Y `{Finite X} `{Finite Y}
: fcard (X -> Y) = nat_exp (fcard Y) (fcard X).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (fcard_equiv (functor_arrow e idmap)^-1 @ _).
  refine (_ @ ap (fun x => nat_exp (fcard Y) x) (fcard_equiv e)).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - reflexivity.
  - refine (fcard_equiv (equiv_sum_ind (fun (_:Fin n.+1) => Y))^-1 @ _).
    refine (fcard_prod _ _ @ _).
    apply (ap011 mult).
    + assumption.
    + refine (fcard_equiv (@Unit_ind (fun (_:Unit) => Y))^-1).
Defined.

(** [fcard] still computes, despite the funext: *)
Goal forall fs:Funext, fcard (Fin 3 -> Fin 4) = 64.
  reflexivity.
Abort.

(** *** Automorphism types (i.e. symmetric groups) *)

Global Instance finite_aut `{Funext} X `{Finite X}
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

Global Instance finite_sigma {X} (Y : X -> Type)
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
  - refine (finite_equiv Empty pr1^-1 _).
  - refine (finite_equiv _ (equiv_sigma_sum (Fin n) Unit Y')^-1 _).
    apply finite_sum.
    + apply IH; exact _.
    + refine (finite_equiv _ (equiv_contr_sigma _)^-1 _).
Defined.

(** Amusingly, this automatically gives us a way to add up a family of natural numbers indexed by any finite set.  (We could of course also define such an operation directly, probably using [merely_ind_hset].) *)

Definition finplus {X} `{Finite X} (f : X -> nat) : nat
  := fcard { x:X & Fin (f x) }.

Definition fcard_sigma {X} (Y : X -> Type)
       `{Finite X} `{forall x, Finite (Y x)}
: fcard { x:X & Y x } = finplus (fun x => fcard (Y x)).
Proof.
  set (f := fun x => fcard (Y x)).
  set (g := fun x => merely_equiv_fin (Y x) : merely (Y x <~> Fin (f x))).
  apply finite_choice in g.
  strip_truncations.
  unfold finplus.
  refine (fcard_equiv' (equiv_functor_sigma' (equiv_idmap X) g)).
Defined.

(** The sum of a finite constant family is the product by its cardinality. *)
Definition finplus_const X `{Finite X} n
: finplus (fun x:X => n) = fcard X * n.
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
: fcard X = finplus (fun y => fcard (hfiber f y)).
Proof.
  refine (_ @ fcard_sigma (hfiber f)).
  refine (fcard_equiv' (equiv_fibration_replacement f)).
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
  apply finite_choice in g.
  strip_truncations.
  unfold finmult.
  refine (fcard_equiv' (equiv_functor_forall' (equiv_idmap X) g)).
Defined.

(** The product of a finite constant family is the exponential by its cardinality. *)
Definition finmult_const `{Funext} X `{Finite X} n
: finmult (fun x:X => n) = nat_exp n (fcard X).
Proof.
  refine (fcard_arrow X (Fin n)).
Defined.


(** ** Finite subsets *)

(** Closure under sigmas implies that a detachable subset of a finite set is finite. *)
Global Instance finite_detachable_subset {X} `{Finite X} (P : X -> Type)
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
  refine (decidable_equiv _ (hfiber_fibration x P)^-1 _).
  refine (detachable_image_finite pr1 x).
  - assumption.                 (** Why doesn't Coq find this? *)
  - apply mapinO_pr1; exact _.  (** Why doesn't Coq find this? *)
Defined.

(** ** Quotients *)

(** The quotient of a finite set by a detachable equivalence relation is finite. *)

Section DecidableQuotients.
  Context `{Univalence} {X} `{Finite X}
          (R : relation X) `{is_mere_relation X R}
          `{Reflexive _ R} `{Transitive _ R} `{Symmetric _ R}
          {Rd : forall x y, Decidable (R x y)}.

  Global Instance finite_quotient : Finite (quotient R).
  Proof.
    assert (e := merely_equiv_fin X).
    strip_truncations.
    pose (R' x y := R (e^-1 x) (e^-1 y)).
    assert (is_mere_relation _ R') by exact _.
    assert (Reflexive R') by (intros ?; unfold R'; apply reflexivity).
    assert (Symmetric R') by (intros ? ?; unfold R'; apply symmetry).
    assert (Transitive R') by (intros ? ? ?; unfold R'; apply transitivity).
    assert (R'd : forall x y, Decidable (R' x y)) by (intros ? ?; unfold R'; apply Rd).
    simple refine (finite_equiv' (quotient R') (quotient_functor_equiv R' R e^-1 _) _); try exact _.
    { intros x y; split; apply idmap. }
    clearbody R'; clear e.
    generalize dependent (fcard X);
      intros n; induction n as [|n IH]; intros R' ? ? ? ? ?.
    - refine (finite_equiv Empty _^-1 _).
      refine (quotient_rec R' Empty_rec (fun x _ _ => match x with end)).
    - pose (R'' x y := R' (inl x) (inl y)).
      assert (is_mere_relation _ R'') by exact _.
      assert (Reflexive R'') by (intros ?; unfold R''; apply reflexivity).
      assert (Symmetric R'') by (intros ? ?; unfold R''; apply symmetry).
      assert (Transitive R'') by (intros ? ? ?; unfold R''; apply transitivity).
      assert (forall x y, Decidable (R'' x y)) by (intros ? ?; unfold R''; apply R'd).
      assert (inlresp := (fun x y => idmap)
                         : forall x y, R'' x y -> R' (inl x) (inl y)).
      destruct (dec (merely {x:Fin n & R' (inl x) (inr tt)})) as [p|np].
      { strip_truncations.
        destruct p as [x r].
        refine (finite_equiv' (quotient R'') _ _).
        refine (BuildEquiv _ _ (quotient_functor R'' R' inl inlresp) _).
        apply isequiv_surj_emb.
        - apply BuildIsSurjection.
          refine (quotient_ind_prop R' _ _).
          intros [y|[]]; apply tr.
          + exists (class_of R'' y); reflexivity.
          + exists (class_of R'' x); simpl.
            apply related_classes_eq, r.
        - apply isembedding_isinj_hset; intros u.
          refine (quotient_ind_prop R'' _ _); intros v.
          revert u; refine (quotient_ind_prop R'' _ _); intros u.
          simpl; intros q.
          apply related_classes_eq; unfold R''.
          exact (classes_eq_related R' (inl u) (inl v) q). }
      { refine (finite_equiv' (quotient R'' + Unit) _ _).
        refine (BuildEquiv _ _ (sum_ind (fun _ => quotient R')
                                        (quotient_functor R'' R' inl inlresp)
                                        (fun _ => class_of R' (inr tt))) _).
        apply isequiv_surj_emb.
        - apply BuildIsSurjection.
          refine (quotient_ind_prop R' _ _).
          intros [y|[]]; apply tr.
          + exists (inl (class_of R'' y)); reflexivity.
          + exists (inr tt); reflexivity.
        - apply isembedding_isinj_hset; intros u.
          refine (sum_ind _ _ _).
          + refine (quotient_ind_prop R'' _ _); intros v.
            revert u; refine (sum_ind _ _ _).
            * refine (quotient_ind_prop R'' _ _); intros u.
              simpl; intros q.
              apply ap, related_classes_eq; unfold R''.
              exact (classes_eq_related R' (inl u) (inl v) q).
            * intros []; simpl.
              intros q.
              apply classes_eq_related in q; try exact _.
              apply symmetry in q.
              elim (np (tr (v ; q))).
          + intros []; simpl.
            destruct u as [u|[]]; simpl.
            * revert u; refine (quotient_ind_prop R'' _ _); intros u; simpl.
              intros q.
              apply classes_eq_related in q; try exact _.
              elim (np (tr (u;q))).
            * intros; reflexivity. }
  Defined.

  (** Therefore, the cardinality of [X] is the sum of the cardinalities of its equivalence classes. *)
  Definition fcard_quotient
  : fcard X = finplus (fun z:quotient R => fcard {x:X & in_class R z x}).
  Proof.
    refine (fcard_domain (class_of R) @ _).
    apply ap, path_arrow; intros z; revert z.
    refine (quotient_ind_prop _ _ _); intros x; simpl.
    apply fcard_equiv'; unfold hfiber.
    refine (equiv_functor_sigma' 1 _); intros y; simpl.
    refine (_ oE sets_exact R y x).
    apply equiv_iff_hprop; apply symmetry.
  Defined.

End DecidableQuotients.

(** ** Injections *)

(** An injection between finite sets induces an inequality between their cardinalities. *)
Definition leq_inj_finite `{Funext} {X Y} {fX : Finite X} {fY : Finite Y}
           (f : X -> Y) (i : IsEmbedding f)
: fcard X <= fcard Y.
Proof.
  assert (MapIn -1 f) by exact _. clear i.
  destruct fX as [n e]; simpl.
  destruct fY as [m e']; simpl.
  strip_truncations.
  pose (g := e' o f o e^-1).
  assert (MapIn -1 g) by (unfold g; exact _).
  clearbody g. clear e e'. generalize dependent m.
  induction n as [|n IHn].
  { intros; exact tt. }
  intros m g ?.
  assert (i : isinj g) by (apply isinj_embedding; exact _).
  destruct m as [|m].
  { elim (g (inr tt)). }
  pose (h := (fin_transpose_last_with m (g (inr tt)))^-1 o g).
  assert (MapIn -1 h) by (unfold h; exact _).
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
             (mapinO_unfunctor_sum_l -1 h Ha Hb)).
Qed.

(** ** Initial segments of [nat] *)

Definition nat_fin (n : nat) (k : Fin n) : nat.
Proof.
  induction n as [|n nf].
  - contradiction.
  - destruct k as [k|_].
    + exact (nf k).
    + exact n.
Defined.

Definition nat_fin_inl (n : nat) (k : Fin n)
: nat_fin n.+1 (inl k) = nat_fin n k
  := 1.

Definition nat_fin_compl (n : nat) (k : Fin n) : nat.
Proof.
  induction n as [|n nfc].
  - contradiction.
  - destruct k as [k|_].
    + exact (nfc k).+1.
    + exact 0.
Defined.

Definition nat_fin_compl_compl n k
: (nat_fin n k + nat_fin_compl n k).+1 = n.
Proof.
  induction n as [|n IH].
  - contradiction.
  - destruct k as [k|?]; simpl.
    + rewrite nat_plus_comm.
      specialize (IH k).
      rewrite nat_plus_comm in IH.
      exact (ap S IH).
    + rewrite nat_plus_comm; reflexivity.
Qed.

(** ** Enumerations *)

(** A function from [nat] to a finite set must repeat itself eventually. *)
Section Enumeration.
  Context `{Funext} {X} `{Finite X} (e : nat -> X).

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
      elim (not_nltn _ q).
    - assumption.
  Defined.

End Enumeration.
