Require Import
  Basics.Overture
  Basics.PathGroupoids
  Basics.Trunc
  Basics.Tactics
  Basics.Iff.
Local Open Scope trunc_scope.
Local Open Scope path_scope.

(** * Decidability *)

(** ** Definitions *)

(* NB: This has to come after our definition of [not] (which is in [Overture]), so that it refers to our [not] rather than the one in [Coq.Logic]. *)
Class Decidable (A : Type) :=
  dec : A + (~ A).
Arguments dec A {_}.

(** The [decide_type] and [decide] tactic allow to automatically prove
decidable claims using previously written decision procedures that
compute. *)
Ltac decide_type A :=
  let K := (eval hnf in (dec A)) in
  match K with
  | inl ?Z => exact Z
  | inr ?Z => exact Z
  end.

Ltac decide :=
  multimatch goal with
  | [|- ?A] => decide_type A
  | [|- ~ ?A] => decide_type A
  end.

Definition decidable_true {A : Type}
  (a : A)
  (P : forall (p : Decidable A), Type)
  (p : forall x, P (inl x))
  : forall p, P p.
Proof.
  intros [x|n].
  - apply p.
  - contradiction n.
Defined.

(** Replace a term [p] of the form [Decidable A] with [inl x] if we have a term [a : A] showing that [A] is true. *)
Ltac decidable_true p a :=
  generalize p;
  rapply (decidable_true a);
  try intro.

Definition decidable_false {A : Type}
  (n : not A)
  (P : forall (p : Decidable A), Type)
  (p : forall n', P (inr n'))
  : forall p, P p.
Proof.
  intros [x|n'].
  - contradiction n.
  - apply p.
Defined.

(** Replace a term [p] of the form [Decidable A] with [inr na] if we have a term [n : not A] showing that [A] is false. *)
Ltac decidable_false p n :=
  generalize p;
  rapply (decidable_false n);
  try intro.

Class DecidablePaths (A : Type) :=
  dec_paths : forall (x y : A), Decidable (x = y).
Global Existing Instance dec_paths.

Class Stable P := stable : ~~P -> P.

(** We always have a map in the other direction. *)
Definition not_not_unit {P : Type} : P -> ~~P
  := fun x np => np x.

Global Instance stable_decidable P `{!Decidable P} : Stable P.
Proof.
  intros dn;destruct (dec P) as [p|n].
  - assumption.
  - apply Empty_rect,dn,n.
Qed.

Global Instance stable_negation P : Stable (~ P).
Proof.
  intros nnnp p.
  exact (nnnp (not_not_unit p)).
Defined.

Definition iff_stable P `(Stable P) : ~~P <-> P.
Proof.
  split.
  - apply stable.
  - exact not_not_unit.
Defined.

Definition stable_iff {A B} (f : A <-> B)
  : Stable A -> Stable B.
Proof.
  intros stableA nnb.
  destruct f as [f finv].
  exact (f (stableA (fun na => nnb (fun b => na (finv b))))).
Defined.

Definition stable_equiv' {A B} (f : A <~> B)
  : Stable A -> Stable B
  := stable_iff f.

Definition stable_equiv {A B} (f : A -> B) `{!IsEquiv f}
  : Stable A -> Stable B
  := stable_equiv' (Build_Equiv _ _ f _).

(**
  Because [vm_compute] evaluates terms in [PROP] eagerly
  and does not remove dead code we
  need the decide_rel hack. Suppose we have [(x = y) =def  (f x = f y)], now:
     bool_decide (x = y) -> bool_decide (f x = f y) -> ...
  As we see, the dead code [f x] and [f y] is actually evaluated,
  which is of course an utter waste.
  Therefore we introduce decide_rel and bool_decide_rel.
     bool_decide_rel (=) x y -> bool_decide_rel (fun a b => f a = f b) x y -> ...
  Now the definition of equality remains under a lambda and
  our problem does not occur anymore!
*)
Definition decide_rel {A B} (R : A -> B -> Type)
  {dec : forall x y, Decidable (R x y)} (x : A) (y : B)
  : Decidable (R x y)
  := dec x y.

(** ** Decidable hprops *)

(** Contractible types are decidable. *)

Global Instance decidable_contr X `{Contr X} : Decidable X
  := inl (center X).

(** Thus, hprops have decidable equality. *)

Global Instance decidablepaths_hprop X `{IsHProp X} : DecidablePaths X
  := fun x y => dec (x = y).

(** Empty types are trivial. *)

Global Instance decidable_empty : Decidable Empty
  := inr idmap.


(** ** Transfer along equivalences *)

Definition decidable_iff {A B} (f : A <-> B)
  : Decidable A -> Decidable B.
Proof.
  intros [a|na].
  - exact (inl (fst f a)).
  - exact (inr (fun b => na (snd f b))).
Defined.

Definition decidable_equiv' (A : Type) {B : Type} (f : A <~> B)
: Decidable A -> Decidable B
  := decidable_iff f.

Definition decidable_equiv (A : Type) {B : Type} (f : A -> B) `{!IsEquiv f}
: Decidable A -> Decidable B
  := decidable_equiv' _ (Build_Equiv _ _ f _).

Definition decidablepaths_equiv
           (A : Type) {B : Type} (f : A -> B) `{IsEquiv A B f}
: DecidablePaths A -> DecidablePaths B.
Proof.
  intros d x y.
  destruct (d (f^-1 x) (f^-1 y)) as [e|ne].
  - apply inl. exact ((eisretr f x)^ @ ap f e @ eisretr f y).
  - apply inr; intros p. apply ne, ap, p.
Defined.

Definition decidablepaths_equiv' (A : Type) {B : Type} (f : A <~> B)
: DecidablePaths A -> DecidablePaths B
  := decidablepaths_equiv A f.

(** ** Hedberg's theorem: any type with decidable equality is a set. *)

(** A weakly constant function is one all of whose values are equal (in a specified way). *)
Class WeaklyConstant {A B} (f : A -> B) :=
  wconst : forall x y, f x = f y.

(** Any map that factors through an hprop is weakly constant. *)
Definition wconst_through_hprop {A B P} `{IsHProp P}
           (f : A -> P) (g : P -> B)
: WeaklyConstant (g o f).
Proof.
  intros x y; apply (ap g), path_ishprop.
Defined.

(** A type is collapsible if it admits a weakly constant endomap. *)
Class Collapsible (A : Type) :=
  { collapse : A -> A ;
    wconst_collapse : WeaklyConstant collapse
  }.
Global Existing Instance wconst_collapse.

Class PathCollapsible (A : Type) :=
  path_coll : forall (x y : A), Collapsible (x = y).
Global Existing Instance path_coll.

Global Instance collapsible_decidable (A : Type) `{Decidable A}
: Collapsible A.
Proof.
  destruct (dec A) as [a | na].
  - exists (const a).
    intros x y; reflexivity.
  - exists idmap.
    intros x y; destruct (na x).
Defined.

Global Instance pathcoll_decpaths (A : Type) `{DecidablePaths A}
: PathCollapsible A.
Proof.
  intros x y; exact _.
Defined.

(** We give this a relatively high-numbered priority so that in deducing [IsHProp -> IsHSet] Coq doesn't detour via [DecidablePaths]. *)
Global Instance hset_pathcoll (A : Type) `{PathCollapsible A}
: IsHSet A | 1000.
Proof.
  apply istrunc_S.
  intros x y.
  assert (h : forall p:x=y, p = (collapse (idpath x))^ @ collapse p).
  { intros []; symmetry; by apply concat_Vp. }
  apply hprop_allpath; intros p q.
  refine (h p @ _ @ (h q)^).
  apply whiskerL.
  apply wconst.
Defined.

Definition collapsible_hprop (A : Type) `{IsHProp A}
: Collapsible A.
Proof.
  exists idmap.
  intros x y; apply path_ishprop.
Defined.

Definition pathcoll_hset (A : Type) `{IsHSet A}
: PathCollapsible A.
Proof.
  intros x y; apply collapsible_hprop; exact _.
Defined.

(** Hedberg's Theorem *)
Corollary hset_decpaths (A : Type) `{DecidablePaths A}
: IsHSet A.
Proof.
  exact _.
Defined.

(** We can use Hedberg's Theorem to simplify a goal of the form [forall (d : Decidable (x = x :> A)), P d] when [A] has decidable paths. *)
Definition decidable_paths_refl (A : Type) `{DecidablePaths A}
  (x : A)
  (P : forall (d : Decidable (x = x)), Type)
  (Px : P (inl idpath))
  : forall d, P d.
Proof.
  rapply (decidable_true idpath).
  intro p.
  (** We cannot eliminate [p : x = x] with path induction, but we can use Hedberg's theorem to replace this with [idpath]. *)
  assert (r : (idpath = p)) by apply path_ishprop.
  by destruct r.
Defined.

(** ** Truncation *)

(** Having decidable equality (which implies being an hset, by Hedberg's theorem above) is itself an hprop. *)

Global Instance ishprop_decpaths `{Funext} (A : Type)
: IsHProp (DecidablePaths A).
Proof.
  apply hprop_inhabited_contr; intros d.
  assert (IsHSet A) by exact _.
  apply (Build_Contr _ d).
  intros d'.
  funext x y.
  generalize (d x y); clear d; intros d.
  generalize (d' x y); clear d'; intros d'.
  destruct d as [d|nd]; destruct d' as [d'|nd'].
  - apply ap, path_ishprop.
  - elim (nd' d).
  - elim (nd d').
  - apply ap, path_forall; intros p; elim (nd p).
Defined.

(** ** Logical Laws *)

(** Various logical laws don't hold constructively as they do classically due to a required use of excluded middle. For us, this means that some laws require further assumptions on the decidability of propositions. *)

(** Here we give the dual De Morgan's Law which complements the one given in Iff.v.  One direction requires that one of the two propositions be decidable, while the other direction needs no assumption.  We state the latter property first, to avoid duplication in the proof. *)
Definition not_prod_sum_not A B : ~ A + ~ B -> ~ (A * B).
Proof.
  intros [na|nb] [a b].
  - exact (na a).
  - exact (nb b).
Defined.

Definition iff_not_prod A B `{Decidable A}
  : ~ (A * B) <-> ~ A + ~ B.
Proof.
  split.
  - intros np.
    destruct (dec A) as [a|na].
    + exact (inr (fun b => np (a, b))).
    + exact (inl na).
  - apply not_prod_sum_not.
Defined.

Definition iff_not_prod' A B `{Decidable B}
  : ~ (A * B) <-> ~ A + ~ B.
Proof.
  split.
  - intros np.
    destruct (dec B) as [b|nb].
    + exact (inl (fun a => np (a, b))).
    + exact (inr nb).
  - apply not_prod_sum_not.
Defined.
