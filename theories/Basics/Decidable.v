(* -*- mode: coq; mode: visual-line -*-  *)
Require Import Overture PathGroupoids Contractible Equivalences Trunc.
Local Open Scope trunc_scope.
Local Open Scope path_scope.

(** * Decidability *)

(** ** Definitions *)

(* NB: This has to come after our definition of [not] (which is in [Overture]), so that it refers to our [not] rather than the one in [Coq.Logic]. *)
Class Decidable (A : Type) :=
  dec : A + (~ A).
Arguments dec A {_}.

Class DecidablePaths (A : Type) :=
  dec_paths : forall (x y : A), Decidable (x = y).
Global Existing Instance dec_paths.

Class Stable P := stable : ~~P -> P.

Global Instance stable_decidable P `{!Decidable P} : Stable P.
Proof.
  intros dn;destruct (dec P) as [p|n].
  - assumption.
  - apply Empty_rect,dn,n.
Qed.

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

Definition decidable_equiv (A : Type) {B : Type} (f : A -> B) `{IsEquiv A B f}
: Decidable A -> Decidable B.
Proof.
  intros [a|na].
  - exact (inl (f a)).
  - exact (inr (fun b => na (f^-1 b))).
Defined.

Definition decidable_equiv' (A : Type) {B : Type} (f : A <~> B)
: Decidable A -> Decidable B
  := decidable_equiv A f.

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

Corollary hset_decpaths (A : Type) `{DecidablePaths A}
: IsHSet A.
Proof.
  exact _.
Defined.

(** ** Truncation *)

(** Having decidable equality (which implies being an hset, by Hedberg's theorem above) is itself an hprop. *)

Global Instance ishprop_decpaths `{Funext} (A : Type)
: IsHProp (DecidablePaths A).
Proof.
  apply hprop_inhabited_contr; intros d.
  assert (IsHSet A) by exact _.
  exists d; intros d'.
  apply path_forall; intros x; apply path_forall; intros y.
  generalize (d x y); clear d; intros d.
  generalize (d' x y); clear d'; intros d'.
  destruct d as [d|nd]; destruct d' as [d'|nd'].
  - apply ap, path_ishprop.
  - elim (nd' d).
  - elim (nd d').
  - apply ap, path_forall; intros p; elim (nd p).
Defined.
