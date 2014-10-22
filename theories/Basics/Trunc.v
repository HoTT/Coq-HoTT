(* -*- mode: coq; mode: visual-line -*-  *)
(** * Truncatedness *)

Require Import Overture PathGroupoids Contractible Equivalences.
Local Open Scope equiv_scope.
Local Open Scope trunc_scope.
Local Open Scope path_scope.
Generalizable Variables A B m n f.

(** ** Arithmetic on truncation-levels. *)

Fixpoint trunc_index_add (m n : trunc_index) : trunc_index
  := match m with
       | -2 => n
       | m'.+1 => (trunc_index_add m' n).+1
     end.

Notation "m -2+ n" := (trunc_index_add m n) (at level 50, left associativity) : trunc_scope.

Fixpoint trunc_index_leq (m n : trunc_index) : Type
  := match m, n with
       | -2, _ => Unit
       | m'.+1, -2 => Empty
       | m'.+1, n'.+1 => trunc_index_leq m' n'
     end.

Notation "m <= n" := (trunc_index_leq m n) (at level 70, no associativity) : trunc_scope.

(** ** Truncatedness proper. *)

(** A contractible space is (-2)-truncated, by definition. *)
Definition contr_trunc_minus_two `{H : IsTrunc -2 A} : Contr A
  := H.

(** Truncation levels are cumulative. *)
Global Instance trunc_succ `{IsTrunc n A} : IsTrunc n.+1 A | 1000.
Proof.
  generalize dependent A.
  induction n as [| n I]; simpl; intros A H x y.
  - apply contr_paths_contr.
  - apply I, H.
Qed.

Global Instance trunc_leq {m n} (Hmn : m <= n) `{IsTrunc m A} : IsTrunc n A | 1000.
Proof.
  generalize dependent A; generalize dependent m.
  induction n as [ | n' IH];
    intros [ | m'] Hmn A ? .
  - (* -2, -2 *) assumption.
  - (* S m', -2 *) destruct Hmn.
  - (* -2, S n' *) apply @trunc_succ, (IH -2); auto.
  - (* S m', S n' *) intros x y; apply (IH m');
                     auto with typeclass_instances.
Qed.

(** In particular, a contractible type, hprop, or hset is truncated at all higher levels. *)

Definition trunc_contr {n} {A} `{Contr A} : IsTrunc n A
  := (@trunc_leq -2 n tt _ _).

Definition trunc_hprop {n} {A} `{IsHProp A} : IsTrunc n.+1 A
  := (@trunc_leq -1 n.+1 tt _ _).

Definition trunc_hset {n} {A} `{IsHSet A} : IsTrunc n.+1.+1 A
  := (@trunc_leq 0 n.+1.+1 tt _ _).

(** Consider the preceding definitions as instances for typeclass search, but only if the requisite hypothesis is already a known assumption; otherwise they result in long or interminable searches. *)
Hint Immediate trunc_contr : typeclass_instances.
Hint Immediate trunc_hprop : typeclass_instances.
Hint Immediate trunc_hset : typeclass_instances.

(** Equivalence preserves truncation (this is, of course, trivial with univalence).
   This is not an [Instance] because it causes infinite loops.
   *)
Definition trunc_equiv A {B} (f : A -> B)
  `{IsTrunc n A} `{IsEquiv A B f}
  : IsTrunc n B.
Proof.
  generalize dependent B; generalize dependent A.
  induction n as [| n I]; simpl; intros A ? B f ?.
  - exact (contr_equiv _ f).
  - intros x y.
    exact (I (f^-1 x = f^-1 y) (H (f^-1 x) (f^-1 y)) (x = y) ((ap (f^-1))^-1) _).
Qed.

Definition trunc_equiv' A {B} (f : A <~> B) `{IsTrunc n A}
  : IsTrunc n B
  := trunc_equiv A f.

(** ** Truncated morphisms *)

Class IsTruncMap (n : trunc_index) {X Y : Type} (f : X -> Y) :=
  istruncmap_fiber : forall y:Y, IsTrunc n (hfiber f y).

Global Existing Instance istruncmap_fiber.

Notation IsEmbedding := (IsTruncMap -1).

(** ** Universes of truncated types *)

(** It is convenient for some purposes to consider the universe of all n-truncated types (within a given universe of types).  In particular, this allows us to state the important fact that each such universe is itself (n+1)-truncated. *)

Record TruncType (n : trunc_index) := BuildTruncType {
  trunctype_type : Type ;
  istrunc_trunctype_type : IsTrunc n trunctype_type
}.
(* Note: the naming of the second constructor is more than a little clunky.  However, the more obvious [istrunc_trunctype] is taken by the theorem below, that [IsTrunc n.+1 (TruncType n)], which seems to have an even better claim to it. *)

Arguments BuildTruncType _ _ {_}.
Arguments trunctype_type {_} _.
Arguments istrunc_trunctype_type [_] _.

Coercion trunctype_type : TruncType >-> Sortclass.
Global Existing Instance istrunc_trunctype_type.

Notation "n -Type" := (TruncType n) (at level 1) : type_scope.
Notation hProp := (-1)-Type.
Notation hSet := 0-Type.

Notation BuildhProp := (BuildTruncType -1).
Notation BuildhSet := (BuildTruncType 0).

(** This is (as of October 2014) the only [Canonical Structure] in the library.  It would be nice to do without it, in the interests of minimizing the number of fancy Coq features that the reader needs to know about. *)
Canonical Structure default_TruncType := fun n T P => (@BuildTruncType n T P).

(** ** Facts about hprops *)

(** An inhabited proposition is contractible.
   This is not an [Instance] because it causes infinite loops.
   *)
Lemma contr_inhabited_hprop (A : Type) `{H : IsHProp A} (x : A)
  : Contr A.
Proof.
  exists x.
  intro y.
  apply center, H.
Defined.

(** If inhabitation implies contractibility, then we have an h-proposition.  We probably won't often have a hypothesis of the form [A -> Contr A], so we make sure we give priority to other instances. *)
Global Instance hprop_inhabited_contr (A : Type) : (A -> Contr A) -> IsHProp A | 10000.
Proof.
  intros H x y.
  pose (C := H x).
  apply contr_paths_contr.
Defined.

(** Any two points in an hprop are connected by a path. *)
Theorem path_ishprop `{H : IsHProp A} : forall x y : A, x = y.
Proof.
  apply H.
Defined.

(** Conversely, this property characterizes hprops. *)
Theorem hprop_allpath (A : Type) : (forall (x y : A), x = y) -> IsHProp A.
  intros H x y.
  pose (C := BuildContr A x (H x)).
  apply contr_paths_contr.
Defined.

(** Two propositions are equivalent as soon as there are maps in both directions. *)
Definition isequiv_iff_hprop `{IsHProp A} `{IsHProp B}
  (f : A -> B) (g : B -> A)
: IsEquiv f.
Proof.
  apply (isequiv_adjointify f g);
    intros ?; apply path_ishprop.
Defined.

Definition equiv_iff_hprop_uncurried `{IsHProp A} `{IsHProp B}
  : (A <-> B) -> (A <~> B).
Proof.
  intros [f g].
  apply (equiv_adjointify f g);
    intros ?; apply path_ishprop.
Defined.

Definition equiv_iff_hprop `{IsHProp A} `{IsHProp B}
  : (A -> B) -> (B -> A) -> (A <~> B)
  := fun f g => equiv_iff_hprop_uncurried (f, g).

(** ** Hedberg's theorem: any type with decidable equality is a set. *)

Class WeaklyConstant {A B} (f : A -> B) :=
  wconst : forall x y, f x = f y.

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

Global Instance hset_pathcoll (A : Type) `{PathCollapsible A}
: IsHSet A.
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
