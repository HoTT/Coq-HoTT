Require Import Basics Types.Unit Types.Sigma Types.Universe Types.Equiv.
Require Import HFiber Truncations Pointed.Core Pointed.Loops.
(* Require Import PropResizing. *)

(** * Facts about "small" types  *)

(** This closely follows Section 2 of the paper "Non-accessible localizations", by Dan Christensen, https://arxiv.org/abs/2109.06670 *)

(* TODO: be consistent about "issmall" vs "small", "islocally" vs "locally".
   Also, should it be "islocally_small" or "islocallysmall"? *)
(* Require Import Conn. *)
(* Require Import misc. *)

Open Scope trunc_scope.

(** Universe variables:  we most often use a subset of [i j k u].  We think of [Type@{i}] as containing the "small" types and [Type@{j}] the "large" types.  In some early results, there are no constraints between [i] and [j], and in others we require that [i <= j], as expected.  While the case [i = j] isn't particularly interesting, we put some effort into ensuring that it is permitted as well, as there is no semantic reason to exclude it.  The universe variable [k] should be thought of as max(i+1,j), and it is generally required to satisfy [i < k] and [j <= k].  If we assume that [i < j], then we can take [k = j], but we include [k] so that we also allow the case [i = j].  The universe variable [u] is only present because we occasionally use Univalence in [Type@{k}], so the equality types need a larger universe to live in.  Because of this, most results require [k < u].

Summary of the most common situation:  [i < k < u, j <= k], where [i] is for the small types, [j] is for the large types, [k = max(i+1,j)] and [u] is an ambient universe for Univalence.

We include universe annotations when they clarify the meaning (e.g. in [IsSmall] and when using [PropResizing]), and also when it is required in order to keep control of the universe variables. *)

(** We say that [X : Type@{j}] is small (relative to Type@{i}) if it is equivalent to a type in [Type@{i}].  We use a record to avoid an extra universe variable.  This version has no constraints on [i] and [j].  It lands in [max(i+1,j)], as expected. *)
#[universes(cumulative)]
Record IsSmall@{i j | } (X : Type@{j}) :=
  { smalltype : Type@{i} ;
    equiv_smalltype : smalltype <~> X
  }.
Arguments smalltype {X} _.
Arguments equiv_smalltype {X} _.

Global Instance ishprop_issmall@{i j k | i < k, j <= k} `{Univalence} (X : Type@{j})
  : IsHProp (IsSmall@{i j} X).
Proof.
  apply hprop_inhabited_contr.
  intros [Z e].
  (* [IsSmall X] is equivalent to [IsSmall Z], which is contractible since it is a based path space. *)
  rapply (istrunc_equiv_istrunc { Y : Type@{i} & Y <~> Z } _).
  equiv_via (sig@{k k} (fun Y : Type@{i} => Y <~> X)).
  2: issig.
  apply equiv_functor_sigma_id.
  intro Y.
  exact (equiv_functor_postcompose_equiv Y e).
Defined.

(** A type in [Type@{i}] is clearly small.  Make this a Global Instance? *)
Definition issmall_in@{i j | i <= j} (X : Type@{i}) : IsSmall@{i j} X
  := Build_IsSmall X X equiv_idmap.

(** The small types are closed under equivalence. *)
Definition issmall_equiv_issmall@{i j1 j2 | } {A : Type@{j1}} {B : Type@{j2}}
  (e : A <~> B) (sA : IsSmall@{i j1} A)
  : IsSmall@{i j2} B.
Proof.
  exists (smalltype sA).
  exact (e oE (equiv_smalltype sA)).
Defined.

(** The small types are closed under dependent sums. *)
Definition sigma_closed_issmall@{i j | } {A : Type@{j}}
  (B : A -> Type@{j}) (sA : IsSmall@{i j} A)
  (sB : forall a, IsSmall@{i j} (B a))
  : IsSmall@{i j} { a : A & B a }.
Proof.
  exists { a : (smalltype sA) & (smalltype (sB (equiv_smalltype sA a))) }.
  snrapply equiv_functor_sigma'; intros; apply equiv_smalltype.
Defined.

(** If a map has small codomain and fibers, then the domain is small. *)
Definition issmall_codomain_fibers_small@{i j | } {X Y : Type@{j}}
  (f : X -> Y)
  (sY : IsSmall@{i j} Y)
  (sF : forall y : Y, IsSmall@{i j} (hfiber f y))
  : IsSmall@{i j} X.
Proof.
  nrapply issmall_equiv_issmall.
  - exact (equiv_fibration_replacement f)^-1%equiv.
  - apply sigma_closed_issmall; assumption.
Defined.

(** Every contractible type is small. *)
Definition issmall_contr@{i j| } (X : Type@{j}) (T : IsTrunc (-2) X): IsSmall@{i j} X.
Proof.
  refine (issmall_equiv_issmall (equiv_contr_unit)^-1 _).
  apply issmall_in@{i i}.
Defined.

(** If we can show that [X] is small when it is inhabited, then it is in fact small. This isn't yet in the paper. It lets us simplify the statement of Proposition 2.8. Note that this implies propositional resizing, so the [PropResizing] assumption is necessary. *)
(* Definition issmall_inhabited_issmall@{i j k | i < k, j <= k} `{PropResizing} `{Univalence}
  (X : Type@{j})
  (isX : X -> IsSmall@{i j} X)
  : IsSmall@{i j} X.
Proof.
  (* Since IsSmall@{i j} lives in a universe larger than [i] and we're not assuming [i <= j], we have to pass through universe [k], which we think of as max(i+1,j). *)
  apply lower_issmall@{i j k}.
  (* Now the goal is IsSmall@{i k} X. *)
  apply (issmall_codomain_fibers_small isX).
  - rapply issmall_hprop.
  - intro sX.
    apply sigma_closed_issmall.
    1: apply (lift_issmall _ sX).
    intro x.
    rapply issmall_contr.
Defined. *)

(** * Locally small types *)

(** We say that a type [X] is 0-locally small if it is small, and (n+1)-locally small if its identity types are n-locally small. *)
(* TODO: Can I make this an inductive type and avoid the extra universe variable [k]? *)
Fixpoint IsLocallySmall@{i j k | i < k, j <= k} (n : nat) (X : Type@{j}) : Type@{k}
  := match n with
    | 0%nat => IsSmall@{i j} X
    | S m => forall x y : X, IsLocallySmall m (x = y)
    end.

Global Instance ishprop_islocally_small@{i j k | i < k, j <= k} `{Univalence}
  (n : nat) (X : Type@{j})
  : IsHProp@{k} (IsLocallySmall@{i j k} n X).
Proof.
  (* Here and later we use [simple_induction] to control the universe variable. *)
  revert X; simple_induction n n IHn; exact _.
Defined.

(** A small type is n-locally small for all [n]. *)
Definition islocally_small_in@{i j k | i <= j, j <= k, i < k} (n : nat) (X : Type@{i})
  : IsLocallySmall@{i j k} n X.
Proof.
  revert X.
  induction n; intro X.
  - apply issmall_in.
  - intros x y.
    exact (IHn (x = y)).
Defined.

(** The n-locally small types are closed under equivalence. *)
Definition islocally_small_equiv_islocally_small@{i j1 j2 k | i < k, j1 <= k, j2 <= k}
  (n : nat) {A : Type@{j1}} {B : Type@{j2}}
  (e : A <~> B) (lsA : IsLocallySmall@{i j1 k} n A)
  : IsLocallySmall@{i j2 k} n B.
Proof.
  revert A B e lsA.
  simple_induction n n IHn.
  - exact @issmall_equiv_issmall.
  - intros A B e lsA b b'.
    nrapply IHn.
    * exact (equiv_ap' (e^-1%equiv) b b')^-1%equiv.
    * apply lsA.
Defined.

(** A small type is n-locally small for all n. *)
Definition islocally_small_small@{i j k | i < k, j <= k} (n : nat)
  (X : Type@{j}) (sX : IsSmall@{i j} X)
  : IsLocallySmall@{i j k} n X.
Proof.
  apply (islocally_small_equiv_islocally_small n (equiv_smalltype sX)).
  apply islocally_small_in.
Defined.

(** If a type is n-locally small, then it is (n+1)-locally small. *)
Definition islocally_small_succ@{i j k | i < k, j <= k} (n : nat)
  (X : Type@{j}) (lsX : IsLocallySmall@{i j k} n X)
  : IsLocallySmall@{i j k} n.+1 X.
Proof.
  revert X lsX; simple_induction n n IHn; intros X.
  - apply islocally_small_small.
  - intro lsX.
    intros x y.
    apply IHn, lsX.
Defined.

(** The n-locally small types are closed under dependent sums. *)
Definition sigma_closed_islocally_small@{i j k | i < k, j <= k}
  (n : nat) {A : Type@{j}} (B : A -> Type@{j})
  (lsA : IsLocallySmall@{i j k} n A)
  (lsB : forall a, IsLocallySmall@{i j k} n (B a))
  : IsLocallySmall@{i j k} n { a : A & B a }.
Proof.
  revert A B lsA lsB.
  simple_induction n n IHn.
  - exact @sigma_closed_issmall.
  - intros A B lsA lsB x y.
    apply (islocally_small_equiv_islocally_small n (equiv_path_sigma _ x y)).
    apply IHn.
    * apply lsA.
    * intro p.
      apply lsB.
Defined.

(** If a map has n-locally small codomain and fibers, then the domain is n-locally small. *)
Definition islocally_small_codomain_fibers_locally_small@{i j k | i < k, j <= k}
  (n : nat) {X Y : Type@{j}} (f : X -> Y)
  (sY : IsLocallySmall@{i j k} n Y)
  (sF : forall y : Y, IsLocallySmall@{i j k} n (hfiber f y))
  : IsLocallySmall@{i j k} n X.
Proof.
  nrapply islocally_small_equiv_islocally_small.
  - exact (equiv_fibration_replacement f)^-1%equiv.
  - apply sigma_closed_islocally_small; assumption.
Defined.

(** Sends a trunc_index [n] to the natural number [n+2]. *)
Fixpoint trunc_index_to_nat (n : trunc_index) : nat
  := match n with
    | minus_two => 0
    | n'.+1 => (trunc_index_to_nat n').+1
    end.

Notation "n ..+2" := (trunc_index_to_nat n) (at level 2) : trunc_scope.

(** Under propositional resizing, every (n+1)-truncated type is (n+2)-locally small. This is Lemma 2.3 in the paper. *)
(* Definition islocally_small_trunc@{i j k | i < k, j <= k} `{PropResizing}
  (n : trunc_index) (X : Type@{j}) (T : IsTrunc n.+1 X)
  : IsLocallySmall@{i j k} n..+2 X.
Proof.
  revert n X T.
  simple_induction n n IHn; cbn.
  - nrapply issmall_hprop.
  - intros X T x y.
    rapply IHn.
Defined. *)
