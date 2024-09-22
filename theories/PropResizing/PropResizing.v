Require Import Basics.Overture Basics.Tactics Basics.Trunc Basics.Equivalences
  Types.Universe Nat.Core.
Require Import Universes.Smallness.

Set Universe Minimization ToSet.

(** * Propositional resizing *)

Local Open Scope path_scope.

(** See the note by [Funext] in Overture.v regarding classes for axioms *)
Monomorphic Axiom PropResizing : Type0.
Existing Class PropResizing.

(** Mark this axiom as a "global axiom", which some of our tactics will automatically handle. *)
Global Instance is_global_axiom_propresizing : IsGlobalAxiom PropResizing := {}.

(** Propositional resizing says that every (-1)-truncated type is small. *)
Axiom issmall_hprop@{i j | } : forall `{PropResizing} (X : Type@{j})
  (T : IsHProp X), IsSmall@{i j} X.

(** TODO: inline and remove *)
Definition resize_hprop@{j i | } `{PropResizing} (A : Type@{j}) `{IsHProp A}
  : Type@{i}
  := smalltype@{i j} (issmall_hprop@{i j} A _).

(** TODO: inline and remove *)
Definition equiv_resize_hprop@{j i | } `{PropResizing} (A : Type@{j}) `{IsHProp A}
  : A <~> resize_hprop A
  := (equiv_smalltype@{i j} (issmall_hprop@{i j} A _))^-1%equiv.

Global Instance ishprop_resize_hprop
       `{PropResizing} (A : Type) `{IsHProp A}
  : IsHProp (resize_hprop A)
  := istrunc_equiv_istrunc A (equiv_resize_hprop A).

(** If we can show that [X] is small when it is inhabited, then it is in fact small. This isn't yet in the paper. It lets us simplify the statement of Proposition 2.8. Note that this implies propositional resizing, so the [PropResizing] assumption is necessary. *)
Definition issmall_inhabited_issmall@{i j k | i < k, j <= k} `{PropResizing} `{Univalence}
  (X : Type@{j})
  (isX : X -> IsSmall@{i j} X)
  : IsSmall@{i j} X.
Proof.
  (* Since [IsSmall] is cumulative, it suffices to prove [IsSmall@{i k} X] for [k] the universe that [IsSmall@{i j}] lives in.  We think of [k] as max(i+1,j). *)
  apply (issmall_codomain_issmall_fibers@{i k} isX).
  - nrefine (issmall_hprop@{i k} _ _).
    nrapply ishprop_issmall@{i k k}.
  - intro sX.
    apply sigma_closed_issmall@{i k}.
    1: exact sX.
    intro x.
    nrapply issmall_contr@{i k}.
    nrapply istrunc_paths@{k}.
    nrapply ishprop_issmall@{i k k}.
Defined.

(** Sends a trunc_index [n] to the natural number [n+2]. *)
Fixpoint trunc_index_to_nat (n : trunc_index) : nat
  := match n with
    | minus_two => 0%nat
    | n'.+1 => (trunc_index_to_nat n').+1
    end.

Notation "n ..+2" := (trunc_index_to_nat n) (at level 2) : trunc_scope.

(** Under propositional resizing, every (n+1)-truncated type is (n+2)-locally small. This is Lemma 2.3 in the paper. *)
Definition islocallysmall_trunc@{i j k | i < k, j <= k} `{PropResizing}
  (n : trunc_index) (X : Type@{j}) (T : IsTrunc n.+1 X)
  : IsLocallySmall@{i j k} n..+2 X.
Proof.
  revert n X T.
  simple_induction n n IHn; cbn.
  - nrapply issmall_hprop@{i j}.
  - intros X T x y.
    rapply IHn.
Defined.
