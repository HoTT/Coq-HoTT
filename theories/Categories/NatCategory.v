(** * Discrete categories on [n] objects *)
Require Import Category.Core DiscreteCategory IndiscreteCategory.
Require Import Types.Unit Trunc Types.Sum Types.Empty.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Local Open Scope nat_scope.

Module Export Core.
  (** ** [Fin n] types, or [CardinalityRepresentative] *)
  (** We use [Empty] for [0] and [Unit] for [1] so that we get nice judgmental behavior.
      TODO: this should be unified with [Spaces.Finite.Fin].
   *)
  Fixpoint CardinalityRepresentative (n : nat) : Type0 :=
    match n with
      | 0 => Empty
      | 1 => Unit
      | S n' => (CardinalityRepresentative n' + Unit)%type
    end.

  Coercion CardinalityRepresentative : nat >-> Sortclass.

  (** ** [Fin n] is an hSet *)
  Global Instance trunc_cardinality_representative (n : nat)
  : IsHSet (CardinalityRepresentative n).
  Proof.
    induction n; [ typeclasses eauto |].
    induction n; [ typeclasses eauto |].
    intros [x|x] [y|y];
      typeclasses eauto.
  Qed.

  (** ** Define the categories [n] *)
  Definition nat_category (n : nat) :=
    match n with
      | 0 => indiscrete_category 0
      | 1 => indiscrete_category 1
      | S (S n') => discrete_category (S (S n'))
    end.

  Coercion nat_category : nat >-> Category.

  Module Export NatCategoryCoreNotations.
    Notation "1" := (nat_category 1) : category_scope.
  End NatCategoryCoreNotations.

  Typeclasses Transparent nat_category.
  Hint Unfold nat_category : core.
  Arguments nat_category / .
End Core.

Module Notations.
  Include Core.NatCategoryCoreNotations.
End Notations.
