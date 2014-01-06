Require Import Category.Core DiscreteCategory IndiscreteCategory.
Require Import types.Unit Trunc types.Sum types.Empty.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Module Export Core.
  Fixpoint CardinalityRepresentative (n : nat) : Set :=
    match n with
      | 0 => Empty
      | 1 => Unit
      | S n' => (CardinalityRepresentative n' + Unit)%type
    end.

  Coercion CardinalityRepresentative : nat >-> Sortclass.

  Instance trunc_cardinality_representative (n : nat)
  : IsHSet (CardinalityRepresentative n).
  Proof.
    induction n; [ typeclasses eauto |].
    induction n; [ typeclasses eauto |].
    intros [x|x] [y|y];
      typeclasses eauto.
  Qed.

  Definition nat_category (n : nat) :=
    match n with
      | 0 => indiscrete_category 0
      | 1 => indiscrete_category 1
      | S (S n') => discrete_category (S (S n'))
    end.

  Coercion nat_category : nat >-> PreCategory.

  Module Export NatCategoryCoreNotations.
    Notation "1" := (nat_category 1) : category_scope.
  End NatCategoryCoreNotations.

  Typeclasses Transparent nat_category.
  Hint Unfold nat_category.
  Arguments nat_category / .
End Core.

Module Notations.
  Include Core.NatCategoryCoreNotations.
End Notations.
