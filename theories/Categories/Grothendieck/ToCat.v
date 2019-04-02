(** * Grothendieck Construction of a functor to Cat *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Pseudofunctor.Core Pseudofunctor.FromFunctor.
Require Import Cat.Core.
Require Import Grothendieck.PseudofunctorToCat.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section Grothendieck.
  Context `{Funext}.

  Variable P : Category -> Type.
  (*Context `{forall C, IsHProp (P C)}.*)
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation cat := (@sub_pre_cat _ P HF).

  Variable C : Category.
  Variable F : Functor C cat.

  (** ** Category of elements *)
  Definition category : Category
    := category (F : FunctorToCat).

  (** ** First projection functor *)
  Definition pr1 : Functor category C
    := pr1 (F : FunctorToCat).
End Grothendieck.
