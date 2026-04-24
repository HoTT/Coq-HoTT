(** * Grothendieck Construction of a functor to Cat *)
Require Import Category.Core Functor.Core.
Require Import Pseudofunctor.FromFunctor.
Require Import Cat.Core.
Require Import Grothendieck.PseudofunctorToCat.

Set Implicit Arguments.
Generalizable All Variables.

Local Open Scope morphism_scope.

Section Grothendieck.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  (*Context `{forall C, IsHProp (P C)}.*)
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation cat := (@sub_pre_cat _ P HF).

  Variable C : PreCategory.
  Variable F : Functor C cat.

  (** ** Category of elements *)
  Definition category : PreCategory
    := category (pseudofunctor_of_functor_to_cat F).

  (** ** First projection functor *)
  Definition pr1 : Functor category C
    := pr1 (pseudofunctor_of_functor_to_cat F).
End Grothendieck.
