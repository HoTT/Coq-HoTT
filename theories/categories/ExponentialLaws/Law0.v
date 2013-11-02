Require Import Category.Core Functor.Core FunctorCategory.Core Functor.Identity Functor.Composition.
Require Import InitialTerminalCategory.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

Section law0.
  Context `{Funext}.
  Context `{IsInitialCategory zero}.
  Context `{IsTerminalCategory one}.
  Local Notation "0" := zero : category_scope.
  Local Notation "1" := one : category_scope.

  Variable C : PreCategory.

  Global Instance IsTerminalCategory_functors_from_initial
  : IsTerminalCategory (0 -> C).

  Definition functor : Functor (0 -> C) 1
    := center _.

  Definition inverse : Functor 1 (0 -> C)
    := center _.

  Definition law
  : functor o inverse = 1
    /\ inverse o functor = 1
    := center _.
End law0.

Section law0'.
  Context `{Funext}.
  Context `{IsInitialCategory zero}.
  Context `{IsTerminalCategory one}.
  Local Notation "0" := zero : category_scope.
  Local Notation "1" := one : category_scope.

  Variable C : PreCategory.
  Variable c : C.

  Local Instance IsInitialCategory_functors_to_initial_from_inhabited
  : IsInitialCategory (C -> 0)
    := fun P F => @Functors.to_initial_category_empty C _ _ F P c.

  Definition functor' : Functor (C -> 0) 0
    := center _.

  Definition inverse' : Functor 0 (C -> 0)
    := center _.

  Definition law'
  : functor' o inverse' = 1
    /\ inverse' o functor' = 1
    := center _.
End law0'.

Section law00.
  Context `{Funext}.
  Context `{IsInitialCategory zero}.
  Context `{IsInitialCategory zero'}.
  Context `{IsTerminalCategory one}.
  Local Notation "0" := zero : category_scope.
  Local Notation "00" := zero' : category_scope.
  Local Notation "1" := one : category_scope.

  Local Instance IsTerminalCategory_functors_to_initial_from_initial
  : IsTerminalCategory (0 -> 00)
    := _.

  Definition functor00 : Functor (0 -> 0) 1
    := center _.

  Definition inverse00 : Functor 1 (0 -> 0)
    := center _.

  Definition law00
  : functor00 o inverse00 = 1
    /\ inverse00 o functor00 = 1
    := center _.
End law00.
