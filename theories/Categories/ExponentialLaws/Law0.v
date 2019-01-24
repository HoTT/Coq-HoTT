(** * Exponential laws about the initial category *)
Require Import Category.Core Functor.Core FunctorCategory.Core Functor.Identity Functor.Composition.Core.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Functors InitialTerminalCategory.NaturalTransformations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

(** In this file, we prove that

      - [x⁰ ≅ 1]
      - [0ˣ ≅ 0] if [x ≠ 0]
      - [0⁰ ≅ 1]
 *)


(** ** x⁰ ≅ 1 *)
Section law0.
  Context `{Funext}.
  Context `{IsInitialCategory zero}.
  Context `{IsTerminalCategory one}.
  Local Notation "0" := zero : category_scope.
  Local Notation "1" := one : category_scope.

  Variable C : PreCategory.

  Global Instance IsTerminalCategory_functors_from_initial
  : IsTerminalCategory (0 -> C) := {}.

  (** There is only one functor to the terminal category [1]. *)
  Definition functor : Functor (0 -> C) 1
    := center _.

  (** We have already proven in [InitialTerminalCategory.v] that [0 -> C] is a terminal category, so there is only one functor to it. *)
  Definition inverse : Functor 1 (0 -> C)
    := center _.

  (** Since the objects and morphisms in terminal categories are contractible, functors to a terminal category are also contractible, by [trunc_functor]. *)
  Definition law
  : functor o inverse = 1
    /\ inverse o functor = 1
    := center _.
End law0.

(** ** [0ˣ ≅ 0] if [x ≠ 0] *)
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

  (** There is exactly one functor from an initial category, and we proved above that if [C] is inhabited, then [C -> 0] is initial. *)
  Definition functor' : Functor (C -> 0) 0
    := center _.

  (** There is exactly one functor from the initial category [0]. *)
  Definition inverse' : Functor 0 (C -> 0)
    := center _.

  (** Since objects and morphisms in an initial category are -1-truncated, so are functors to an initial category. *)
  Definition law'
  : functor' o inverse' = 1
    /\ inverse' o functor' = 1
    := center _.
End law0'.

(** ** [0⁰ ≅ 1] *)
Section law00.
  Context `{Funext}.
  Context `{IsInitialCategory zero}.
  Context `{IsInitialCategory zero'}.
  Context `{IsTerminalCategory one}.
  Local Notation "0" := zero : category_scope.
  Local Notation "00" := zero' : category_scope.
  Local Notation "1" := one : category_scope.

  (** This is just a special case of the first law above. *)

  Definition functor00 : Functor (0 -> 0) 1
    := functor _.

  Definition inverse00 : Functor 1 (0 -> 0)
    := inverse _.

  Definition law00
  : functor00 o inverse00 = 1
    /\ inverse00 o functor00 = 1
    := law _.
End law00.
