(** * Opposite functors *)
Require Category.Dual.
Import Category.Dual.CategoryDualNotations.
Require Import Category.Core Functor.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

(** ** Definition of [Fᵒᵖ] *)
Definition opposite C D (F : Functor C D) : Functor C^op D^op
  := Build_Functor (C^op) (D^op)
                   (object_of F)
                   (fun s d (m : morphism C^op s d) => (F _1 m)%morphism)
                   (fun d' d s m1 m2 => composition_of F s d d' m2 m1)
                   (identity_of F).

Local Notation "F ^op" := (opposite F) : functor_scope.

Local Open Scope functor_scope.

(** ** [ᵒᵖ] is judgmentally involutive *)
Definition opposite_involutive C D (F : Functor C D) : (F^op)^op = F
  := idpath.

Module Export FunctorDualNotations.
  Notation "F ^op" := (opposite F) : functor_scope.
End FunctorDualNotations.
