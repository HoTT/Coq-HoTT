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
Section opposite.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition opposite (F : Functor C D) : Functor C^op D^op
    := Build_Functor (C^op) (D^op)
                     (object_of F)
                     (fun s d => morphism_of F (s := d) (d := s))
                     (fun d' d s m1 m2 => composition_of F s d d' m2 m1)
                     (identity_of F).
End opposite.

Local Notation "F ^op" := (opposite F) (at level 3, format "F ^op") : functor_scope.

Section opposite_involutive.
  Local Open Scope functor_scope.

  (** ** [ᵒᵖ] is propositionally involutive *)
  Lemma opposite_involutive C D (F : Functor C D)
  : ((F^op)^op)%functor = F.
  Proof.
    destruct F; reflexivity.
  Defined.
End opposite_involutive.

Module Export FunctorDualNotations.
  Notation "F ^op" := (opposite F) (at level 3, format "F ^op") : functor_scope.
End FunctorDualNotations.
