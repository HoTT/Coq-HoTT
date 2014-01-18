Require Category.Dual.
Import Category.Dual.CategoryDualNotations.
Require Import Category.Core Functor.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

Section opposite.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition opposite (F : Functor C D) : Functor C^op D^op
    := Build_Functor (C^op) (D^op)
                     (object_of F)
                     (fun s d => morphism_of F (s := d) (d := s))
                     (fun d' d s m1 m2 => composition_of F s d d' m2 m1)
                     (identity_of F).

  (** I wish Coq had η conversion for records, so we wouldn't need this
      nonsense. *)
  Definition opposite_inv (F : Functor C^op D^op) : Functor C D
    := Build_Functor C D
                     (object_of F)
                     (fun s d => morphism_of F (s := d) (d := s))
                     (fun d' d s m1 m2 => composition_of F s d d' m2 m1)
                     (identity_of F).

  Definition opposite_invL (F : Functor C^op D) : Functor C D^op
    := Build_Functor C (D^op)
                     (object_of F)
                     (fun s d => morphism_of F (s := d) (d := s))
                     (fun d' d s m1 m2 => composition_of F s d d' m2 m1)
                     (identity_of F).

  Definition opposite_invR (F : Functor C D^op) : Functor C^op D
    := Build_Functor (C^op) D
                     (object_of F)
                     (fun s d => morphism_of F (s := d) (d := s))
                     (fun d' d s m1 m2 => composition_of F s d d' m2 m1)
                     (identity_of F).
End opposite.

Local Notation "F ^op" := (opposite F) : functor_scope.
Local Notation "F ^op'" := (opposite_inv F) (at level 3) : functor_scope.
Local Notation "F ^op'L" := (opposite_invL F) (at level 3) : functor_scope.
Local Notation "F ^op'R" := (opposite_invR F) (at level 3) : functor_scope.

Section opposite_involutive.
  Local Open Scope functor_scope.

  Local Notation op_op_id := Category.Dual.opposite_involutive.

  Lemma opposite_involutive C D (F : Functor C D)
  : match op_op_id C in (_ = C), op_op_id D in (_ = D) return Functor C D with
      | idpath, idpath => ((F^op)^op)%functor
    end = F.
  Proof.
    destruct F, C, D; reflexivity.
  Defined.

  Lemma opposite_law C D (F : Functor C D)
  : F^op^op' = F.
  Proof.
    destruct F; reflexivity.
  Defined.

  Lemma opposite'_law C D (F : Functor C^op D^op)
  : F^op'^op = F.
  Proof.
    destruct F; reflexivity.
  Defined.

  Lemma opposite'LR_law C D (F : Functor C^op D)
  : F^op'L^op'R = F.
  Proof.
    destruct F; reflexivity.
  Defined.

  Lemma opposite'RL_law C D (F : Functor C D^op)
  : F^op'R^op'L = F.
  Proof.
    destruct F; reflexivity.
  Defined.
End opposite_involutive.

Module Export FunctorDualNotations.
  Notation "F ^op" := (opposite F) : functor_scope.
  Notation "F ^op'" := (opposite_inv F) (at level 3) : functor_scope.
  Notation "F ^op'L" := (opposite_invL F) (at level 3) : functor_scope.
  Notation "F ^op'R" := (opposite_invR F) (at level 3) : functor_scope.
End FunctorDualNotations.
