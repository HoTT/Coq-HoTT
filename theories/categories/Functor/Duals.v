Require Category.Duals.
Import Category.Duals.Notations.
Require Import Category.Core Functor.Core.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

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
End opposite.

Local Notation "F ^op" := (opposite F) : functor_scope.
Local Notation "F ^op'" := (opposite_inv F) (at level 3) : functor_scope.

Section opposite_involutive.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor C D.

  Local Notation op_op_id := Category.Duals.opposite_involutive.

  Lemma opposite_involutive
  : match op_op_id C in (_ = C), op_op_id D in (_ = D) return Functor C D with
      | idpath, idpath => ((F^op)^op)%functor
    end = F.
  Proof.
    destruct F, C, D; reflexivity.
  Defined.
End opposite_involutive.

Module Export Notations.
  Notation "F ^op" := (opposite F) : functor_scope.
  Notation "F ^op'" := (opposite_inv F) (at level 3) : functor_scope.
End Notations.
