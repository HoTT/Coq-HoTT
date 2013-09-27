Require Export Category.Duals Functor.Core.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.

Section functor_opposite.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition functor_opposite (F : Functor C D) : Functor C^op D^op
    := Build_Functor (C^op) (D^op)
                     (object_of F)
                     (fun s d => morphism_of F (s := d) (d := s))
                     (fun d' d s m1 m2 => composition_of F s d d' m2 m1)
                     (identity_of F).

  (** I wish Coq had η conversion for records, so we wouldn't need this
      nonsense. *)
  Definition functor_opposite_inv (F : Functor C^op D^op) : Functor C D
    := Build_Functor C D
                     (object_of F)
                     (fun s d => morphism_of F (s := d) (d := s))
                     (fun d' d s m1 m2 => composition_of F s d d' m2 m1)
                     (identity_of F).
End functor_opposite.

Notation "F ^op" := (functor_opposite F) : functor_scope.
Notation "F ^op'" := (functor_opposite_inv F) (at level 3) : functor_scope.

Section functor_opposite_Id.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor C D.

  Lemma op_op_functor_id
  : match op_op_id C in (_ = C), op_op_id D in (_ = D) return Functor C D with
      | idpath, idpath => ((F^op)^op)%functor
    end = F.
  Proof.
    destruct F, C, D; reflexivity.
  Defined.
End functor_opposite_Id.
