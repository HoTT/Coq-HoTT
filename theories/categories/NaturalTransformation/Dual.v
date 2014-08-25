(** * Opposite natural transformations *)
Require Category.Dual Functor.Dual.
Import Category.Dual.CategoryDualNotations Functor.Dual.FunctorDualNotations.
Require Import Category.Core Functor.Core NaturalTransformation.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

(** ** Definition of [Tᵒᵖ], and some variants that strip off [ᵒᵖ]s *)
Section opposite.
  Variable C : PreCategory.
  Variable D : PreCategory.

  (** If we had judgmental eta for records, we wouldn't need all these variants. *)

  Definition opposite
             (F G : Functor C D)
             (T : NaturalTransformation F G)
  : NaturalTransformation G^op F^op
    := Build_NaturalTransformation' (G^op) (F^op)
                                    (components_of T)
                                    (fun s d => commutes_sym T d s)
                                    (fun s d => commutes T d s).

  Definition opposite'
             (F G : Functor C^op D^op)
             (T : NaturalTransformation F G)
  : NaturalTransformation G^op' F^op'
    := Build_NaturalTransformation' (G^op') (F^op')
                                    (components_of T)
                                    (fun s d => commutes_sym T d s)
                                    (fun s d => commutes T d s).

  Definition opposite_finv
             (F G : Functor C^op D^op)
             (T : NaturalTransformation G^op' F^op')
  : NaturalTransformation F G
    := Build_NaturalTransformation' F G
                                    (components_of T)
                                    (fun s d => commutes_sym T d s)
                                    (fun s d => commutes T d s).

  Definition opposite_tinv
             (F G : Functor C D)
             (T : NaturalTransformation G^op F^op)
  : NaturalTransformation F G
    := Build_NaturalTransformation' F G
                                    (components_of T)
                                    (fun s d => commutes_sym T d s)
                                    (fun s d => commutes T d s).
End opposite.

Local Notation "T ^op" := (opposite T) (at level 3, format "T ^op") : natural_transformation_scope.
Local Notation "T ^op'" := (opposite' T) (at level 3, format "T ^op'") : natural_transformation_scope.
Local Notation "T ^op''" := (opposite_finv T) (at level 3, format "T ^op''") : natural_transformation_scope.
Local Notation "T ^op'''" := (opposite_tinv T) (at level 3, format "T ^op'''") : natural_transformation_scope.

(** ** [ᵒᵖ] is propositionally involutive *)
Section opposite_involutive.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variables F G : Functor C D.
  Variable T : NaturalTransformation F G.

  Local Open Scope natural_transformation_scope.

  Local Notation op_op_functor_id := Functor.Dual.opposite_involutive.
  Local Notation op_op_id := Category.Dual.opposite_involutive.

  (** ewww, the transports *)
  Lemma opposite_involutive
  : match op_op_functor_id F in (_ = F), op_op_functor_id G in (_ = G) return
          NaturalTransformation F G
    with
      | idpath, idpath => match op_op_id C as HC, op_op_id D as HD return
                                (NaturalTransformation
                                   (match HC in (_ = C), HD in (_ = D) return Functor C D with
                                      | idpath, idpath => (F ^op) ^op
                                    end)
                                   (match HC in (_ = C), HD in (_ = D) return Functor C D with
                                      | idpath, idpath => (G ^op) ^op
                                    end))
                          with
                            | idpath, idpath => (T ^op) ^op
                          end
    end = T.
  Proof.
    destruct T, F, G, C, D; reflexivity.
  Defined.
End opposite_involutive.

Module Export NaturalTransformationDualNotations.
  Notation "T ^op" := (opposite T) (at level 3, format "T ^op") : natural_transformation_scope.
  Notation "T ^op'" := (opposite' T) (at level 3, format "T ^op'") : natural_transformation_scope.
  Notation "T ^op''" := (opposite_finv T) (at level 3, format "T ^op''") : natural_transformation_scope.
  Notation "T ^op'''" := (opposite_tinv T) (at level 3, format "T ^op'''") : natural_transformation_scope.
End NaturalTransformationDualNotations.
