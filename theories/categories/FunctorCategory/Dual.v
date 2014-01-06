Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual Functor.Dual NaturalTransformation.Dual.
Require Import Functor.Composition.Core Functor.Identity.
Require Import FunctorCategory.Core.
Require Import Functor.Paths.
Require Import HoTT.Tactics types.Forall.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

Section opposite.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition opposite_functor : Functor (C -> D) (C^op -> D^op)^op
    := Build_Functor
         (C -> D) ((C^op -> D^op)^op)
         (fun F => F^op)%functor
         (fun _ _ T => T^op)%natural_transformation
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Definition opposite_functor_inv : Functor (C^op -> D^op)^op (C -> D)
    := Build_Functor
         ((C^op -> D^op)^op) (C -> D)
         (fun F => F^op')%functor
         (fun _ _ T => T^op')%natural_transformation
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Definition opposite_functor' : Functor (C -> D)^op (C^op -> D^op)
    := Build_Functor
         ((C -> D)^op) (C^op -> D^op)
         (fun F => F^op)%functor
         (fun _ _ T => T^op)%natural_transformation
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).


  Definition opposite_functor_inv' : Functor (C^op -> D^op) (C -> D)^op
    := Build_Functor
         (C^op -> D^op) ((C -> D)^op)
         (fun F => F^op')%functor
         (fun _ _ T => T^op')%natural_transformation
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Local Ltac op_t :=
    split;
    path_functor;
    [ (exists (path_forall _ _ (@opposite'_law C D)))
    | (exists (path_forall _ _ (@opposite_law C D))) ];
    repeat (apply path_forall; intro);
    simpl;
    rewrite !transport_forall_constant;
    transport_path_forall_hammer;
    destruct_head NaturalTransformation;
    destruct_head Functor;
    exact idpath.

  Definition opposite_functor_law
  : opposite_functor o opposite_functor_inv = 1
    /\ opposite_functor_inv o opposite_functor = 1.
  Proof.
    abstract op_t.
  Qed.

  Definition opposite_functor'_law
  : opposite_functor' o opposite_functor_inv' = 1
    /\ opposite_functor_inv' o opposite_functor' = 1.
  Proof.
    abstract op_t.
  Qed.
End opposite.
