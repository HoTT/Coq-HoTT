(** * Dual functor categories *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.NaturalTransformation.Core.
Require Import HoTT.Categories.Category.Dual HoTT.Categories.Functor.Dual HoTT.Categories.NaturalTransformation.Dual.
Require Import HoTT.Categories.Functor.Composition.Core HoTT.Categories.Functor.Identity.
Require Import HoTT.Categories.FunctorCategory.Core.
Require Import HoTT.Categories.Functor.Paths.
Require Import HoTT.Tactics HoTT.Types.Forall.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

Section opposite.
  Context `{Funext}.

  (** ** Functors [(C → D) ↔ (Cᵒᵖ → Dᵒᵖ)ᵒᵖ] *)
  Definition opposite_functor (C D : PreCategory) : Functor (C -> D) (C^op -> D^op)^op
    := Build_Functor
         (C -> D) ((C^op -> D^op)^op)
         (fun F => F^op)%functor
         (fun _ _ T => T^op)%natural_transformation
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Local Ltac op_t C D :=
    split;
    path_functor;
    repeat (apply path_forall; intro);
    simpl;
    destruct_head NaturalTransformation;
    exact idpath.

  (** ** The above functors are isomorphisms *)
  Definition opposite_functor_law C D
  : opposite_functor C D o (opposite_functor C^op D^op)^op = 1
    /\ (opposite_functor C^op D^op)^op o opposite_functor C D = 1.
  Proof.
    op_t C D.
  Qed.
End opposite.
