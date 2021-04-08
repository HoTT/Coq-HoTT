(** * Functors involving functor categories involving the terminal category *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.FunctorCategory.Core HoTT.Categories.Functor.Identity HoTT.Categories.NaturalTransformation.Core HoTT.Categories.NaturalTransformation.Paths HoTT.Categories.Functor.Composition.Core.
Require Import HoTT.Categories.InitialTerminalCategory.Core HoTT.Categories.InitialTerminalCategory.Functors HoTT.Categories.InitialTerminalCategory.NaturalTransformations.
Require Import HoTT.Basics HoTT.Types.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

Section law1.
  Context `{Funext}.
  Context `{IsInitialCategory zero}.
  Context `{IsTerminalCategory one}.
  Local Notation "0" := zero : category_scope.
  Local Notation "1" := one : category_scope.

  Variable C : PreCategory.

  (** ** [C¹ → C] *)
  Definition functor : Functor (1 -> C) C
    := Build_Functor (1 -> C) C
                     (fun F => F (center _))
                     (fun s d m => m (center _))
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Definition inverse_morphism_of
             s d (m : morphism C s d)
  : morphism (1 -> C)
             (Functors.from_terminal _ s)
             (Functors.from_terminal _ d).
  Proof.
    refine (Build_NaturalTransformation
              (Functors.from_terminal _ s)
              (Functors.from_terminal _ d)
              (fun _ => m)
              _).
    simpl; intros.
    etransitivity;
      [ apply right_identity
      | symmetry; apply left_identity ].
  Defined.

  Global Arguments inverse_morphism_of / _ _ _.

  (** ** [C → C¹] *)
  Definition inverse : Functor C (1 -> C).
  Proof.
    refine (Build_Functor
              C (1 -> C)
              (@Functors.from_terminal _ _ _ _ _)
              inverse_morphism_of
              _
              _
           );
    abstract (path_natural_transformation; trivial).
  Defined.
End law1.

Section law1'.
  Context `{Funext}.
  Context `{IsInitialCategory zero}.
  Context `{IsTerminalCategory one}.
  Local Notation "0" := zero : category_scope.
  Local Notation "1" := one : category_scope.

  Variable C : PreCategory.

  Global Instance: IsTerminalCategory (C -> 1) := {}.

  (** ** [1ˣ → 1] *)
  Definition functor' : Functor (C -> 1) 1
    := Functors.to_terminal _.

  (** ** [1 → 1ˣ] *)
  Definition inverse' : Functor 1 (C -> 1)
    := Functors.to_terminal _.

  (** ** [1ˣ ≅ 1] *)
  Definition law'
  : functor' o inverse' = 1
    /\ inverse' o functor' = 1
    := center _.
End law1'.
