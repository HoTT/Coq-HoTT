(** * Pseudofunctors from initial and terminal categories *)
Require Import Category.Core Functor.Core.
Require Import Functor.Identity.
Require Import Pseudofunctor.Core.
Require Import InitialTerminalCategory.Core.
Require Import FunctorCategory.Morphisms.
Require Import NaturalTransformation.Paths.
Require Import NatCategory.
Require Import PathGroupoids.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Section pseudofunctors.
  (** ** Constant functor from any terminal category *)
  Definition from_terminal `{Funext} `{@IsTerminalCategory one Hone Hone'}
             (c : PreCategory)
  : Pseudofunctor one.
  Proof.
    refine (Build_Pseudofunctor
              one
              (fun _ => c)
              (fun _ _ _ => 1%functor)
              (fun _ _ _ _ _ => reflexivity _)
              (fun _ => reflexivity _)
              _
              _
              _);
      simpl;
      abstract (
          intros;
          path_natural_transformation;
          rewrite ap_const; simpl;
          reflexivity
        ).
  Defined.

  (** *** Functor from any initial category *)
  Definition from_initial `{Funext} `{@IsInitialCategory zero}
  : Pseudofunctor zero
    := Build_Pseudofunctor
         zero
         (fun x => initial_category_ind _ x)
         (fun x _ _ => initial_category_ind _ x)
         (fun x _ _ _ _ => initial_category_ind _ x)
         (fun x => initial_category_ind _ x)
         (fun x => initial_category_ind _ x)
         (fun x => initial_category_ind _ x)
         (fun x => initial_category_ind _ x).
End pseudofunctors.

Local Arguments from_terminal / .
Local Arguments from_initial / .

Definition from_1 `{Funext} c : Pseudofunctor 1
  := Eval simpl in from_terminal c.
Definition from_0 `{Funext} : Pseudofunctor 0
  := Eval simpl in from_initial.

Local Notation "! x" := (@from_terminal _ terminal_category _ _ _ x) : pseudofunctor_scope.

Module Export InitialTerminalCategoryPseudofunctorsNotations.
  Notation "! x" := (@from_terminal _ terminal_category _ _ _ x) : pseudofunctor_scope.
End InitialTerminalCategoryPseudofunctorsNotations.
