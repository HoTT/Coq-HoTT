(** * Functors to and from initial and terminal categories *)
Require Import Category.Core Functor.Core Functor.Paths.
Require Import InitialTerminalCategory.Core.
Require Import NatCategory Contractible.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Section functors.
  Variable C : PreCategory.

  (** *** Functor to any terminal category *)
  Definition to_terminal `{@IsTerminalCategory one Hone Hone'}
  : Functor C one
    := Build_Functor
         C one
         (fun _ => center _)
         (fun _ _ _ => center _)
         (fun _ _ _ _ _ => contr _)
         (fun _ => contr _).

  (** *** Constant functor from any terminal category *)
  Definition from_terminal `{@IsTerminalCategory one Hone Hone'} (c : C)
  : Functor one C
    := Build_Functor
         one C
         (fun _ => c)
         (fun _ _ _ => identity c)
         (fun _ _ _ _ _ => symmetry _ _ (@identity_identity _ _))
         (fun _ => idpath).

  (** *** Functor from any initial category *)
  Definition from_initial `{@IsInitialCategory zero}
  : Functor zero C
    := Build_Functor
         zero C
         (fun x => initial_category_rect _ x)
         (fun x _ _ => initial_category_rect _ x)
         (fun x _ _ _ _ => initial_category_rect _ x)
         (fun x => initial_category_rect _ x).
End functors.

Local Arguments to_terminal / .
Local Arguments from_terminal / .
Local Arguments from_initial / .

Definition to_1 C : Functor C 1
  := Eval simpl in to_terminal C.
Definition from_1 C c : Functor 1 C
  := Eval simpl in from_terminal C c.
Definition from_0 C : Functor 0 C
  := Eval simpl in from_initial C.

Local Notation "! x" := (from_terminal _ x) (at level 3) : functor_scope.

(** *** Uniqueness principles about initial and terminal categories and functors *)
Section unique.
  Context `{Funext}.

  Global Instance trunc_initial_category_function
         `{@IsInitialCategory zero} T
  : Contr (zero -> T) :=
    let x := {| center x := initial_category_rect _ x |} in x.
  Proof.
    intro y.
    apply path_forall; intro x.
    apply (initial_category_rect _ x).
  Defined.

  Variable C : PreCategory.

  Global Instance trunc_initial_category
         `{@IsInitialCategory zero}
  : Contr (Functor zero C)
    := let x := {| center := from_initial C |} in x.
  Proof.
    abstract (
        intros; apply path_functor'_sig;
        (exists (center _));
        apply path_forall; intro x;
        apply (initial_category_rect _ x)
      ).
  Defined.

  Global Instance trunc_to_initial_category
         `{@IsInitialCategory zero}
  : IsHProp (Functor C zero).
  Proof.
    typeclasses eauto.
  Qed.

  Definition to_initial_category_empty
             `{@IsInitialCategory zero}
             (F : Functor C zero)
  : IsInitialCategory C
    := fun P x => initial_category_rect P (F x).

  Global Instance trunc_terminal_category
         `{@IsTerminalCategory one H0 H1}
  : Contr (Functor C one)
    := let x := {| center := to_terminal C |} in x.
  Proof.
    intros.
    exact (center _).
  Defined.
End unique.

Module Export InitialTerminalCategoryFunctorsNotations.
  Notation "! x" := (from_terminal _ x) : functor_scope.
End InitialTerminalCategoryFunctorsNotations.
