(** * Natural transformations between functors from initial categories and to terminal categories *)
Require Import Category.Core Functor.Core NaturalTransformation.Core Functor.Paths NaturalTransformation.Paths.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Functors.
Require Import NatCategory Contractible.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Section NaturalTransformations.
  Variable C : PreCategory.

  Definition from_initial
             `{@IsInitialCategory zero} (F G : Functor zero C)
  : NaturalTransformation F G
    := Build_NaturalTransformation
         F G
         (fun x => initial_category_rect _ x)
         (fun x _ _ => initial_category_rect _ x).

  Global Instance trunc_from_initial
         `{Funext}
         `{@IsInitialCategory zero} (F G : Functor zero C)
  : Contr (NaturalTransformation F G)
    := let x := {| center := from_initial F G |}
       in x.
  Proof.
    abstract (
        intros;
        apply path_natural_transformation;
        intro x;
        exact (initial_category_rect _ x)
      ).
  Defined.

  Local Existing Instance Functors.to_initial_category_empty.

  Global Instance trunc_to_initial
         `{Funext}
         `{@IsInitialCategory zero}
         (F G : Functor zero C)
  : Contr (NaturalTransformation F G)
    := trunc_from_initial F G.

  Definition to_terminal
             `{@IsTerminalCategory one H0 H1} (F G : Functor C one)
  : NaturalTransformation F G
    := Build_NaturalTransformation
         F G
         (fun x => center _)
         (fun _ _ _ => path_contr _ _).

  Global Instance trunc_to_terminal
         `{Funext}
         `{@IsTerminalCategory one H0 H1} (F G : Functor C one)
  : Contr (NaturalTransformation F G)
    := let x := {| center := to_terminal F G |} in x.
  Proof.
    abstract (path_natural_transformation; exact (contr _)).
  Defined.
End NaturalTransformations.
