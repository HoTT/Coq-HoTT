(** * Natural transformations between functors from initial categories and to terminal categories *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.NaturalTransformation.Core HoTT.Categories.Functor.Paths HoTT.Categories.NaturalTransformation.Paths.
Require Import HoTT.Categories.InitialTerminalCategory.Core HoTT.Categories.InitialTerminalCategory.Functors.
Require Import HoTT.Categories.NatCategory HoTT.Basics.Contractible.

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
         (fun x => initial_category_ind _ x)
         (fun x _ _ => initial_category_ind _ x).

  Global Instance trunc_from_initial
         `{Funext}
         `{@IsInitialCategory zero} (F G : Functor zero C)
  : Contr (NaturalTransformation F G).
  Proof.
    refine (Build_Contr _ (from_initial F G) _).
    abstract (
        intros;
        apply path_natural_transformation;
        intro x;
        exact (initial_category_ind _ x)
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
             `{@IsTerminalCategory one H1 H2} (F G : Functor C one)
  : NaturalTransformation F G
    := Build_NaturalTransformation
         F G
         (fun x => center _)
         (fun _ _ _ => path_contr _ _).

  Global Instance trunc_to_terminal
         `{Funext}
         `{@IsTerminalCategory one H1 H2} (F G : Functor C one)
  : Contr (NaturalTransformation F G).
  Proof.
    refine (Build_Contr _ (to_terminal F G) _).
    abstract (path_natural_transformation; exact (contr _)).
  Defined.
End NaturalTransformations.
