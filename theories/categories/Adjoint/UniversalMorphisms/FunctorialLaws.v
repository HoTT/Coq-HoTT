(** * Functoriality of the construction of adjunctions from universal morphisms *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Identity Functor.Composition.Core.
Require Import NaturalTransformation.Composition.Core NaturalTransformation.Composition.Laws.
Require Import NaturalTransformation.Identity.
Require Import NaturalTransformation.Paths.
Require Import Functor.Dual NaturalTransformation.Dual Category.Dual.
Require Import Adjoint.Core Adjoint.UnitCounit Adjoint.UnitCounitCoercions Adjoint.Dual.
Require Import Comma.Core UniversalProperties Comma.Dual InitialTerminalCategory.Core InitialTerminalCategory.Functors.
Require Import Adjoint.UniversalMorphisms.Core Adjoint.UniversalMorphisms.FunctorialParts.
Require Import HProp Types.Sigma HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope natural_transformation_scope.
Local Open Scope morphism_scope.

Section adjunction_from_universal.
  Section initial.
    Local Arguments functor__of__initial_morphism : simpl never.
    Local Arguments unit : simpl never.
    Local Arguments counit : simpl never.

    Section identity_of.
      Context `{Funext}.
      Variable C : PreCategory.
      Variable D : PreCategory.

      Variable G : Functor D C.
      Context `(HM : forall Y, @IsInitialMorphism _ _ Y G (M Y)).

      Definition initial_identity_of
      : @initial_morphism_of C C 1 D D 1 G G 1 M HM M HM
        = ((left_identity_natural_transformation_2 _)
             o (right_identity_natural_transformation_1 _))%natural_transformation.
      Proof.
        apply path_natural_transformation; intro.
        cbn.
        autorewrite with morphism functor.
        apply unit_counit_equation_1.
      Qed.
    End identity_of.
  End initial.

  Section terminal.
    Section identity_of.
      Context `{Funext}.
      Variable C : PreCategory.
      Variable D : PreCategory.

      Variable F : Functor C D.
      Context `(HM : forall X, @IsTerminalMorphism _ _ F X (M X)).

      Definition terminal_identity_of
      : @terminal_morphism_of C C 1 D D 1 F F 1 M HM M HM
        = ((right_identity_natural_transformation_2 _)
             o (left_identity_natural_transformation_1 _))%natural_transformation
        := ap (@NaturalTransformation.Dual.opposite _ _ _ _)
              (@initial_identity_of _ _ _ F^op _ HM).
    End identity_of.
  End terminal.
End adjunction_from_universal.
