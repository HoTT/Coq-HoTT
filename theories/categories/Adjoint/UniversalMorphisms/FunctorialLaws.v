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
  Local Ltac try_various_ways tac :=
    progress repeat first [ progress tac
                          | rewrite <- ?Functor.Core.composition_of;
                            progress try_associativity_quick tac
                          | rewrite -> ?Functor.Core.composition_of;
                            progress try_associativity_quick tac ].

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

      Definition initial_identity_of_nondep
      : @initial_morphism_of_nondep C D G G 1 M HM M HM = 1%natural_transformation.
      Proof.
        apply path_natural_transformation; intro.
        cbn.
        autorewrite with morphism functor.
        apply unit_counit_equation_1.
      Qed.
    End identity_of.

    Section composition_of.
      Context `{Funext}.
      (** TODO: How do I write the dependent version? *)
      Variable C : PreCategory.
      Variable D : PreCategory.

      Variable G : Functor D C.
      Variable G' : Functor D C.
      Variable G'' : Functor D C.
      Variable T : NaturalTransformation G G'.
      Variable T' : NaturalTransformation G' G''.
      Context `(HM : forall Y, @IsInitialMorphism _ _ Y G (M Y)).
      Context `(HM' : forall Y, @IsInitialMorphism _ _ Y G' (M' Y)).
      Context `(HM'' : forall Y, @IsInitialMorphism _ _ Y G'' (M'' Y)).

      Local Open Scope natural_transformation_scope.

      Definition initial_composition_of_nondep
      : (@initial_morphism_of_nondep _ _ _ _ (T' o T) _ HM _ HM'')
        = ((initial_morphism_of_nondep T HM HM')
             o (initial_morphism_of_nondep T' HM' HM'')).
      Proof.
        apply path_natural_transformation; intro.
        cbn.
        (** This is suboptimal, because we keep rewriting back and
            forth with associativity and [composition_of].  But it
            only takes 2 seconds total, so it's probably not worth
            optimizing. *)
        repeat match goal with
                 | _ => reflexivity
                 | _ => progress autorewrite with morphism
                 | _ => try_various_ways ltac:f_ap
                 | [ |- context[components_of ?T ?x] ]
                   => try_various_ways ltac:(simpl rewrite <- (commutes T))
                 | [ |- context[unit ?A] ]
                   => try_various_ways ltac:(rewrite (unit_counit_equation_1 A))
                 | [ |- context[unit ?A] ]
                   => try_various_ways ltac:(rewrite (unit_counit_equation_2 A))
               end.
      Qed.
    End composition_of.
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

    Section composition_of.
      Context `{Funext}.
      (** TODO: How do I write the dependent version? *)
      Variable C : PreCategory.
      Variable D : PreCategory.

      Variable F : Functor C D.
      Variable F' : Functor C D.
      Variable F'' : Functor C D.
      Variable T : NaturalTransformation F F'.
      Variable T' : NaturalTransformation F' F''.
      Context `(HM : forall X, @IsTerminalMorphism _ _ F X (M X)).
      Context `(HM' : forall X, @IsTerminalMorphism _ _ F' X (M' X)).
      Context `(HM'' : forall X, @IsTerminalMorphism _ _ F'' X (M'' X)).

      Local Open Scope natural_transformation_scope.

      Definition terminal_composition_of_nondep
      : (@terminal_morphism_of_nondep _ _ _ _ (T' o T) _ HM'' _ HM)
        = ((terminal_morphism_of_nondep T HM' HM)
             o (terminal_morphism_of_nondep T' HM'' HM'))
        := ap (@NaturalTransformation.Dual.opposite _ _ _ _)
              (@initial_composition_of_nondep _ _ _ _ _ _ T'^op T^op _ HM'' _ HM' _ HM).
    End composition_of.
  End terminal.
End adjunction_from_universal.
