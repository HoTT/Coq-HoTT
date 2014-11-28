(** * Functoriality of the construction of adjunctions from universal morphisms *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Identity Functor.Composition.Core.
Require Import NaturalTransformation.Composition.Core NaturalTransformation.Composition.Laws.
Require Import Functor.Dual NaturalTransformation.Dual Category.Dual.
Require Import Adjoint.Core Adjoint.UnitCounit Adjoint.UnitCounitCoercions Adjoint.Dual.
Require Import Comma.Core UniversalProperties Comma.Dual InitialTerminalCategory.Core InitialTerminalCategory.Functors.
Require Import Adjoint.UniversalMorphisms.Core.
Require Import HProp Types.Sigma HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope natural_transformation_scope.
Local Open Scope morphism_scope.

Section initial.
  (** ** action on morphisms of the construction of a left adjoint to [G] from an initial object of [(Y / G)] for all [Y : C] *)
  (** *** functoriality on [C], [D], and [G] *)
  Section also_categories.
    Variable C : PreCategory.
    Variable C' : PreCategory.
    Variable CF : Functor C C'.
    Variable D : PreCategory.
    Variable D' : PreCategory.
    Variable DF : Functor D D'.

    Variable G : Functor D C.
    Variable G' : Functor D' C'.
    Variable T : NaturalTransformation (CF o G) (G' o DF).
    Context `(HM : forall Y, @IsInitialMorphism _ _ Y G (M Y)).
    Context `(HM' : forall Y, @IsInitialMorphism _ _ Y G' (M' Y)).

    Definition initial_morphism_of
    : NaturalTransformation (functor__of__initial_morphism HM' o CF)
                            (DF o functor__of__initial_morphism HM).
    Proof.
      refine ((_)
                o (counit (adjunction__of__initial_morphism HM') oR (DF o functor__of__initial_morphism HM))
                o _
                o ((functor__of__initial_morphism HM')
                     oL ((T oR functor__of__initial_morphism HM)
                           o _
                           o (CF oL unit (adjunction__of__initial_morphism HM))
                           o _)))%natural_transformation;
      nt_solve_associator.
    Defined.
  End also_categories.

  (** *** functoriality in [G] *)
  Section only_functor.
    Variable C : PreCategory.
    Variable D : PreCategory.

    Variable G : Functor D C.
    Variable G' : Functor D C.
    Variable T : NaturalTransformation G G'.
    Context `(HM : forall Y, @IsInitialMorphism _ _ Y G (M Y)).
    Context `(HM' : forall Y, @IsInitialMorphism _ _ Y G' (M' Y)).

    Definition initial_morphism_of_nondep
    : NaturalTransformation (functor__of__initial_morphism HM')
                            (functor__of__initial_morphism HM).
    Proof.
      refine (_ o (@initial_morphism_of C C 1 D D 1 G G' (_ o T o _) _ HM _ HM') o _)%natural_transformation;
      nt_solve_associator.
    Defined.
  End only_functor.
End initial.

Section terminal.
  (** ** action on morphisms of the construction of a right adjoint to [F] from a terminal object of [(F / X)] for all [X : D] *)
  Definition terminal_morphism_of
             C C' CF
             D D' DF
             (F : Functor C D) (F' : Functor C' D')
             (T : NaturalTransformation (F' o CF) (DF o F))
             `(HM : forall X, @IsTerminalMorphism _ _ F X (M X))
             `(HM' : forall X, @IsTerminalMorphism _ _ F' X (M' X))
  : NaturalTransformation (CF o functor__of__terminal_morphism HM)
                          (functor__of__terminal_morphism HM' o DF)
    := (@initial_morphism_of _ _ DF^op _ _ CF^op F^op F'^op T^op _ HM _ HM')^op.

  Definition terminal_morphism_of_nondep
             C D
             (F F' : Functor C D)
             (T : NaturalTransformation F' F)
             `(HM : forall X, @IsTerminalMorphism _ _ F X (M X))
             `(HM' : forall X, @IsTerminalMorphism _ _ F' X (M' X))
  : NaturalTransformation (functor__of__terminal_morphism HM)
                          (functor__of__terminal_morphism HM')
    := (@initial_morphism_of_nondep _ _ F^op F'^op T^op _ HM _ HM')^op.
End terminal.
