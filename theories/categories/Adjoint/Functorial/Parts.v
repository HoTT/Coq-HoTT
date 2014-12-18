(** * Functoriality of the construction of adjunctions from universal morphisms *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Identity Functor.Composition.Core.
Require Import NaturalTransformation.Composition.Core NaturalTransformation.Composition.Laws.
Require Import Functor.Dual NaturalTransformation.Dual Category.Dual.
Require Import Adjoint.Core Adjoint.UnitCounit Adjoint.UnitCounitCoercions Adjoint.Dual.
Require Import HProp Types.Sigma HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope natural_transformation_scope.
Local Open Scope morphism_scope.

Section left.
  (** ** action on morphisms of the construction of a left adjoint to [G] *)
  (** *** functoriality on [C], [D], and [G] *)
  Section also_categories.
    Variables C C' : PreCategory.
    Variable CF : Functor C C'.
    Variables D D' : PreCategory.
    Variable DF : Functor D D'.

    Variable G : Functor D C.
    Variable F : Functor C D.
    Variable A : F -| G.
    Variable G' : Functor D' C'.
    Variable F' : Functor C' D'.
    Variable A' : F' -| G'.
    Variable T : NaturalTransformation (CF o G) (G' o DF).

    Definition left_morphism_of
    : NaturalTransformation (F' o CF) (DF o F).
    Proof.
      refine ((_)
                o (counit A' oR (DF o F))
                o _
                o (F'
                     oL ((T oR F)
                           o _
                           o (CF oL unit A)
                           o _)))%natural_transformation;
      nt_solve_associator.
    Defined.
  End also_categories.

  (** *** functoriality in [G] *)
  Section only_functor.
    Variables C D : PreCategory.

    Variable G : Functor D C.
    Variable F : Functor C D.
    Variable A : F -| G.
    Variable G' : Functor D C.
    Variable F' : Functor C D.
    Variable A' : F' -| G'.
    Variable T : NaturalTransformation G G'.

    Definition left_morphism_of_nondep
    : NaturalTransformation F' F.
    Proof.
      refine (_ o (@left_morphism_of C C 1 D D 1 G F A G' F' A' (_ o T o _)) o _)%natural_transformation;
      nt_solve_associator.
    Defined.
  End only_functor.
End left.

Section right.
  (** ** action on morphisms of the construction of a right adjoint to [F] *)
  Definition right_morphism_of
             C C' CF
             D D' DF
             (F : Functor C D) (G : Functor D C) (A : F -| G)
             (F' : Functor C' D') (G' : Functor D' C') (A' : F' -| G')
             (T : NaturalTransformation (F' o CF) (DF o F))
  : NaturalTransformation (CF o G) (G' o DF)
    := (@left_morphism_of _ _ DF^op _ _ CF^op F^op G^op A^op F'^op G'^op A'^op T^op)^op.

  Definition right_morphism_of_nondep
             C D
             (F : Functor C D) (G : Functor D C) (A : F -| G)
             (F' : Functor C D) (G' : Functor D C) (A' : F' -| G')
             (T : NaturalTransformation F' F)
  : NaturalTransformation G G'
    := (@left_morphism_of_nondep _ _ F^op G^op A^op F'^op G'^op A'^op T^op)^op.
End right.
