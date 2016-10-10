(** * Functoriality of the construction of adjunctions *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Identity Functor.Composition.Core.
Require Import NaturalTransformation.Composition.Core NaturalTransformation.Composition.Laws.
Require Import NaturalTransformation.Identity.
Require Import NaturalTransformation.Paths.
Require Import Functor.Dual NaturalTransformation.Dual Category.Dual.
Require Import Adjoint.Core Adjoint.UnitCounit Adjoint.UnitCounitCoercions Adjoint.Dual.
Require Import Adjoint.Composition.Core.
Require Import Adjoint.Functorial.Parts.
Require Import HProp Types.Sigma HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope natural_transformation_scope.
Local Open Scope morphism_scope.

Section laws.
  (** Some tactics to handle all the proofs.  The tactics deal with
      the "obvious" commutativity requirements by writing back and
      forth with associativity and respectfulness of composition,
      trying to find applications of the adjunction laws. *)
  Local Ltac try_various_ways tac :=
    progress repeat first [ progress tac
                          | rewrite <- ?Functor.Core.composition_of;
                            progress try_associativity_quick tac
                          | rewrite -> ?Functor.Core.composition_of;
                            progress try_associativity_quick tac ].

  (** This is suboptimal, because we keep rewriting back and forth
      with associativity and [composition_of].  But it only takes 0.74
      seconds total, so it's probably not worth optimizing. *)
  Local Ltac handle_laws' :=
    idtac;
    match goal with
      | _ => reflexivity
      | _ => progress rewrite ?identity_of, ?Category.Core.left_identity, ?Category.Core.right_identity
      | _ => try_various_ways ltac:(f_ap)
      | [ |- context[components_of ?T ?x] ]
        => try_various_ways ltac:(simpl rewrite <- (commutes T))
      | [ |- context[unit ?A] ]
        => try_various_ways ltac:(rewrite (unit_counit_equation_1 A))
      | [ |- context[unit ?A] ]
        => try_various_ways ltac:(rewrite (unit_counit_equation_2 A))
    end.

  Local Ltac t :=
    apply path_natural_transformation; intro;
    cbn;
    repeat handle_laws'.

  Section left.
    Local Arguments unit : simpl never.
    Local Arguments counit : simpl never.

    Section identity_of.
      Context `{Funext}.
      Variables C D : PreCategory.

      Variable G : Functor D C.
      Variable F : Functor C D.
      Variable A : F -| G.

      Definition left_identity_of
      : @left_morphism_of C C 1 D D 1 G F A G F A 1
        = ((left_identity_natural_transformation_2 _)
             o (right_identity_natural_transformation_1 _))%natural_transformation.
      Proof. t. Qed.

      Definition left_identity_of_nondep
      : @left_morphism_of_nondep C D G F A G F A 1 = 1%natural_transformation.
      Proof. t. Qed.
    End identity_of.

    Section composition_of_dep.
      Context `{Funext}.
      Variables C C' C'' : PreCategory.
      Variable CF : Functor C C'.
      Variable CF' : Functor C' C''.
      Variables D D' D'' : PreCategory.
      Variable DF : Functor D D'.
      Variable DF' : Functor D' D''.

      Variable G : Functor D C.
      Variable F : Functor C D.
      Variable A : F -| G.
      Variable G' : Functor D' C'.
      Variable F' : Functor C' D'.
      Variable A' : F' -| G'.
      Variable G'' : Functor D'' C''.
      Variable F'' : Functor C'' D''.
      Variable A'' : F'' -| G''.
      Variable T : NaturalTransformation (CF o G) (G' o DF).
      Variable T' : NaturalTransformation (CF' o G') (G'' o DF').

      Local Open Scope natural_transformation_scope.

      Definition left_composition_of
      : (@left_morphism_of
           _ _ _ _ _ _ _ _
           A _ _ A''
           ((associator_1 _ _ _)
              o (T' oR DF)
              o (associator_2 _ _ _)
              o (CF' oL T)
              o (associator_1 _ _ _)))
        = (associator_2 _ _ _)
            o (DF' oL left_morphism_of A A' T)
            o (associator_1 _ _ _)
            o (left_morphism_of A' A'' T' oR CF)
            o (associator_2 _ _ _).
      Proof. t. Qed.
    End composition_of_dep.

    Section composition_of.
      Context `{Funext}.
      Variables C D : PreCategory.

      Variable G : Functor D C.
      Variable F : Functor C D.
      Variable A : F -| G.
      Variable G' : Functor D C.
      Variable F' : Functor C D.
      Variable A' : F' -| G'.
      Variable G'' : Functor D C.
      Variable F'' : Functor C D.
      Variable A'' : F'' -| G''.
      Variable T : NaturalTransformation G G'.
      Variable T' : NaturalTransformation G' G''.

      Local Open Scope natural_transformation_scope.

      Definition left_composition_of_nondep
      : (@left_morphism_of_nondep _ _ _ _ A _ _ A'' (T' o T))
        = ((left_morphism_of_nondep A A' T)
             o (left_morphism_of_nondep A' A'' T')).
      Proof. t. Qed.
    End composition_of.
  End left.

  Section right.
    Section identity_of.
      Context `{Funext}.
      Variables C D : PreCategory.

      Variable F : Functor C D.
      Variable G : Functor D C.
      Variable A : F -| G.

      Definition right_identity_of
      : @right_morphism_of C C 1 D D 1 F G A F G A 1
        = ((right_identity_natural_transformation_2 _)
             o (left_identity_natural_transformation_1 _))%natural_transformation
        := ap (@NaturalTransformation.Dual.opposite _ _ _ _)
              (@left_identity_of _ _ _ F^op G^op A^op).

      Definition right_identity_of_nondep
      : @right_morphism_of_nondep C D F G A F G A 1 = 1%natural_transformation
        := ap (@NaturalTransformation.Dual.opposite _ _ _ _)
              (@left_identity_of_nondep _ _ _ F^op G^op A^op).
    End identity_of.

    Section composition_of_dep.
      Context `{Funext}.
      Variables C C' C'' : PreCategory.
      Variable CF : Functor C C'.
      Variable CF' : Functor C' C''.
      Variables D D' D'' : PreCategory.
      Variable DF : Functor D D'.
      Variable DF' : Functor D' D''.

      Variable F : Functor C D.
      Variable G : Functor D C.
      Variable A : F -| G.
      Variable F' : Functor C' D'.
      Variable G' : Functor D' C'.
      Variable A' : F' -| G'.
      Variable F'' : Functor C'' D''.
      Variable G'' : Functor D'' C''.
      Variable A'' : F'' -| G''.
      Variable T : NaturalTransformation (F' o CF) (DF o F).
      Variable T' : NaturalTransformation (F'' o CF') (DF' o F').

      Local Open Scope natural_transformation_scope.

      (** This is slow, at about 3.8 s.  It also requires the opposite
          association to unify. *)
      Definition right_composition_of
      : right_morphism_of
          A A''
          ((associator_2 DF' DF F)
             o ((DF' oL T)
                  o ((associator_1 DF' F' CF)
                       o ((T' oR CF)
                            o (associator_2 F'' CF' CF)))))
        = (associator_1 G'' DF' DF)
            o ((right_morphism_of A' A'' T' oR DF)
                 o ((associator_2 CF' G' DF)
                      o ((CF' oL right_morphism_of A A' T)
                           o (associator_1 CF' CF G))))
        := ap (@NaturalTransformation.Dual.opposite _ _ _ _)
              (@left_composition_of
                 _ _ _ _ (DF^op) (DF'^op) _ _ _ (CF^op) (CF'^op)
                 _ _ A^op _ _ A'^op _ _ A''^op T^op T'^op).
    End composition_of_dep.

    Section composition_of.
      Context `{Funext}.
      Variables C D : PreCategory.

      Variable F : Functor C D.
      Variable G : Functor D C.
      Variable A : F -| G.
      Variable F' : Functor C D.
      Variable G' : Functor D C.
      Variable A' : F' -| G'.
      Variable F'' : Functor C D.
      Variable G'' : Functor D C.
      Variable A'' : F'' -| G''.
      Variable T : NaturalTransformation F F'.
      Variable T' : NaturalTransformation F' F''.

      Local Open Scope natural_transformation_scope.

      Definition right_composition_of_nondep
      : (@right_morphism_of_nondep _ _ _ _ A'' _ _ A (T' o T))
        = ((right_morphism_of_nondep A' A T)
             o (right_morphism_of_nondep A'' A' T'))
        := ap (@NaturalTransformation.Dual.opposite _ _ _ _)
              (@left_composition_of_nondep _ _ _ _ _ A''^op _ _ A'^op _ _ A^op T'^op T^op).
    End composition_of.
  End right.
End laws.
