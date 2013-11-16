Require Import Category.Core Functor.Core NaturalTransformation.Core NaturalTransformation.Paths.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope path_scope.
Local Open Scope natural_transformation_scope.

Section identity.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Local Ltac id_fin_t :=
    intros;
    etransitivity;
    [ apply left_identity
    | apply symmetry; apply right_identity ].

  (** There is an identity natrual transformation.  We create a number
      of variants, for various uses. *)
  Section generalized.
    Variables F G : Functor C D.
    Hypothesis HO : object_of F = object_of G.
    Hypothesis HM : transport (fun GO => forall s d,
                                           morphism C s d
                                           -> morphism D (GO s) (GO d))
                              HO
                              (morphism_of F)
                    = morphism_of G.

    Local Notation CO c := (transport (fun GO => morphism D (F c) (GO c))
                                      HO
                                      (identity (F c))).

    Definition generalized_identity_commutes
               s d (m : morphism C s d)
    : CO d o morphism_of F m
      = morphism_of G m o CO s.
    Proof.
      case HM. case HO.
      id_fin_t.
    Defined.

    Definition generalized_identity
    : NaturalTransformation F G
      := Build_NaturalTransformation
           F G
           (fun c => CO c)
           generalized_identity_commutes.
  End generalized.

  Global Arguments generalized_identity_commutes / .
  Global Arguments generalized_identity F G !HO !HM / .

  Section generalized'.
    Variables F G : Functor C D.
    Hypothesis H : F = G.

    Definition generalized_identity'
    : NaturalTransformation F G.
    Proof.
      apply (generalized_identity
               F G
               (ap (@object_of C D) H)).
      case H.
      reflexivity.
    Defined.
  End generalized'.

  Definition identity (F : Functor C D)
  : NaturalTransformation F F
    := Eval simpl in @generalized_identity F F 1 1.

  Global Arguments generalized_identity' F G !H / .
End identity.

Global Opaque commutes.

Module Export NaturalTransformationIdentityNotations.
  Notation "1" := (identity _) : natural_transformation_scope.
End NaturalTransformationIdentityNotations.
