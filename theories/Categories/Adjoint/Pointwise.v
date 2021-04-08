(** * Pointwise Adjunctions *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.NaturalTransformation.Core.
Require Import HoTT.Categories.Functor.Identity.
Require Import HoTT.Categories.Category.Morphisms.
Require Import HoTT.Categories.Functor.Composition.Core HoTT.Categories.NaturalTransformation.Composition.Core.
Require Import HoTT.Categories.Adjoint.Core HoTT.Categories.Adjoint.UnitCounit HoTT.Categories.Adjoint.UnitCounitCoercions.
Require Import HoTT.Categories.Functor.Pointwise.Core.
Require HoTT.Categories.NaturalTransformation.Pointwise.
Require HoTT.Categories.Functor.Pointwise.Properties.
Require Import HoTT.Categories.Category.Morphisms HoTT.Categories.FunctorCategory.Morphisms.
Require Import HoTT.Categories.FunctorCategory.Core.
Require HoTT.Categories.NaturalTransformation.Identity.
Require HoTT.Categories.NaturalTransformation.Composition.Laws.
Import NaturalTransformation.Identity.NaturalTransformationIdentityNotations.
Require Import HoTT.Categories.NaturalTransformation.Paths HoTT.Categories.Functor.Paths.
Require Import HoTT.Basics.PathGroupoids HoTT.HProp HoTT.Types.Forall HoTT.Tactics HoTT.Types.Arrow.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope functor_scope.
Local Open Scope natural_transformation_scope.

Section AdjointPointwise.
  Context `{Funext}.

  Variables C D : PreCategory.

  (** ** [F ⊣ G] → [E^F ⊣ E^G] *)
  Section l.
    Variable E : PreCategory.

    Variable F : Functor C D.
    Variable G : Functor D C.

    Variable A : F -| G.

    Definition unit_l
    : NaturalTransformation (identity (E -> C))
                            ((pointwise (identity E) G) o (pointwise (identity E) F)).
    Proof.
      pose proof (A : AdjunctionUnit _ _) as A''.
      refine (_ o (((idtoiso (C := (_ -> _)) (Functor.Pointwise.Properties.identity_of _ _))^-1)%morphism : morphism _ _ _)).
      refine (_ o NaturalTransformation.Pointwise.pointwise_r (Functor.Identity.identity E) (proj1 A'')).
      refine (((idtoiso
                  (C := (_ -> _))
                  (Functor.Pointwise.Properties.composition_of
                     (Functor.Identity.identity E) F
                     (Functor.Identity.identity E) G)) : morphism _ _ _)
                o _).
      refine (NaturalTransformation.Pointwise.pointwise_l _ _).
      exact (NaturalTransformation.Composition.Laws.left_identity_natural_transformation_2 _).
    Defined.

    Definition counit_l
    : NaturalTransformation (pointwise (identity E) F o pointwise (identity E) G)
                            (identity (E -> D)).
    Proof.
      pose proof (A : AdjunctionCounit _ _) as A''.
      refine ((((idtoiso (C := (_ -> _)) (Functor.Pointwise.Properties.identity_of _ _)))%morphism : morphism _ _ _) o _).
      refine (NaturalTransformation.Pointwise.pointwise_r (Functor.Identity.identity E) (proj1 A'') o _).
      refine (_ o
                (((idtoiso
                     (C := (_ -> _))
                     (Functor.Pointwise.Properties.composition_of
                        (Functor.Identity.identity E) G
                        (Functor.Identity.identity E) F))^-1)%morphism : morphism _ _ _)).
      refine (NaturalTransformation.Pointwise.pointwise_l _ _).
      exact (NaturalTransformation.Composition.Laws.left_identity_natural_transformation_1 _).
    Defined.

    Create HintDb adjoint_pointwise discriminated.
    Hint Rewrite
         identity_of left_identity right_identity
         eta_idtoiso composition_of idtoiso_functor
         @ap_V @ap10_V @ap10_path_forall
         path_functor_uncurried_fst
    : adjoint_pointwise.

    Definition pointwise_l : pointwise (identity E) F -| pointwise (identity E) G.
    Proof.
      Time (
          (exists unit_l counit_l);
          abstract (
              path_natural_transformation;
              intros;
              destruct A;
              simpl in *;
                repeat match goal with
                         | _ => progress simpl
                         | _ => progress autorewrite with adjoint_pointwise
                         | [ |- context[ap object_of (path_functor_uncurried ?F ?G (?HO; ?HM))] ]
                           => rewrite (@path_functor_uncurried_fst _ _ _ F G HO HM)
                         | _ => progress unfold Functor.Pointwise.Properties.identity_of
                         | _ => progress unfold Functor.Pointwise.Properties.composition_of
                         | _ => progress unfold Functor.Pointwise.Properties.identity_of_helper
                         | _ => progress unfold Functor.Pointwise.Properties.composition_of_helper
                         | _ => progress unfold Functor.Pointwise.Properties.identity_of_helper_helper
                         | _ => progress unfold Functor.Pointwise.Properties.composition_of_helper_helper
                         | [ H : _ |- _ ] => apply H
                       end
            )
        ). (* 23.345 s *)
    Defined.
  End l.

  (** ** [F ⊣ G] → [Gᴱ ⊣ Fᴱ] *)
  Section r.
    Variable F : Functor C D.
    Variable G : Functor D C.

    Variable A : F -| G.

    Variable E : PreCategory.

    Definition unit_r
    : NaturalTransformation (identity (C -> E))
                            ((pointwise F (identity E)) o (pointwise G (identity E))).
    Proof.
      pose proof (A : AdjunctionUnit _ _) as A''.
      refine (_ o (((idtoiso (C := (_ -> _)) (Functor.Pointwise.Properties.identity_of _ _))^-1)%morphism : morphism _ _ _)).
      refine (_ o NaturalTransformation.Pointwise.pointwise_l (proj1 A'') (Functor.Identity.identity E)).
      refine (((idtoiso
                  (C := (_ -> _))
                  (Functor.Pointwise.Properties.composition_of
                     G (Functor.Identity.identity E)
                     F (Functor.Identity.identity E))) : morphism _ _ _)
                o _).
      refine (NaturalTransformation.Pointwise.pointwise_r _ _).
      exact (NaturalTransformation.Composition.Laws.left_identity_natural_transformation_2 _).
    Defined.

    Definition counit_r
    : NaturalTransformation (pointwise G (identity E) o pointwise F (identity E))
                            (identity (D -> E)).
    Proof.
      pose proof (A : AdjunctionCounit _ _) as A''.
      refine ((((idtoiso (C := (_ -> _)) (Functor.Pointwise.Properties.identity_of _ _)))%morphism : morphism _ _ _) o _).
      refine (NaturalTransformation.Pointwise.pointwise_l (proj1 A'') (Functor.Identity.identity E) o _).
      refine (_ o
                (((idtoiso
                     (C := (_ -> _))
                     (Functor.Pointwise.Properties.composition_of
                        F (Functor.Identity.identity E)
                        G (Functor.Identity.identity E)))^-1)%morphism : morphism _ _ _)).
      refine (NaturalTransformation.Pointwise.pointwise_r _ _).
      exact (NaturalTransformation.Composition.Laws.left_identity_natural_transformation_1 _).
    Defined.

    Create HintDb adjoint_pointwise discriminated.
    Hint Rewrite
         identity_of left_identity right_identity
         eta_idtoiso composition_of idtoiso_functor
         @ap_V @ap10_V @ap10_path_forall
         path_functor_uncurried_fst
    : adjoint_pointwise.

    Definition pointwise_r : pointwise G (identity E) -| pointwise F (identity E).
    Proof.
      Time (
          (exists unit_r counit_r);
          abstract (
              path_natural_transformation;
              intros;
              destruct A;
              simpl in *;
                repeat match goal with
                         | _ => reflexivity
                         | _ => progress simpl
                         | _ => progress autorewrite with adjoint_pointwise
                         | [ |- context[ap object_of (path_functor_uncurried ?F ?G (?HO; ?HM))] ]
                           => rewrite (@path_functor_uncurried_fst _ _ _ F G HO HM)
                         | _ => progress unfold Functor.Pointwise.Properties.identity_of
                         | _ => progress unfold Functor.Pointwise.Properties.composition_of
                         | _ => progress unfold Functor.Pointwise.Properties.identity_of_helper
                         | _ => progress unfold Functor.Pointwise.Properties.composition_of_helper
                         | _ => progress unfold Functor.Pointwise.Properties.identity_of_helper_helper
                         | _ => progress unfold Functor.Pointwise.Properties.composition_of_helper_helper
                         | _ => rewrite <- composition_of; progress rewrite_hyp
                       end
            )
        ). (* 19.097 *)
    Defined.
  End r.
End AdjointPointwise.
