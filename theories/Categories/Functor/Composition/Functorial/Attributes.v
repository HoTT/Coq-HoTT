(** * Attributes of Functoriality of functor composition *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.NaturalTransformation.Core.
Require Import HoTT.Categories.Functor.Composition.Core HoTT.Categories.Functor.Composition.Functorial.Core.
Require Import HoTT.Categories.NaturalTransformation.Composition.Core HoTT.Categories.NaturalTransformation.Composition.Functorial.
Require Import HoTT.Categories.NaturalTransformation.Isomorphisms.
Require Import HoTT.Categories.Functor.Attributes.
Require Import HoTT.Categories.FunctorCategory.Core.
Require Import HoTT.Categories.Category.Morphisms.
Require Import HoTT.Categories.SetCategory.Core.
Require Import HoTT.Categories.NaturalTransformation.Paths.
Require Import HoTT.HSet HoTT.HProp HoTT.Truncations.
(*.
Require Import Category.Prod  NaturalTransformation.Composition.Functorial NaturalTransformation.Composition.Laws ExponentialLaws.Law4.Functors.
Require Import NaturalTransformation.Paths.
Require ProductLaws.*)

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope natural_transformation_scope.
Local Open Scope morphism_scope.

(** ** Precomposition with an essentially surjective functor is faithful *)
Section faithfull_precomposition_essential_surjective.
  (** Quoting the HoTT Book:

  Lemma. If [A], [B], [C] are precategories and [H : A → B] is an
  essentially surjective functor, then [(– ∘ H) : (B → C) → (A → C)]
  is faithful. *)

  Context `{fs : Funext}.
  Variables A B C : PreCategory.

  Variable H : Functor A B.

  Context `{H_is_essentially_surjective : IsEssentiallySurjective A B H}.

  Lemma isfaithful_precomposition_essentially_surjective_helper
        (F G : Functor B C)
        (T U : NaturalTransformation F G)
        (a : A) (b : B)
        (f : H a <~=~> b)
        (H' : T oR H = U oR H)
  : T b = U b.
  Proof.
    apply (ap components_of) in H'.
    apply apD10 in H'; hnf in H'; simpl in H'.
    rewrite <- !(path_components_of_isomorphic' f).
    rewrite H'.
    reflexivity.
  Qed.

  Global Instance isfaithful_precomposition_essentially_surjective
  : @IsFaithful _ (B -> C) (A -> C) (compose_functor _ _ _ H).
  Proof.
    repeat match goal with
             | _ => eapply isfaithful_precomposition_essentially_surjective_helper;
                   eassumption
             | _ => intro
             | _ => progress hnf in *
             | _ => progress simpl in *
             | _ => apply path_forall
             | _ => progress strip_truncations
             | [ H : _ |- _ ] => apply ap10 in H
             | _ => progress path_natural_transformation
             | [ H : sig _ |- _ ] => destruct H
             | [ H : _, t : _ |- _ ]
               => generalize dependent (H t); clear H
           end.
  Qed.
End faithfull_precomposition_essential_surjective.
