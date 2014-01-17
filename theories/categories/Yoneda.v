Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual.
Require Import Category.Prod.
Require Import Functor.Composition.Core.
Require Import Category.Morphisms.
Require Import SetCategory.
Require Import Functor.Attributes.
Require ExponentialLaws.Law4.Functors.
Require ProductLaws.
Require Import HomFunctor.
Require Import FunctorCategory.Core.
Require Import NaturalTransformation.Paths.
Require Import HSet HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope functor_scope.

Section yoneda.
  Context `{Funext}.
  Variable C : PreCategory.

  Definition coyoneda : Functor C^op (C -> set_cat)
    := ExponentialLaws.Law4.Functors.inverse _ _ _ (hom_functor C).

  Definition yoneda : Functor C (C^op -> set_cat)
    := ExponentialLaws.Law4.Functors.inverse _ _ _ (hom_functor C o ProductLaws.Swap.functor _ _).
End yoneda.

Section yoneda_lemma.
  Context `{Funext}.
  Variable C : PreCategory.

  Definition yoneda_lemma_morphism (c : C) (X : object (C^op -> set_cat))
  : morphism set_cat
             (BuildhSet
                (morphism (C^op -> set_cat) (yoneda C c) X)
                _)
             (X c)
    := fun a => a c 1%morphism.

  Definition yoneda_lemma_morphism_inverse (c : C^op) (X : object (C^op -> set_cat))
  : morphism set_cat
             (X c)
             (BuildhSet
                (morphism (C^op -> set_cat) (yoneda C c) X)
                _).
  Proof.
    simpl; intro Xc.
    hnf.
    let F := match goal with |- NaturalTransformation ?F ?G => constr:(F) end in
    let G := match goal with |- NaturalTransformation ?F ?G => constr:(G) end in
    refine (Build_NaturalTransformation
              F G
              (fun c' : C => (fun f : morphism _ c c' => X.(morphism_of) f Xc))
              _
           ).
    abstract (
        repeat first [ reflexivity
                     | intro
                     | apply path_forall
                     | progress simpl in *
                     | progress unfold Overture.compose
                     | rewrite !composition_of
                     | progress rewrite ?left_identity, ?right_identity
                     | rewrite !identity_of
                     | match goal with
                         | [ F : Functor _ _ |- _ ] => simpl rewrite (composition_of F)
                       end ]
      ).
  Defined.

  Local Arguments Overture.compose / .
  Local Arguments yoneda_lemma_morphism / .
  Local Arguments yoneda_lemma_morphism_inverse / .

  Global Instance yoneda_lemma (c : C) (X : object (C^op -> set_cat))
  : IsIsomorphism (@yoneda_lemma_morphism c X).
  Proof.
    exists (@yoneda_lemma_morphism_inverse c X);
    abstract (
        repeat (intro || apply path_forall || path_natural_transformation);
        simpl in *;
          solve [ simpl rewrite <- (fun c d m => ap10 (commutes x c d m));
                  rewrite ?right_identity, ?left_identity;
                  reflexivity
                | match goal with
                    | [ F : Functor _ _ |- _ ] => rewrite (identity_of F)
                  end;
                  reflexivity ]
      ).
  Defined.
End yoneda_lemma.

Section coyoneda_lemma.
  Context `{Funext}.
  Variable C : PreCategory.

  Definition coyoneda_lemma_morphism (c : C) (X : object (C -> set_cat))
  : morphism set_cat
             (BuildhSet
                (morphism (C -> set_cat) (coyoneda _ c) X)
                _)
             (X c)
    := fun a => a c 1%morphism.

  Definition coyoneda_lemma_morphism_inverse (c : C) (X : object (C -> set_cat))
  : morphism set_cat
             (X c)
             (BuildhSet
                (morphism (C -> set_cat) (coyoneda C c) X)
                _).
  Proof.
    simpl; intro Xc.
    hnf.
    let F := match goal with |- NaturalTransformation ?F ?G => constr:(F) end in
    let G := match goal with |- NaturalTransformation ?F ?G => constr:(G) end in
    refine (Build_NaturalTransformation
              F G
              (fun c' : C => (fun f : morphism _ c c' => X.(morphism_of) f Xc))
              _
           ).
    abstract (
        repeat first [ reflexivity
                     | intro
                     | apply path_forall
                     | progress simpl
                     | progress unfold Overture.compose
                     | rewrite !composition_of
                     | rewrite !identity_of ]
      ).
  Defined.

  Local Arguments Overture.compose / .
  Local Arguments coyoneda_lemma_morphism / .
  Local Arguments coyoneda_lemma_morphism_inverse / .

  Global Instance coyoneda_lemma (c : C) (X : object (C -> set_cat))
  : IsIsomorphism (@coyoneda_lemma_morphism c X).
  Proof.
    exists (@coyoneda_lemma_morphism_inverse c X);
    abstract (
        repeat (intro || apply path_forall || path_natural_transformation);
        simpl in *;
          solve [ simpl rewrite <- (fun c d m => ap10 (commutes x c d m));
                  rewrite ?right_identity, ?left_identity;
                  reflexivity
                | rewrite identity_of;
                  reflexivity ]
      ).
  Defined.
End coyoneda_lemma.

Section FullyFaithful.
  Context `{Funext}.
  Variable C : PreCategory.

  Local Arguments Overture.compose / .

  Definition yoneda_embedding : IsFullyFaithful (yoneda C).
  Proof.
    intros c c'.
    pose (yoneda_lemma (C := C) c (yoneda C c')) as YL.
    exists (yoneda_lemma_morphism (X := yoneda C c'));
      [ eapply iso_moveR_Mp
      | eapply iso_moveR_pM ];
      repeat (intro || apply path_forall || path_natural_transformation);
        simpl;
        rewrite ?left_identity, ?right_identity;
        reflexivity.
  Qed.

  Definition coyoneda_embedding : IsFullyFaithful (coyoneda C).
  Proof.
    intros c c'.
    pose (coyoneda_lemma (C := C) c (coyoneda C c')) as YL.
    exists (coyoneda_lemma_morphism (X := coyoneda C c'));
      [ eapply iso_moveR_Mp
      | eapply iso_moveR_pM ];
      repeat (intro || apply path_forall || path_natural_transformation);
        simpl;
        rewrite ?left_identity, ?right_identity;
        reflexivity.
  Qed.
End FullyFaithful.
