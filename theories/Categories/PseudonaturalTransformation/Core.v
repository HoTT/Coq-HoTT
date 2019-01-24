(** * Definition of pseudonatural transformation *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Pseudofunctor.Core.
Require Import Category.Pi.
Require Import FunctorCategory.Core.
Require Import Category.Morphisms FunctorCategory.Morphisms.
Require Import Functor.Composition.Core Functor.Identity.
Require Import NaturalTransformation.Composition.Core NaturalTransformation.Composition.Laws.
Require Import NaturalTransformation.Identity.
Require Import NaturalTransformation.Isomorphisms.
Require Import NaturalTransformation.Paths.
Require Import FunctorCategory.Core.
Require Import HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Declare Scope pseudonatural_transformation_scope.
Delimit Scope pseudonatural_transformation_scope with pseudonatural_transformation.

Local Open Scope natural_transformation_scope.
Local Open Scope functor_scope.
Local Open Scope morphism_scope.
Local Open Scope pseudonatural_transformation_scope.

(** Quoting Michael Shulman from an email:

    The 2-limit in question is sometimes called a "descent object", or
    the totalization of a truncated cosimplicial object.  It's a
    generalization of an equalizer.  The set of natural
    transformations between two ordinary functors [F],[G : C → D] is
    the equalizer of

    [Π_x D(Fx,Gx) ⇉ Π_{x→y} D(Fx,Gy)]

    The category of pseudonatural transformations between two
    2-functors is the descent object of

    [Π_x D(Fx,Gx) ⇉ Π_{x→y} D(Fx,Gy) ⇛ Π_{x→y→z} D(Fx,Gz)]

    where there are three maps from the second product to the third,
    corresponding to picking out [x→y], [y→z], and [x→z].

    In general, the descent object of

    [A ⇉ B ⇛ C]

    is the category of objects [a∈A] equipped with an isomorphism
    between their two images in [B] which results in a commutative
    triangle between their three images in [C]. *)

(** Later, he said (https://github.com/HoTT/HoTT/pull/382##issuecomment-41240787):

    The "naturality" axiom is only necessary if the domain is a
    2-category rather than a 1-category. However, the respect for
    units axiom really is necessary; I guess I forgot to mention that
    in the email. The way it comes up in the descent object is that
    there's a map from [B] to [A] given by projecting the components
    of identities, and the coherence cell has to become an identity
    when composed with that map. *)

(** We construct the parts as above, but inline the resulting definitions for speed.
<<
Module PseudonaturalTransformationParts.
  Section PseudonaturalTransformation.
    Context `{Funext}.

    Variable X : PreCategory.

    Variables F G : Pseudofunctor X.


    Definition A : PreCategory
      := (forall x : X, F x -> G x)%category.
    Definition B : PreCategory
      := (forall x y (m : morphism X x y), F x -> G y)%category.
    Definition C : PreCategory
      := (forall x y z (m1 : morphism X y z) (m2 : morphism X x y), F x -> G z)%category.

    Definition a_part := Eval simpl in object A.

    Definition A_to_B_1 : Functor A B.
    Proof.
      refine (Build_Functor
                A B
                (fun x__Fx_to_Gx => fun x y m => x__Fx_to_Gx y o p_morphism_of F m)%functor
                (fun x__s x__d x__m => fun x y m => x__m y oR p_morphism_of F m)
                _
                _);
      simpl; repeat (intro || apply path_forall);
      [ apply composition_of_whisker_r
      | apply whisker_r_left_identity ].
    Defined.

    Definition A_to_B_2 : Functor A B.
    Proof.
      refine (Build_Functor
                A B
                (fun x__Fx_to_Gx => fun x y m => p_morphism_of G m o x__Fx_to_Gx x)%functor
                (fun x__s x__d x__m => fun x y m => p_morphism_of G m oL x__m x)
                _
                _);
      simpl; repeat (intro || apply path_forall);
      [ apply composition_of_whisker_l
      | apply whisker_l_right_identity ].
    Defined.

    Definition b_part (a : a_part)
      := Eval simpl in forall x y m, (A_to_B_1 a x y m <~=~> A_to_B_2 a x y m).

    Definition B_to_A : Functor B A
      := Build_Functor
           B A
           (fun xym__Fx_to_Gy => fun x => xym__Fx_to_Gy x x 1)
           (fun x__s x__d x__m => fun x => x__m x x 1)
           (fun _ _ _ _ _ => idpath)
           (fun _ => idpath).

    Definition b_id_part (a : a_part) (b : b_part a)
      := Eval simpl in
          forall x,
            (((left_identity_natural_transformation_1 _)
                o (p_identity_of G _ oR _)
                o (B_to_A _1 b x)
                o (_ oL (p_identity_of F _)^-1)
                o (left_identity_natural_transformation_2 _))
             = 1)%natural_transformation.

    Definition B_to_C_1 : Functor B C.
    Proof.
      refine (Build_Functor
                B C
                (fun xym__Fx_to_Gy => fun x y z m1 m2 => xym__Fx_to_Gy y z m1 o p_morphism_of F m2)%functor
                (fun xym__s xym__d xym__m => fun x y z m1 m2 => xym__m y z m1 oR p_morphism_of F m2)
                _
                _);
      simpl; repeat (intro || apply path_forall);
      [ apply composition_of_whisker_r
      | apply whisker_r_left_identity ].
    Defined.

    Definition B_to_C_2 : Functor B C.
    Proof.
      refine (Build_Functor
                B C
                (fun xym__Fx_to_Gy => fun x y z m1 m2 => p_morphism_of G m1 o xym__Fx_to_Gy x y m2)%functor
                (fun xym__s xym__d xym__m => fun x y z m1 m2 => p_morphism_of G m1 oL xym__m x y m2)
                _
                _);
      simpl; repeat (intro || apply path_forall);
      [ apply composition_of_whisker_l
      | apply whisker_l_right_identity ].
    Defined.

    Definition B_to_C_3 : Functor B C
      := Build_Functor
           B C
           (fun xym__Fx_to_Gy => fun x y z m1 m2 => xym__Fx_to_Gy x z (m1 o m2))
           (fun xym__s xym__d xym__m => fun x y z m1 m2 => xym__m x z (m1 o m2))
           (fun _ _ _ _ _ => idpath)
           (fun _ => idpath).

    Definition c_part' (a : a_part) (b : b_part a)
    : forall (x y z : X) (m1 : morphism X y z) (m2 : morphism X x y), Type.
    Proof.
      hnf in a, b.
      pose (fun x y m => (b x y m : morphism _ _ _)) as bB; simpl in *.
      intros x y z m1 m2.
      exact (((associator_2 _ _ _)
                o (B_to_C_2 _1 bB x y z m1 m2)
                o (associator_1 _ _ _)
                o (B_to_C_1 _1 bB x y z m1 m2)
                o (associator_2 _ _ _))
             = ((p_composition_of G _ _ _ m1 m2 oR _)
                  o (B_to_C_3 _1 bB x y z m1 m2)
                  o (_ oL (p_composition_of F _ _ _ m1 m2)^-1)))%natural_transformation.
    Defined.

    Arguments c_part' / .

    Definition c_part (a : a_part) (b : b_part a)
      := Eval simpl in forall x y z m1 m2, @c_part' a b x y z m1 m2.

    (** We would like to define [PseudonaturalTransformation] here, then our types are η-expanded. *)
  (*Record PseudonaturalTransformation :=
      { p_components_of :> a_part;
        p_commutes : b_part p_components_of;
        p_commutes_coherent : c_part p_commutes }.*)
  End PseudonaturalTransformation.
End PseudonaturalTransformationParts.

Print PseudonaturalTransformationParts.a_part.
Print PseudonaturalTransformationParts.b_part.
Print PseudonaturalTransformationParts.b_id_part.
Print PseudonaturalTransformationParts.c_part.
>> *)

Record PseudonaturalTransformation `{Funext} (X : PreCategory)
       (F G : Pseudofunctor X) :=
  { p_components_of
      :> forall a : X, Functor (F a) (G a);
    p_commutes
    : forall (x y : X) (m : morphism X x y),
        ((p_components_of y o p_morphism_of F m)%functor <~=~> (p_morphism_of G m o p_components_of x)%functor)%natural_transformation;
    p_commutes_respects_identity
    : forall x : X,
        ((left_identity_natural_transformation_1 (p_components_of x))
           o (p_identity_of G x oR p_components_of x)
           o (p_commutes x x 1%morphism)
           o (p_components_of x oL (p_identity_of F x) ^-1)
           o (right_identity_natural_transformation_2 (p_components_of x))
         = 1)%natural_transformation;
    p_commutes_respects_composition
    : forall (x y z : X) (m1 : morphism X y z) (m2 : morphism X x y),
        (((associator_2 (p_morphism_of G m1) (p_morphism_of G m2) (p_components_of x))
            o (p_morphism_of G m1 oL p_commutes x y m2)
            o (associator_1 (p_morphism_of G m1) (p_components_of y) (p_morphism_of F m2))
            o (p_commutes y z m1 oR p_morphism_of F m2)
            o (associator_2 (p_components_of z) (p_morphism_of F m1) (p_morphism_of F m2)))
         = ((p_composition_of G x y z m1 m2 oR p_components_of x o p_commutes x z (m1 o m2)%morphism)
              o (p_components_of z oL (p_composition_of F x y z m1 m2) ^-1)))%natural_transformation }.

Bind Scope pseudonatural_transformation_scope with PseudonaturalTransformation.

Create HintDb pseuodnatural_transformation discriminated.

Arguments p_components_of {_} {X}%category {F G}%pseudofunctor T%pseudonatural_transformation
          a%object : rename, simpl nomatch.

Hint Resolve @p_commutes_respects_identity @p_commutes_respects_composition : category pseudonatural_transformation.
