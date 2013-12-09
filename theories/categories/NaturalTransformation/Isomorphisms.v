Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import NaturalTransformation.Composition.Core.
Require Import Functor.Composition.Core.
Require Import Category.Morphisms FunctorCategory.Morphisms.
Require Import FunctorCategory.Core.
Require Import NaturalTransformation.Paths.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope natural_transformation_scope.
Local Open Scope morphism_scope.


Local Ltac iso_whisker_t :=
  path_natural_transformation;
  try rewrite <- composition_of, <- identity_of;
  try f_ap;
  match goal with
    | [ H : IsIsomorphism _
        |- appcontext[components_of ?T0 ?x o components_of ?T1 ?x] ]
      => change (T0 x o T1 x)
         with (components_of ((T0 : morphism (_ -> _) _ _)
                                o (T1 : morphism (_ -> _) _ _))%morphism
                             x);
        progress rewrite ?(@left_inverse _ _ _ _ H), ?(@right_inverse _ _ _ _ H)
  end;
  reflexivity.

Section composition.
  Context `{Funext}.

  Global Instance isisomorphism_compose
         `(T' : @NaturalTransformation C D F' F'')
         `(T : @NaturalTransformation C D F F')
         `{@IsIsomorphism (C -> D) F' F'' T'}
         `{@IsIsomorphism (C -> D) F F' T}
  : @IsIsomorphism (C -> D) F F'' (T' o T)%natural_transformation
    := @isisomorphism_compose (C -> D) _ _ T' _ _ T _.

  Global Instance iso_whisker_l C D E
         (F : Functor D E)
         (G G' : Functor C D)
         (T : NaturalTransformation G G')
         `{@IsIsomorphism (C -> D) G G' T}
  : @IsIsomorphism (C -> E) (F o G)%functor (F o G')%functor (whisker_l F T).
  Proof.
    exists (whisker_l F (T : morphism (_ -> _) _ _)^-1);
    abstract iso_whisker_t.
  Defined.

  Global Instance iso_whisker_r C D E
         (F F' : Functor D E)
         (T : NaturalTransformation F F')
         (G : Functor C D)
         `{@IsIsomorphism (D -> E) F F' T}
  : @IsIsomorphism (C -> E) (F o G)%functor (F' o G)%functor (whisker_r T G).
  Proof.
    exists (whisker_r (T : morphism (_ -> _) _ _)^-1 G);
    abstract iso_whisker_t.
  Defined.

  Definition idtoiso_compose C D
         (F F' F'' : Functor C D)
         (T' : F' = F'')
         (T : F = F')
  : ((Category.Morphisms.idtoiso (_ -> _) T' : morphism _ _ _)
       o (Category.Morphisms.idtoiso (_ -> _) T : morphism _ _ _))%natural_transformation
    = (Category.Morphisms.idtoiso (_ -> _) (T @ T')%path : morphism _ _ _).
  Proof.
    path_natural_transformation; path_induction; simpl; auto with morphism.
  Defined.

  Definition idtoiso_whisker_l C D E
         (F : Functor D E)
         (G G' : Functor C D)
         (T : G = G')
  : whisker_l F (Category.Morphisms.idtoiso (_ -> _) T : morphism _ _ _)
    = (Category.Morphisms.idtoiso (_ -> _) (ap _ T) : morphism _ _ _).
  Proof.
    path_natural_transformation; path_induction; simpl; auto with functor.
  Defined.

  Definition idtoiso_whisker_r C D E
         (F F' : Functor D E)
         (T : F = F')
         (G : Functor C D)
  : whisker_r (Category.Morphisms.idtoiso (_ -> _) T : morphism _ _ _) G
    = (Category.Morphisms.idtoiso (_ -> _) (ap (fun _ => _ o _)%functor T) : morphism _ _ _).
  Proof.
    path_natural_transformation; path_induction; simpl; auto with functor.
  Defined.
End composition.
