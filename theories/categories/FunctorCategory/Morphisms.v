(** * Morphisms in a functor category *)
Require Import Category.Core Functor.Core NaturalTransformation.Paths FunctorCategory.Core Category.Morphisms NaturalTransformation.Core NaturalTransformation.Composition.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.
Local Open Scope category_scope.
Local Open Scope morphism_scope.

(** ** Natural Isomorphisms - isomorphisms in a functor category *)
Definition NaturalIsomorphism `{Funext} (C D : PreCategory) F G :=
  @Isomorphic (C -> D) F G.

Arguments NaturalIsomorphism {_} [C D] F G / .

Global Instance reflexive_natural_isomorphism `{Funext} C D
: Reflexive (@NaturalIsomorphism _ C D) | 0
  := _.

Coercion natural_transformation_of_natural_isomorphism `{Funext} C D F G
         (T : @NaturalIsomorphism _ C D F G)
: NaturalTransformation F G
  := T : morphism _ _ _.

Local Infix "<~=~>" := NaturalIsomorphism : natural_transformation_scope.

(** ** If [T] is an isomorphism, then so is [T x] for any [x] *)
Definition isisomorphism_components_of `{Funext}
           `{@IsIsomorphism (C -> D) F G T} x
: IsIsomorphism (T x).
Proof.
  exists (T^-1 x).
  - exact (apD10 (ap components_of left_inverse) x).
  - exact (apD10 (ap components_of right_inverse) x).
Defined.

Hint Immediate isisomorphism_components_of : typeclass_instances.
(** When one of the functors is the identity functor, we fail to match correctly, because [apply] is stupid.  So we do its work for it. *)
Hint Extern 10 (@IsIsomorphism _ _ _ (@components_of ?C ?D ?F ?G ?T ?x))
=> apply (fun H' => @isisomorphism_components_of _ C D F G T H' x)
   : typeclass_instances.

Definition inverse `{Funext}
           C D (F G : Functor C D) (T : NaturalTransformation F G)
           `{forall x, IsIsomorphism (T x)}
: NaturalTransformation G F.
Proof.
  exists (fun x => (T x)^-1);
  abstract (
      intros;
      iso_move_inverse;
      first [ apply commutes
            | symmetry; apply commutes ]
    ).
Defined.

(** ** If [T x] is an isomorphism for all [x], then so is [T] *)
Definition isisomorphism_natural_transformation `{Funext}
           C D F G (T : NaturalTransformation F G)
           `{forall x, IsIsomorphism (T x)}
: @IsIsomorphism (C -> D) F G T.
Proof.
  exists (inverse _);
  abstract (
      path_natural_transformation;
      first [ apply left_inverse
            | apply right_inverse ]
    ).
Defined.

Hint Immediate isisomorphism_natural_transformation : typeclass_instances.

(** ** Variant of [idtoiso] for natural transformations *)
Section idtoiso.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition idtoiso_natural_transformation
             (F G : object (C -> D))
             (T : F = G)
  : NaturalTransformation F G.
  Proof.
    refine (Build_NaturalTransformation'
              F G
              (fun x => idtoiso _ (ap10 (ap object_of T) x))
              _
              _);
    intros; case T; simpl;
    [ exact (left_identity _ _ _ _ @ (right_identity _ _ _ _)^)
    | exact (right_identity _ _ _ _ @ (left_identity _ _ _ _)^) ].
  Defined.

  Definition idtoiso
             (F G : object (C -> D))
             (T : F = G)
  : F <~=~> G.
  Proof.
    exists (idtoiso_natural_transformation T).
    exists (idtoiso_natural_transformation (T^)%path);
      abstract (path_natural_transformation; case T; simpl; auto with morphism).
  Defined.

  Lemma eta_idtoiso
        (F G : object (C -> D))
        (T : F = G)
  : Morphisms.idtoiso _ T = idtoiso T.
  Proof.
    case T.
    expand; f_ap.
    exact (center _).
  Qed.
End idtoiso.

Module Export FunctorCategoryMorphismsNotations.
  Infix "<~=~>" := NaturalIsomorphism : natural_transformation_scope.
End FunctorCategoryMorphismsNotations.
