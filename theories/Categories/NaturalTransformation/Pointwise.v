(** * Pointwise Natural Transformations *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.NaturalTransformation.Core.
Require Import HoTT.Categories.FunctorCategory.Core HoTT.Categories.NaturalTransformation.Paths HoTT.Categories.Functor.Composition.Core HoTT.Categories.NaturalTransformation.Composition.Core.
Require Import HoTT.Categories.Functor.Pointwise.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

(** Recall that a "pointwise" functor is a functor [Aᴮ → Cᴰ] induced
    by functors [D → B] and [A → C].  Given two functors [D → B] and a
    natural transformation between them, there is an induced natural
    transformation between the resulting functors between functor
    categories, and similarly for two functors [A → C].  In this file,
    we construct these natural transformations. They will be used to
    construct the pointwise induced adjunction [Fˣ ⊣ Gˣ] of an
    adjunction [F ⊣ G] for all categories [X]. *)

Local Open Scope morphism_scope.
Local Open Scope category_scope.
Local Open Scope functor_scope.
Local Open Scope natural_transformation_scope.

Section pointwise.
  Context `{Funext}.

  Variables C D C' D' : PreCategory.

  Local Ltac t :=
    path_natural_transformation; simpl;
    rewrite <- ?composition_of;
    try apply ap;
    first [ apply commutes
          | symmetry; apply commutes ].

  (** ** [Tˣ] for a natural transformation [T : F → G] and a functor [x : C → D] *)
  Definition pointwise_l
             (F G : Functor C D)
             (T : NaturalTransformation F G)
             (F' : Functor C' D')
  : NaturalTransformation (pointwise F F') (pointwise G F').
  Proof.
    refine (Build_NaturalTransformation
              (pointwise F F') (pointwise G F')
              (fun f : object (D -> C') => (F' o f) oL T)%natural_transformation
              _).
    abstract t.
  Defined.

  (** ** [Fᵀ] for a natural transformation [T : F' → G'] and a functor [F : C → D] *)
  Definition pointwise_r
             (F : Functor C D)
             (F' G' : Functor C' D')
             (T' : NaturalTransformation F' G')
  : NaturalTransformation (pointwise F F') (pointwise F G').
  Proof.
    refine (Build_NaturalTransformation
              (pointwise F F') (pointwise F G')
              (fun f : object (D -> C') => T' oR f oR F)%natural_transformation
              _).
    abstract t.
  Defined.
End pointwise.
