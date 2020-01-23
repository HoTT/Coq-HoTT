(** * Identity pseudofunctor *)
Require Import FunctorCategory.Morphisms.
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import NaturalTransformation.Isomorphisms.
Require Import NaturalTransformation.Paths.
Require Import Cat.Core.
Require Import Pseudofunctor.Core.

(** Bring things into scope. *)
Import NaturalTransformation.Identity.
Import NaturalTransformation.Composition.Core NaturalTransformation.Composition.Laws.
Import Category.Morphisms.
Import FunctorCategory.Core.

Require Import PathGroupoids.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope natural_transformation_scope.

Section identity.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation cat := (@sub_pre_cat _ P HF).

  Local Ltac t :=
    path_natural_transformation;
    abstract (
        autorewrite with functor morphism;
        unfold morphism_isomorphic;
        rewrite ap_idmap, idtoiso_components_of;
        rewrite ?Functor.Composition.Laws.associativity_fst,
        ?Functor.Composition.Laws.left_identity_fst,
        ?Functor.Composition.Laws.right_identity_fst;
        reflexivity
      ).

  Lemma identity_associativity
        (w x y z : PreCategory) (f : Functor w x)
        (g : Functor x y) (h : Functor y z)
  : associator_1 h g f o (1 oR f o 1) =
    h oL 1 o (1 o @morphism_isomorphic _ _ _ (idtoiso (w -> z) (ap idmap (Functor.Composition.Laws.associativity f g h)))).
  Proof.
    t.
  Defined.

  Lemma identity_left_identity
        (x y : PreCategory) (f : Functor x y)
  : 1 oR f o 1 =
    (left_identity_natural_transformation_2 f)
      o @morphism_isomorphic _ _ _ (idtoiso (x -> y) (ap idmap (Functor.Composition.Laws.left_identity f))).
  Proof.
    t.
  Defined.

  Lemma identity_right_identity
        (x y : PreCategory) (f : Functor x y)
  : f oL 1 o 1 =
    (right_identity_natural_transformation_2 f)
      o @morphism_isomorphic _ _ _ (idtoiso (x -> y) (ap idmap (Functor.Composition.Laws.right_identity f))).
  Proof.
    t.
  Defined.

  (** There is an identity pseudofunctor.  It does the obvious thing. *)
  Definition identity : Pseudofunctor cat
    := Build_Pseudofunctor
         cat
         (fun C => C.1)
         (fun _ _ F => F)
         (fun _ _ _ _ _ => reflexivity _)
         (fun _ => reflexivity _)
         (fun x y z w => @identity_associativity x.1 y.1 z.1 w.1)
         (fun x y => @identity_left_identity x.1 y.1)
         (fun x y => @identity_right_identity x.1 y.1).
End identity.

Module Export PseudofunctorIdentityNotations.
  Notation "1" := (identity _) : pseudofunctor_scope.
End PseudofunctorIdentityNotations.
