(** * Identity pseudofunctor *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import NaturalTransformation.Isomorphisms.
Require Import NaturalTransformation.Paths.
Require Import Cat.Core.
Require Import Pseudofunctor.Core.
Require Import PathGroupoids.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Section identity.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation cat := (@sub_pre_cat _ P HF).

  (** There is an identity pseudofunctor.  It does the obvious thing. *)
  Definition identity : Pseudofunctor cat.
  Proof.
    refine (Build_Pseudofunctor
              cat
              (fun C => C.1)
              (fun _ _ F => F)
              (fun _ _ _ _ _ => reflexivity _)
              (fun _ => reflexivity _)
              _
              _
              _);
      simpl;
      intros;
      path_natural_transformation;
      abstract (
          autorewrite with functor morphism;
          rewrite ap_idmap, idtoiso_components_of;
          rewrite ?Functor.Composition.Laws.associativity_fst,
          ?Functor.Composition.Laws.left_identity_fst,
          ?Functor.Composition.Laws.right_identity_fst;
          reflexivity
        ).
  Defined.
End identity.

Module Export PseudofunctorIdentityNotations.
  Notation "1" := (identity _) : pseudofunctor_scope.
End PseudofunctorIdentityNotations.
