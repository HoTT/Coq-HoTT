Require Export Category.Core Functor.Core Functor.Composition Functor.Identity.
Require Import Functor.Paths.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section functor_identityLemmas.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Context `{Funext}.

  Local Open Scope functor_scope.

  Local Transparent functor_compose_identity_of.
  Local Transparent functor_compose_composition_of.

  (** If we had that [match (p : a = b) in (_ = y) return (a = y) with idpath => idpath end ≡ p] (a form of eta for paths), this would be judgemental. *)
  Lemma functor_left_identity (F : Functor D C) : functor_identity _ o F = F.
  Proof.
    by path_functor.
  Defined.

  Lemma functor_right_identity (F : Functor C D) : F o functor_identity _ = F.
  Proof.
    by path_functor.
  Defined.

  Definition functor_left_identity_fst F
  : ap object_of (functor_left_identity F) = idpath
    := @path_functor'_sig_fst _ _ _ (functor_identity C o F) F 1%path 1%path.

  Definition functor_right_identity_fst F
  : ap object_of (functor_right_identity F) = idpath
    := @path_functor'_sig_fst _ _ _ (F o functor_identity C) F 1%path 1%path.
End functor_identityLemmas.

Hint Rewrite @functor_left_identity @functor_right_identity : category.
Hint Rewrite @functor_left_identity @functor_right_identity : functor.
Hint Immediate @functor_left_identity @functor_right_identity : category functor.

Section FunctorCompositionLemmas.
  Variable B : PreCategory.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Context `{H0 : Funext}.

  Local Open Scope functor_scope.

  Local Transparent functor_compose_composition_of.
  Local Transparent functor_compose_identity_of.

  Lemma functor_compose_associativity
        (F : Functor B C) (G : Functor C D) (H : Functor D E)
  : (H o G) o F = H o (G o F).
  Proof.
    by path_functor.
  Defined.

  Definition functor_compose_associativity_fst F G H
  : ap object_of (functor_compose_associativity F G H) = idpath
    := @path_functor'_sig_fst _ _ _ ((H o G) o F) (H o (G o F)) 1%path 1%path.
End FunctorCompositionLemmas.

Hint Resolve @functor_compose_associativity : category functor.

Opaque functor_compose_associativity functor_left_identity functor_right_identity.
