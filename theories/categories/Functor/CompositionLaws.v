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

  Local Transparent compose_functors_identity_of.
  Local Transparent compose_functors_composition_of.

  (** If we had that [match (p : a = b) in (_ = y) return (a = y) with idpath => idpath end ≡ p] (a form of eta for paths), this would be judgemental. *)
  Lemma left_functor_identity (F : Functor D C) : functor_identity _ o F = F.
  Proof.
    by paths_functor.
  Defined.

  Lemma right_functor_identity (F : Functor C D) : F o functor_identity _ = F.
  Proof.
    by paths_functor.
  Defined.

  Definition left_functor_identity_fst F
  : ap object_of (left_functor_identity F) = idpath
    := @paths'_functor_sig_fst _ _ _ (functor_identity C o F) F 1%path 1%path.

  Definition right_functor_identity_fst F
  : ap object_of (right_functor_identity F) = idpath
    := @paths'_functor_sig_fst _ _ _ (F o functor_identity C) F 1%path 1%path.
End functor_identityLemmas.

Hint Rewrite @left_functor_identity @right_functor_identity : category.
Hint Rewrite @left_functor_identity @right_functor_identity : functor.
Hint Immediate @left_functor_identity @right_functor_identity : category functor.

Section FunctorCompositionLemmas.
  Variable B : PreCategory.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Context `{H0 : Funext}.

  Local Open Scope functor_scope.

  Local Transparent compose_functors_composition_of.
  Local Transparent compose_functors_identity_of.

  Lemma associativity_functor_composition
        (F : Functor B C) (G : Functor C D) (H : Functor D E)
  : (H o G) o F = H o (G o F).
  Proof.
    by paths_functor.
  Defined.

  Definition associativity_functor_composition_fst F G H
  : ap object_of (associativity_functor_composition F G H) = idpath
    := @paths'_functor_sig_fst _ _ _ ((H o G) o F) (H o (G o F)) 1%path 1%path.
End FunctorCompositionLemmas.

Hint Resolve @associativity_functor_composition : category functor.

Opaque associativity_functor_composition left_functor_identity right_functor_identity.
