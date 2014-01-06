Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core.
Require Import Functor.Composition.Laws.
Require Import Adjoint.Composition.Core Adjoint.UnitCounit Adjoint.Core Adjoint.Paths Adjoint.Identity.
Require Adjoint.Composition.LawsTactic.
Require Import types.Sigma HoTT.Tactics types.Prod HoTT.PathGroupoids types.Forall.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope adjunction_scope.
Local Open Scope morphism_scope.

Section identity_lemmas.
  Local Notation AdjunctionWithFunctors C D :=
    { fg : Functor C D * Functor D C
    | fst fg -| snd fg }.

  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.

  Variable F : Functor C D.
  Variable G : Functor D C.

  Variable A : F -| G.

  Local Open Scope adjunction_scope.

  Lemma left_identity
  : ((_, _); 1 o A) = ((_, _); A) :> AdjunctionWithFunctors C D.
  Proof.
    apply path_sigma_uncurried; simpl.
    (exists (path_prod'
               (Functor.Composition.Laws.left_identity _)
               (Functor.Composition.Laws.left_identity _))).
    Adjoint.Composition.LawsTactic.law_t.
  Qed.

  Lemma right_identity
  : ((_, _); A o 1) = ((_, _); A) :> AdjunctionWithFunctors C D.
  Proof.
    apply path_sigma_uncurried; simpl.
    (exists (path_prod'
               (Functor.Composition.Laws.right_identity _)
               (Functor.Composition.Laws.right_identity _))).
    Adjoint.Composition.LawsTactic.law_t.
  Qed.
End identity_lemmas.

Hint Rewrite @left_identity @right_identity : category.
Hint Immediate @left_identity @right_identity : category.
