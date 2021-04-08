(** * Left and right identity laws of adjunction composition *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.NaturalTransformation.Core.
Require Import HoTT.Categories.Functor.Composition.Core.
Require Import HoTT.Categories.Functor.Composition.Laws.
Require Import HoTT.Categories.Adjoint.Composition.Core HoTT.Categories.Adjoint.UnitCounit HoTT.Categories.Adjoint.Core HoTT.Categories.Adjoint.Paths HoTT.Categories.Adjoint.Identity.
Require HoTT.Categories.Adjoint.Composition.LawsTactic.
Require Import HoTT.Types.Sigma HoTT.Tactics HoTT.Types.Prod HoTT.Basics.PathGroupoids HoTT.Types.Forall.

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

  Variables C D : PreCategory.

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
               (Functor.Composition.Laws.right_identity _))).
    Adjoint.Composition.LawsTactic.law_t.
  Qed.

  Lemma right_identity
  : ((_, _); A o 1) = ((_, _); A) :> AdjunctionWithFunctors C D.
  Proof.
    apply path_sigma_uncurried; simpl.
    (exists (path_prod'
               (Functor.Composition.Laws.right_identity _)
               (Functor.Composition.Laws.left_identity _))).
    Adjoint.Composition.LawsTactic.law_t.
  Qed.
End identity_lemmas.

Hint Rewrite @left_identity @right_identity : category.
#[export]
Hint Immediate left_identity right_identity : category.
