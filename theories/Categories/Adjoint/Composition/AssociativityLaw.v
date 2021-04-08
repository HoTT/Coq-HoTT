(** * Associativity of adjunction composition *)
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

Section composition_lemmas.
  Local Notation AdjunctionWithFunctors C D :=
    { fg : Functor C D * Functor D C
    | fst fg -| snd fg }.

  Context `{H0 : Funext}.

  Variables B C D E : PreCategory.

  Variable F : Functor B C.
  Variable F' : Functor C B.
  Variable G : Functor C D.
  Variable G' : Functor D C.
  Variable H : Functor D E.
  Variable H' : Functor E D.

  Variable AF : F -| F'.
  Variable AG : G -| G'.
  Variable AH : H -| H'.

  Local Open Scope adjunction_scope.

  Lemma associativity
  : ((_, _); (AH o AG) o AF) = ((_, _); AH o (AG o AF)) :> AdjunctionWithFunctors B E.
  Proof.
    apply path_sigma_uncurried; simpl.
    (exists (path_prod'
               (Functor.Composition.Laws.associativity _ _ _)
               (symmetry _ _ (Functor.Composition.Laws.associativity _ _ _))));
      Adjoint.Composition.LawsTactic.law_t.
  Qed.
End composition_lemmas.

#[export]
Hint Resolve associativity : category.
