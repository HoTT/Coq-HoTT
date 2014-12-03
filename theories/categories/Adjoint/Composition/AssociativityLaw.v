(** * Associativity of adjunction composition *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core.
Require Import Functor.Composition.Laws.
Require Import Adjoint.Composition.Core Adjoint.UnitCounit Adjoint.Core Adjoint.Paths Adjoint.Identity.
Require Adjoint.Composition.LawsTactic.
Require Import Types.Sigma HoTT.Tactics Types.Prod Basics.PathGroupoids Types.Forall.

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

Hint Resolve @associativity : category.
