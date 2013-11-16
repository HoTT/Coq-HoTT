Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core.
Require Import Functor.Composition.Laws.
Require Import Adjoint.Composition.Core Adjoint.UnitCounit Adjoint.Core Adjoint.Paths Adjoint.Identity.
Require Import types.Sigma HoTT.Tactics types.Prod HoTT.PathGroupoids types.Forall.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope adjunction_scope.
Local Open Scope morphism_scope.

Section laws.
  Local Notation AdjunctionWithFunctors C D :=
    { fg : Functor C D * Functor D C
    | fst fg -| snd fg }.

  Local Ltac law_t :=
    rewrite !transport_path_prod'; simpl;
    path_adjunction; simpl;
    repeat match goal with
             | [ |- appcontext[unit (transport ?P ?p ?z)] ]
               => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => @unit _ _ _ _) z)
             | [ |- appcontext[counit (transport ?P ?p ?z)] ]
               => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => @counit _ _ _ _) z)
             | [ |- appcontext[components_of (transport ?P ?p ?z)] ]
               => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => @components_of _ _ _ _) z)
           end;
    rewrite !transport_forall_constant;
    repeat
      match goal with
        | [ |- appcontext[transport (fun y => ?f (@object_of ?C ?D y ?x))] ]
          => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (y x)) (@object_of C D))
        | [ |- appcontext[transport (fun y => ?f (?g (@object_of ?C ?D y ?x)))] ]
          => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (g (y x))) (@object_of C D))
        | [ |- appcontext[transport (fun y => ?f (?g (?h (?i (@object_of ?C ?D y ?x)))))] ]
          => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (g (h (i (y x))))) (@object_of C D))
        | [ |- appcontext[transport (fun y => ?f (@object_of ?C ?D y ?x) ?z)] ]
          => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (y x) z) (@object_of C D))
        | [ |- appcontext[transport (fun y => ?f (?g (@object_of ?C ?D y ?x)) ?z)] ]
          => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (g (y x)) z) (@object_of C D))
        | [ |- appcontext[transport (fun y => ?f (?g (?h (?i (@object_of ?C ?D y ?x)))) ?z)] ]
          => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (g (h (i (y x)))) z) (@object_of C D))
      end;
    unfold symmetry, symmetric_paths;
    rewrite ?ap_V;
    rewrite ?left_identity_fst, ?right_identity_fst, ?associativity_fst;
    simpl;
    repeat (
        rewrite
          ?identity_of,
        ?composition_of,
        ?Category.Core.left_identity,
        ?Category.Core.right_identity,
        ?Category.Core.associativity
      );
    try reflexivity.

  Section identity_lemmas.
    Context `{Funext}.

    Variable C : PreCategory.
    Variable D : PreCategory.

    Variable F : Functor C D.
    Variable G : Functor D C.

    Variable A : F -| G.

    Local Open Scope adjunction_scope.

    Local Transparent left_identity right_identity.


    Lemma left_identity
    : ((_, _); 1 o A) = ((_, _); A) :> AdjunctionWithFunctors C D.
    Proof.
      apply path_sigma_uncurried; simpl.
      (exists (path_prod'
                 (Functor.Composition.Laws.left_identity _)
                 (Functor.Composition.Laws.left_identity _))).
      law_t.
    Qed.

    Lemma right_identity
    : ((_, _); A o 1) = ((_, _); A) :> AdjunctionWithFunctors C D.
    Proof.
      apply path_sigma_uncurried; simpl.
      (exists (path_prod'
                 (Functor.Composition.Laws.right_identity _)
                 (Functor.Composition.Laws.right_identity _))).
      law_t.
    Qed.
  End identity_lemmas.

  Section composition_lemmas.
    Context `{H0 : Funext}.

    Variable B : PreCategory.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable E : PreCategory.

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
      law_t.
    Qed.
  End composition_lemmas.
End laws.

Hint Rewrite @left_identity @right_identity : category.
Hint Immediate @left_identity @right_identity : category.

Hint Resolve @associativity : category.
