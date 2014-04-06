(** * Morphisms in cat *)
Require Import Category.Core Functor.Core FunctorCategory.Core FunctorCategory.Morphisms NaturalTransformation.Core.
Require Import Category.Morphisms.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

(** ** Lemmas relationship between transporting the action of functors on objects, and [idtoiso] *)
Section iso_lemmas.
  Context `{Funext}.

  Variable C : PreCategory.

  Variables s d : C.
  Variables m1 m2 : morphism C s d.
  Variable p : m1 = m2.

  Variable Fs : PreCategory.
  Variable Fd : PreCategory.
  Variable Fm : morphism C s d -> Functor Fs Fd.

  Lemma transport_Fc_to_idtoiso
        s' d' u
  : @transport _ (fun m => morphism _ (Fm m s') d') _ _ p u
    = u o components_of (Category.Morphisms.idtoiso (_ -> _) (ap Fm p) : morphism _ _ _)^-1 s'.
  Proof.
    case p; clear p; simpl; autorewrite with morphism; reflexivity.
  Qed.

  Lemma transport_cF_to_idtoiso
        s' d' u
  : @transport _ (fun m => morphism _ s' (Fm m d')) _ _ p u
    = components_of (Category.Morphisms.idtoiso (_ -> _) (ap Fm p) : morphism _ _ _) d' o u.
  Proof.
    case p; clear p; simpl; autorewrite with morphism; reflexivity.
  Qed.
End iso_lemmas.
