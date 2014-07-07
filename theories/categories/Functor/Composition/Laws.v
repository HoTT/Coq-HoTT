(** * Laws about composition of functors *)
Require Import Category.Core Functor.Core Functor.Composition.Core Functor.Identity.
Require Import Functor.Paths.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section identity_lemmas.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Context `{Funext}.

  Local Open Scope functor_scope.

  (** ** left identity : [1 ∘ F = F] *)
  (** If we had that [match (p : a = b) in (_ = y) return (a = y) with idpath => idpath end ≡ p] (a form of eta for paths), this would be judgemental. *)
  Lemma left_identity (F : Functor D C) : identity _ o F = F.
  Proof.
    by path_functor.
  Defined.

  (** ** right identity : [F ∘ 1 = F] *)
  Lemma right_identity (F : Functor C D) : F o identity _ = F.
  Proof.
    by path_functor.
  Defined.

  (** ** Action of left and right identity laws on objects *)
  Definition left_identity_fst F
  : ap object_of (left_identity F) = idpath
    := @path_functor'_sig_fst _ _ _ (identity C o F) F 1%path 1%path.

  Definition right_identity_fst F
  : ap object_of (right_identity F) = idpath
    := @path_functor'_sig_fst _ _ _ (F o identity C) F 1%path 1%path.
End identity_lemmas.

Hint Rewrite @left_identity @right_identity : category.
Hint Rewrite @left_identity @right_identity : functor.
Hint Immediate @left_identity @right_identity : category functor.

Section composition_lemmas.
  Context `{fs : Funext}.

  Variable B : PreCategory.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Local Open Scope functor_scope.

  (** ** associativity : [(H ∘ G) ∘ F = H ∘ (G ∘ F)] *)
  Lemma associativity
        (F : Functor B C) (G : Functor C D) (H : Functor D E)
  : (H o G) o F = H o (G o F).
  Proof.
    by path_functor.
  Defined.

  (** ** Action of associativity on objects *)
  Definition associativity_fst F G H
  : ap object_of (associativity F G H) = idpath
    := @path_functor'_sig_fst _ _ _ ((H o G) o F) (H o (G o F)) 1%path 1%path.
End composition_lemmas.

Hint Resolve @associativity : category functor.

Arguments associativity : simpl never.
Arguments left_identity : simpl never.
Arguments right_identity : simpl never.
