(** * Laws about composition of functors *)
Require Import Category.Core Functor.Core Functor.Composition.Core Functor.Identity.
Require Import Functor.Paths.
Require Import Basics.PathGroupoids HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section identity_lemmas.
  Context `{Funext}.

  Variables C D : PreCategory.

  Local Open Scope functor_scope.

  (** ** left identity : [1 ∘ F = F] *)
  (** If we had that [match (p : a = b) in (_ = y) return (a = y) with idpath => idpath end ≡ p] (a form of eta for paths), this would be judgemental. *)
  Lemma left_identity (F : Functor C D) : 1 o F = F.
  Proof.
    by path_functor.
  Defined.

  (** ** right identity : [F ∘ 1 = F] *)
  Lemma right_identity (F : Functor C D) : F o 1 = F.
  Proof.
    by path_functor.
  Defined.

  (** ** Action of left and right identity laws on objects *)
  Definition left_identity_fst F
  : ap object_of (left_identity F) = idpath
    := @path_functor_uncurried_fst _ _ _ (1 o F) F 1 1.

  Definition right_identity_fst F
  : ap object_of (right_identity F) = idpath
    := @path_functor_uncurried_fst _ _ _ (F o 1) F 1 1.
End identity_lemmas.

Hint Rewrite @left_identity @right_identity : category.
Hint Rewrite @left_identity @right_identity : functor.
Hint Immediate @left_identity @right_identity : category functor.

Section composition_lemmas.
  Context `{fs : Funext}.

  Variables B C D E : PreCategory.

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
    := @path_functor_uncurried_fst _ _ _ ((H o G) o F) (H o (G o F)) 1%path 1%path.
End composition_lemmas.

Hint Resolve @associativity : category functor.

Section coherence.
  Context `{fs : Funext}.

  Local Open Scope path_scope.
  Local Open Scope functor_scope.

  Local Ltac coherence_t :=
    repeat match goal with
             | [ |- _ = _ :> (_ = _ :> Functor _ _) ] => apply path_path_functor_uncurried
             | _ => reflexivity
             | _ => progress rewrite ?ap_pp, ?concat_1p, ?concat_p1
             | _ => progress rewrite ?associativity_fst, ?left_identity_fst, ?right_identity_fst
             | _ => progress push_ap_object_of
           end.

  (** ** coherence triangle *)
  (** The following triangle is coherent
<<
      G ∘ (1 ∘ F) === (G ∘ 1) ∘ F
            \\           //
             \\         //
              \\       //
               \\     //
                \\   //
                 \\ //
                 G ∘ F
>> *)
  Lemma triangle C D E (F : Functor C D) (G : Functor D E)
  : (associativity F 1 G @ ap (compose G) (left_identity F))
    = (ap (fun G' : Functor D E => G' o F) (right_identity G)).
  Proof.
    coherence_t.
  Qed.

  (** ** coherence pentagon *)
  (** The following pentagon is coherent
<<
                  K ∘ (H ∘ (G ∘ F))
                  //             \\
                 //               \\
                //                 \\
               //                   \\
              //                     \\
      (K ∘ H) ∘ (G ∘ F)        K ∘ ((H ∘ G) ∘ F)
              ||                      ||
              ||                      ||
              ||                      ||
              ||                      ||
              ||                      ||
      ((K ∘ H) ∘ G) ∘ F ====== (K ∘ (H ∘ G)) ∘ F
>> *)
  Lemma pentagon A B C D E
        (F : Functor A B) (G : Functor B C) (H : Functor C D) (K : Functor D E)
  : (associativity F G (K o H) @ associativity (G o F) H K)
    = (ap (fun KHG => KHG o F) (associativity G H K) @ associativity F (H o G) K @ ap (compose K) (associativity F G H)).
  Proof.
    coherence_t.
  Qed.
End coherence.

Arguments associativity : simpl never.
Arguments left_identity : simpl never.
Arguments right_identity : simpl never.
