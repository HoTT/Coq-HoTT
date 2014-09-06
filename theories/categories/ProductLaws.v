(** * Laws about product categories *)
Require Import Category.Core Functor.Core InitialTerminalCategory.Core InitialTerminalCategory.Functors Category.Prod Functor.Prod Functor.Composition.Core Functor.Identity Functor.Prod.Universal Functor.Composition.Laws Functor.Prod.Universal.
Require Import Functor.Paths.
Require Import types.Prod types.Forall HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope functor_scope.

Local Notation prod_type := Coq.Init.Datatypes.prod.
Local Notation fst_type := Coq.Init.Datatypes.fst.
Local Notation snd_type := Coq.Init.Datatypes.snd.
Local Notation pair_type := Coq.Init.Datatypes.pair.

(** ** Swap functor [C × D → D × C] *)
Module Swap.
  Definition functor (C D : PreCategory)
  : Functor (C * D) (D * C)
    := Build_Functor (C * D) (D * C)
                     (fun cd => (snd_type cd, fst_type cd)%core)
                     (fun _ _ m => (snd_type m, fst_type m)%core)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Definition law (C D : PreCategory)
  : functor C D o functor D C = 1
    := idpath.
End Swap.

(** ** Laws about the initial category [0] *)
Module Law0.
  Section law0.
    Context `{Funext}.
    Context `{IsInitialCategory zero}.
    Local Notation "0" := zero : category_scope.

    Variable C : PreCategory.

    Global Instance is_initial_category__product
    : IsInitialCategory (C * 0)
      := fun P c => initial_category_rect P (snd c).

    Global Instance is_initial_category__product'
    : IsInitialCategory (0 * C)
      := fun P c => initial_category_rect P (fst c).

    Definition functor : Functor (C * 0) 0 := Functors.from_initial _.
    Definition functor' : Functor (0 * C) 0 := Functors.from_initial _.
    Definition inverse : Functor 0 (C * 0) := Functors.from_initial _.
    Definition inverse' : Functor 0 (0 * C) := Functors.from_initial _.

    (** *** [C × 0 ≅ 0] *)
    Definition law
    : functor o inverse = 1
      /\ inverse o functor = 1
      := center _.

    (** *** [0 × C ≅ 0] *)
    Definition law'
    : functor' o inverse' = 1
      /\ inverse' o functor' = 1
      := center _.
  End law0.
End Law0.

(** ** Laws about the terminal category [1] *)
Module Law1.
  Section law1.
    Context `{Funext}.
    Context `{IsTerminalCategory one}.
    Local Notation "1" := one : category_scope.
    Variable C : PreCategory.

    Definition functor : Functor (C * 1) C
      := fst.

    Definition functor' : Functor (1 * C) C
      := snd.

    Definition inverse : Functor C (C * 1)
      := 1 * Functors.to_terminal _.

    Definition inverse' : Functor C (1 * C)
      := Functors.to_terminal _ * 1.

    (** We could throw this in a [repeat match goal with ... end], but
      we know the order, so we hard-code the order to speed it up by a
      factor of about 10. *)

    Local Ltac t_prod :=
      split;
      try first [ exact (compose_fst_prod _ _)
                | exact (compose_snd_prod _ _) ];
      [];
      apply Functor.Prod.Universal.path_prod;
      rewrite <- !Functor.Composition.Laws.associativity by assumption;
      (rewrite ?compose_fst_prod, ?compose_snd_prod,
       ?Functor.Composition.Laws.left_identity,
       ?Functor.Composition.Laws.right_identity
        by assumption);
      try (reflexivity || exact (center _)).

    (** *** [C × 1 ≅ C] *)
    Lemma law1
    : functor o inverse = 1
      /\ inverse o functor = 1.
    Proof.
      unfold functor, inverse.
      t_prod.
    Qed.

    (** *** [1 × C ≅ C] *)
    Lemma law1'
    : functor' o inverse' = 1
      /\ inverse' o functor' = 1.
    Proof.
      unfold functor', inverse'.
      t_prod.
    Qed.
  End law1.
End Law1.
