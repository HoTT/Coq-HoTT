(** * The simplex category Δ, and the precategory of simplicial sets, [Δᵒᵖ → set] *)
From HoTT Require Import Basics Types Spaces.Nat.Core.
Require Import Category.Core Functor.Core Functor.Paths.
Require Import SetCategory.Core.
Require Import ChainCategory FunctorCategory.Core.
Require Import Category.Dual.
Require Import Functor.Identity Functor.Composition.Core Functor.Composition.Laws.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.
Local Open Scope category_scope.

(** We define the precategory Δ of simplices, or finite non-empty linear
    orders *)

Module Export Core.
  Section simplicial_sets.
    Context `{Funext}.

    (** We say that the objects of Δ are natural numbers, where a
        number [n] is morally considered as the canonical [n]-simplex,
        a finite linear order on [n + 1] elements.  By declaring
        [chain] to be a local coercion from [nat] to [PreCategory], we
        can rely on on-the-fly eta-expansion to make this moral
        consideration a reality, telling Coq that it can unify, for
        example, [nat -> nat -> Type] with [PreCategory -> PreCategory
        -> Type] by silently inserting [chain]. *)

    Local Coercion chain : nat >-> PreCategory.

    Definition simplex_category
      := @Build_PreCategory
           nat
           Functor
           identity
           compose
           associativity
           left_identity
           right_identity
           _.

    Definition simplicial_category (C : PreCategory) : PreCategory
      := simplex_category^op -> C.

    Definition simplicial_set := simplicial_category set_cat.
    Definition simplicial_prop := simplicial_category prop_cat.
  End simplicial_sets.

  Notation simplicial_of obj := (simplicial_category (cat_of obj)).
End Core.

Module Utf8.
  Notation Δ := simplex_category.
End Utf8.
