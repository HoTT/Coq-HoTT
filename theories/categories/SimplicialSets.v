(** * The simplex category Δ, and the precategory of simplicial sets, [Δᵒᵖ → set] *)
Require Import Category.Core Functor.Core.
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

Module Export Core.
  Section simplicial_sets.
    Context `{Funext}.

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
