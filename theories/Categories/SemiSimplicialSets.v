(** * The category of semisimplicial sets *)
Require Import Types.
Require Import Category.Core Functor.Core.
Require Import Category.Morphisms.
Require Import Category.Dual FunctorCategory.Core.
Require Import SetCategory.Core.
Require Import SimplicialSets.
Require Import Category.Sigma.OnMorphisms Category.Subcategory.Wide.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

Module Export Core.
  Section semisimplicial_sets.
    Context `{Funext}.
    (** Quoting David Spivak:

        Consider the subcategory of [Δ] with the same objects (wide)
        but only injective morphisms.  If we call that [Γ] (which is
        nonstandard), then semi-simplicial sets (also a non-standard
        term) (sic) are [Fun(Γᵒᵖ, Set)]. Define the obvious inclusion
        [Γ -> Δ], which we will use to make simplicial sets without
        having to worry about "degneracies". *)

    Definition semisimplex_category : PreCategory
      := wide simplex_category
              (@IsMonomorphism _)
              _ _ _.

    Definition semisimplicial_inclusion_functor : semisimplex_category -> simplex_category
      := pr1_mor.

    Definition semisimplicial_category (C : PreCategory) : PreCategory
      := semisimplex_category^op -> C.

    Definition semisimplicial_set := semisimplicial_category set_cat.
    Definition semisimplicial_prop := semisimplicial_category prop_cat.
  End semisimplicial_sets.

  Notation semisimplicial_of obj := (semisimplicial_category (cat_of obj)).
End Core.
