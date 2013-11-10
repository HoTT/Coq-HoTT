Require Import Category.Core Functor.Core.
Require Import Category.Prod Functor.Prod.
Require Import Functor.Composition Functor.Identity.
Require Import InitialTerminalCategory.
Require Import Comma.Core.
Require Import types.Prod.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.
Local Open Scope category_scope.

Section comma_category.
  Variable A : PreCategory.
  Variable B : PreCategory.
  Variable C : PreCategory.
  Variable S : Functor A C.
  Variable T : Functor B C.

  Definition comma_category_projection : Functor (S |v| T) (A * B)
    := Build_Functor
         (S |v| T) (A * B)
         (fun abf => (CommaCategory.a abf, CommaCategory.b abf)%core)
         (fun _ _ m => (CommaCategory.g m, CommaCategory.h m)%core)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).
End comma_category.

Section slice_category.
  Variable A : PreCategory.

  Local Arguments Functor.Composition.compose / .
  Local Arguments Functor.Composition.compose_composition_of / .
  Local Arguments Functor.Composition.compose_identity_of / .
  Local Arguments path_prod / .
  Local Arguments path_prod' / .
  Local Arguments path_prod_uncurried / .
  Local Transparent Functor.Composition.compose_composition_of.
  Local Transparent Functor.Composition.compose_identity_of.

  Definition arrow_category_projection : Functor (arrow_category A) A
    := Eval simpl in fst o comma_category_projection _ 1.

  Definition slice_category_over_projection (a : A) : Functor (A / a) A
    := Eval simpl in fst o comma_category_projection 1 _.

  Definition coslice_category_over_projection (a : A) : Functor (a \ A) A
    := Eval simpl in snd o comma_category_projection _ 1.

  Section slice_coslice.
    Variable C : PreCategory.
    Variable a : C.
    Variable S : Functor A C.

    Definition slice_category_projection : Functor (S |v| a) A
      := Eval simpl in fst o comma_category_projection S !a.

    Definition coslice_category_projection : Functor (a |v| S) A
      := Eval simpl in snd o comma_category_projection !a S.
  End slice_coslice.
End slice_category.
