Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import FunctorCategory.Core Functor.Composition.Core NaturalTransformation.Composition.Core NaturalTransformation.Composition.Laws.
Require Import FunextVarieties.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

Section functorial_composition.
  Context `{fs : Funext, fs' : Funext, fs'' : Funext, fs''' : Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Local Open Scope natural_transformation_scope.

  Definition whiskerL_functor (F : @functor_category fs D E)
  : (@functor_category fs' (@functor_category fs'' C D) (@functor_category fs''' C E))
    := Build_Functor
         (C -> D) (C -> E)
         (fun G => F o G)%functor
         (fun _ _ T => F oL T)
         (fun _ _ _ _ _ => @composition_of_whisker_l Funext_downward_closed _ _ _ _ _ _ _ _ _)
         (fun _ => @whisker_l_right_identity Funext_downward_closed _ _ _ _ _).

  Definition whiskerR_functor (G : @functor_category fs C D)
  : (@functor_category fs' (@functor_category fs'' D E) (@functor_category fs''' C E))
    := Build_Functor
         (D -> E) (C -> E)
         (fun F => F o G)%functor
         (fun _ _ T => T oR G)
         (fun _ _ _ _ _ => @composition_of_whisker_r Funext_downward_closed _ _ _ _ _ _ _ _ _)
         (fun _ => @whisker_r_left_identity Funext_downward_closed _ _ _ _ _).
End functorial_composition.
