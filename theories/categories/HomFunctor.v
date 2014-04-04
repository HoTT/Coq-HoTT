Require Import Category.Core Functor.Core SetCategory.Core Category.Dual Functor.Composition.Core.
Require Category.Prod Functor.Prod.
Import Category.Prod.CategoryProdNotations Functor.Prod.FunctorProdNotations.
Require Import HSet Overture FunextVarieties.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section hom_functor.
  Context `{Funext}.
  Variable C : PreCategory.

  Local Notation obj_of c'c :=
    (BuildhSet
       (morphism
          C
          (fst (c'c : object (C^op * C)))
          (snd (c'c : object (C^op * C))))
       _).

  Let hom_functor_morphism_of s's d'd (hf : morphism (C^op * C) s's d'd)
  : morphism set_cat (obj_of s's) (obj_of d'd)
    := fun g => snd hf o g o fst hf.

  Definition hom_functor : Functor (C^op * C) set_cat.
    refine (Build_Functor (C^op * C) set_cat
                          (fun c'c => obj_of c'c)
                          hom_functor_morphism_of
                          _
                          _);
    subst hom_functor_morphism_of;
    simpl;
    (* TODO: I don't want to have to give [Funext_downward_closed] explicitly here. *)
    abstract (
        repeat (apply (@path_forall Funext_downward_closed) || intros [] || intro);
        unfold compose, Overture.compose;
        simpl in *;
        rewrite <- ?associativity, ?left_identity, ?right_identity;
        reflexivity
      ).
  Defined.
End hom_functor.

Section covariant_contravariant.
  Context `{Funext}.
  Variable C : PreCategory.

  Local Open Scope functor_scope.

  Local Arguments Functor.Prod.induced_snd / .
  Local Arguments Functor.Prod.induced_fst / .

  Definition covariant_hom_functor (A : object C^op)
    := Eval simpl in Functor.Prod.induced_snd (hom_functor C) A.
  Definition contravariant_hom_functor (A : C)
    := Eval simpl in Functor.Prod.induced_fst (hom_functor C) A.
End covariant_contravariant.
