(** * Hom Functor *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.SetCategory.Core HoTT.Categories.Category.Dual HoTT.Categories.Functor.Composition.Core.
Require HoTT.Categories.Category.Prod HoTT.Categories.Functor.Prod.Core.
Import Category.Prod.CategoryProdNotations Functor.Prod.Core.FunctorProdCoreNotations.
Require Import HoTT.Basics.Trunc HoTT.HSet HoTT.TruncType.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

(** ** Definition of [hom : Cᵒᵖ × C → Set] as a functor *)
Section hom_functor.
  Context `{Funext}.
  Variable C : PreCategory.

  Local Notation obj_of c'c :=
    (BuildhSet
       (morphism
          C
          (fst (c'c : object (C^op * C)))
          (snd (c'c : object (C^op * C))))).

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
    abstract (
        repeat (apply path_forall || intros [] || intro);
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

  Local Arguments Functor.Prod.Core.induced_snd / .
  Local Arguments Functor.Prod.Core.induced_fst / .

  (** ** Covariant hom functor [hom_C(A, ─) : C → set] *)
  Definition covariant_hom_functor (A : object C^op)
    := Eval simpl in Functor.Prod.Core.induced_snd (hom_functor C) A.
  (** ** Contravariant hom functor [hom_C(─, A) : Cᵒᵖ → set] *)
  Definition contravariant_hom_functor (A : C)
    := Eval simpl in Functor.Prod.Core.induced_fst (hom_functor C) A.
End covariant_contravariant.
