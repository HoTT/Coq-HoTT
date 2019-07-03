(** * Functors to cat are pseudofunctors *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core NaturalTransformation.Composition.Core NaturalTransformation.Composition.Laws.
Require Import Functor.Identity.
Require Import Pseudofunctor.Core.
Require Import Cat.Core.
Require Import FunctorCategory.Core.
Require Import FunctorCategory.Morphisms NaturalTransformation.Isomorphisms.
Require Import Category.Morphisms NaturalTransformation.Paths.
Require Import Basics.PathGroupoids Basics.Trunc.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.
Local Open Scope morphism_scope.

(** Every functor to Cat is a pseudofunctor *)
Section of_functor.
  Context `{Funext}.
  Variable C : PreCategory.
  Context `{HP : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation cat := (@sub_pre_cat _ P HP).

  Variable F : Functor C cat.

  Definition path_functor_helper A B (F1 F2 : Functor A B) (pf1 pf2 : F1 = F2)
  : P A -> P B -> pf1 = pf2
    := fun PA PB => @path_ishprop _ (@HP A B PA PB F1 F2) _ _.

  Local Hint Extern 0 (P ?x.1) => exact x.2 : core.

  Local Tactic Notation "transitivity_idtoiso" open_constr(hyp) :=
    lazymatch goal with
      | [ |- ?f (Category.Morphisms.idtoiso ?C _) = _ ] => etransitivity (f (Category.Morphisms.idtoiso C hyp));
                                       [ do 2 refine (ap _ _); (* https://coq.inria.fr/bugs/show_bug.cgi?id=3626 *)
                                         apply path_functor_helper;
                                         simpl; trivial
                                       | path_natural_transformation ]
    end.

  Local Ltac pseudofunctor_t :=
    intros;
    unfold natural_transformation_of_natural_isomorphism;
    rewrite ?idtoiso_whisker_r, ?idtoiso_whisker_l;
    repeat (
        let C := match goal with |- @paths (@NaturalTransformation ?C ?D ?F ?G) _ _ => constr:((C -> D)%category) end in
        first [ eapply (@iso_moveL_pV C)
              | eapply (@iso_moveL_Vp C)
              | eapply (@iso_moveL_pM C)
              | eapply (@iso_moveL_Mp C) ];
        simpl
      );
    rewrite ?idtoiso_inv;
    simpl;
    change @NaturalTransformation.Composition.Core.compose
    with (fun C D F G H => Category.Core.compose (C := C -> D) (s := F) (d := G) (d' := H));
    cbv beta;
    rewrite ?idtoiso_comp;
    first [ transitivity_idtoiso (Functor.Composition.Laws.left_identity _)
          | transitivity_idtoiso ((Functor.Composition.Laws.left_identity _)^)
          | transitivity_idtoiso (Functor.Composition.Laws.right_identity _)
          | transitivity_idtoiso ((Functor.Composition.Laws.right_identity _)^)
          | transitivity_idtoiso (Functor.Composition.Laws.associativity _ _ _)
          | transitivity_idtoiso ((Functor.Composition.Laws.associativity _ _ _)^) ];
    rewrite eta_idtoiso;
    simpl;
    rewrite ?ap_V, ?Functor.Composition.Laws.left_identity_fst, ?Functor.Composition.Laws.right_identity_fst, ?Functor.Composition.Laws.associativity_fst;
    try reflexivity.

  (* The following helpers were generated with
<<
intros.
    repeat match goal with
             | [ |- context[idtoiso ?C (?f ?x)] ] => generalize (f x); intro
             | [ |- context[MorphismOf ?F ?f] ] => generalize dependent (MorphismOf F f); repeat (let x := fresh "x" in intro x)
             | [ |- context[ObjectOf ?F ?f] ] => generalize dependent (ObjectOf F f); repeat (let x := fresh "x" in intro x)
           end.
    simpl in *.
    unfold SubPreCatCat.
    simpl in *.
    clear.
    destruct_head_hnf @sigT.
    simpl in *.
    repeat match goal with
             | [ H : _ |- _ ] => revert H
           end.
    intros H P.
>> *)

  Lemma pseudofunctor_of_functor__composition_of
        {x0 x1 x2 x : PreCategory}
        {x7 x11 : Functor x0 x1}
        {x12 : x7 = x11}
        {x6 : Functor x0 x2} {x9 : Functor x2 x1}
        {x14 : x11 = (x9 o x6)%functor}
        {x4 : Functor x0 x} {x5 : Functor x x1}
        {x8 : x7 = (x5 o x4)%functor} {x10 : Functor x x2}
        {x13 : x6 = (x10 o x4)%functor} {x15 : x5 = (x9 o x10)%functor}
        (H0' : P x0) (H1' : P x1) (H2' : P x2) (H' : P x)
  : ((associator_1 x9 x10 x4)
       o ((idtoiso (x -> x1) x15 : morphism _ _ _)
            oR x4
            o (idtoiso (x0 -> x1) x8 : morphism _ _ _)))%natural_transformation
    = (x9
         oL (idtoiso (x0 -> x2) x13 : morphism _ _ _)
         o ((idtoiso (x0 -> x1) x14 : morphism _ _ _)
              o (idtoiso (x0 -> x1) x12 : morphism _ _ _)))%natural_transformation.
  Proof.
    clear F.
    symmetry; simpl; pseudofunctor_t.
  Qed.

  Lemma pseudofunctor_of_functor__left_identity_of
        {x0 x : PreCategory}
        {x2 : Functor x x} {x3 : x2 = 1%functor}
        {x4 x5 : Functor x0 x} {x6 : x4 = x5} {x7 : x4 = (x2 o x5)%functor}
        (H0' : P x0) (H' : P x)
  : ((Category.Morphisms.idtoiso (x -> x) x3 : morphism _ _ _)
       oR x5
       o (Category.Morphisms.idtoiso (x0 -> x) x7 : morphism _ _ _))%natural_transformation
    = ((NaturalTransformation.Composition.Laws.left_identity_natural_transformation_2 x5)
         o (Category.Morphisms.idtoiso (x0 -> x) x6 : morphism _ _ _))%natural_transformation.
  Proof.
    clear F.
    simpl; pseudofunctor_t.
  Qed.

  Lemma pseudofunctor_of_functor__right_identity_of
        {x0 x : PreCategory}
        {x4 : Functor x0 x0} {x5 : x4 = 1%functor}
        {x2 x3 : Functor x0 x} {x6 : x2 = x3} {x7 : x2 = (x3 o x4)%functor}
        (H0' : P x0) (H' : P x)
  : (x3
       oL (Category.Morphisms.idtoiso (x0 -> x0) x5 : morphism _ _ _)
       o (Category.Morphisms.idtoiso (x0 -> x) x7 : morphism _ _ _))%natural_transformation
    = ((NaturalTransformation.Composition.Laws.right_identity_natural_transformation_2 x3)
         o (Category.Morphisms.idtoiso (x0 -> x) x6 : morphism _ _ _))%natural_transformation.
  Proof.
    clear F.
    simpl; pseudofunctor_t.
  Qed.

  Definition pseudofunctor_of_functor : Pseudofunctor C
    := Build_Pseudofunctor
         C
         (fun x => pr1 (F x))
         (fun s d m => F _1 m)
         (fun s d d' m0 m1 => Category.Morphisms.idtoiso (_ -> _) (composition_of F _ _ _ m1 m0))
         (fun x => Category.Morphisms.idtoiso (_ -> _) (identity_of F x))
         (fun w x y z _ _ _ => pseudofunctor_of_functor__composition_of (F w).2 (F z).2 (F y).2 (F x).2)
         (fun x y _ => pseudofunctor_of_functor__left_identity_of (F x).2 (F y).2)
         (fun x y _ => pseudofunctor_of_functor__right_identity_of (F x).2 (F y).2).
End of_functor.

Definition FunctorToCat `{Funext} {C} `{HP : forall C D, P C -> P D -> IsHSet (Functor C D)}
  := Functor C (@sub_pre_cat _ P HP).
Identity Coercion functor_to_cat_id : FunctorToCat >-> Functor.
Definition pseudofunctor_of_functor_to_cat `(F : @FunctorToCat H C P HP)
  := @pseudofunctor_of_functor _ C P HP F.
