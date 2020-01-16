(** * ∑-categories on objects - a generalization of subcategories *)
Require Import HoTT.Basics HoTT.Types.
Require Import Category.Core Functor.Core Category.Sigma.Core.
Require Functor.Composition.Core Functor.Identity.
Require Import Functor.Paths.
Import Functor.Identity.FunctorIdentityNotations.
Import Functor.Composition.Core.FunctorCompositionCoreNotations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Notation sigT_type := Coq.Init.Specif.sigT.
Local Notation pr1_type := Overture.pr1.

Local Open Scope morphism_scope.
Local Open Scope functor_scope.

Section sigT_obj.
  Variable A : PreCategory.
  Variable Pobj : A -> Type.

  (** ** Definition of [sigT_obj]-precategory *)
  Definition sigT_obj : PreCategory
    := @Build_PreCategory
         (sigT_type Pobj)
         (fun s d => morphism A (pr1_type s) (pr1_type d))
         (fun x => @identity A (pr1_type x))
         (fun s d d' m1 m2 => m1 o m2)%morphism
         (fun _ _ _ _ => associativity A _ _ _ _)
         (fun _ _ => left_identity A _ _)
         (fun _ _ => right_identity A _ _)
         _.

  (** ** First projection functor *)
  Definition pr1_obj : Functor sigT_obj A
    := Build_Functor
         sigT_obj A
         (@pr1_type _ _)
         (fun s d m => m)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Definition sigT_obj_as_sigT : PreCategory
    := @sig A Pobj (fun _ _ _ => Unit) _ (fun _ => tt) (fun _ _ _ _ _ _ _ => tt).

  Definition sigT_functor_obj : Functor sigT_obj_as_sigT sigT_obj
    := Build_Functor sigT_obj_as_sigT sigT_obj
                     (fun x => x)
                     (fun _ _ => @pr1_type _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Definition sigT_functor_obj_inv : Functor sigT_obj sigT_obj_as_sigT
    := Build_Functor sigT_obj sigT_obj_as_sigT
                     (fun x => x)
                     (fun _ _ m => existT _ m tt)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Local Open Scope functor_scope.

  Lemma sigT_obj_eq `{Funext}
  : sigT_functor_obj o sigT_functor_obj_inv = 1
    /\ sigT_functor_obj_inv o sigT_functor_obj = 1.
  Proof.
    split; path_functor; trivial.
    apply path_forall; intros [].
    apply path_forall; intros [].
    apply path_forall; intros [? []].
    reflexivity.
  Qed.

  Definition sigT_obj_compat : pr1_obj o sigT_functor_obj = pr1
    := idpath.
End sigT_obj.

Arguments pr1_obj {A Pobj}.

Module Export CategorySigmaOnObjectsNotations.
  Notation "{ x : A | P }" := (sigT_obj A (fun x => P)) : category_scope.
End CategorySigmaOnObjectsNotations.
