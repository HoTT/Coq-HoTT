Require Import Basics.Overture.
Require Import Category.Core.
Require Import Category.Univalent.
Require Import Category.Morphisms.

Require Import Functor.Core.
Require Import Functor.Attributes.
Require Import Yoneda.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope category_scope.
Local Open Scope functor_scope.

Module Export RezkCompletion.

  Private Inductive Rezk (A : PreCategory) : Type :=
    | i : object A -> Rezk A.

  Arguments i {A} a.

  Axiom j 
    : forall {A : PreCategory} (a b : A) 
    (e : morphism A a b) (H : IsIsomorphism e), i a = i b.

  Arguments j {A a b} e {H}.

  Axiom j_id 
    : forall {A : PreCategory} (a : A), 
    j (identity a) = idpath (i a).

  Axiom j_concat 
    : forall {A : PreCategory} (a b c : A) 
    (f : a <~=~> b) (g : b <~=~> c),
    j (g o f) = j f @ j g.

  Axiom Rezk_trunc 
    : forall {A : PreCategory}, 
    IsTrunc 1 (Rezk A).

  Axiom Rezk_ind : forall {A} (P : Rezk A -> Type)
     (i' : forall (a : A), P (i a)), Type.

End RezkCompletion.

Section Rezk.
  Context `{Univalence}.
  Context `{Funext}.

  Definition RezkCompletion (A : PreCategory) : PreCategory.
  Proof.
    serapply (@Build_PreCategory (Rezk A)).
  Admitted.

  Lemma Rezk_IsCategory {A : PreCategory} 
    : IsCategory (RezkCompletion A).
  Proof.
  Admitted.

  Theorem Rezk_weak (A : PreCategory) 
    : exists (I : Functor A (RezkCompletion A)), IsWeakEquivalence I.
  Proof.
  Admitted.

End Rezk.