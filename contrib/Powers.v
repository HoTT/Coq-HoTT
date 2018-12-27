Require Import Basics.
Require Import Category.Core.
Require Import Functor.Core.
Require Import Functor.Composition.Core.
Require Import Limits.Core.
Require Import Limits.Functors.
Require Import FunctorCategory.Core.
Require Import Adjoint.Core.
Require Import InitialTerminalCategory.Core NatCategory.
Require Import Comma.Core.
Require Import DiscreteCategory.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.


(**
  Power limit and copower colimit in a category
**)

Section powers.

Local Open Scope category_scope.
Local Open Scope functor_scope.

Context {C : PreCategory}.

Context `{Funext}.

Variables I : hSet.

Definition I_cat := discrete_category I.

Context `(has_limits
              : forall (F : Functor I_cat C),
                  @IsLimit _ C I_cat F (limits F)).

Definition PowerFunctor : Functor C C :=
   ExponentialLaws.Law1.Functors.functor _ 
   o limit_functor has_limits 
   o diagonal_functor' C I_cat.

End powers.