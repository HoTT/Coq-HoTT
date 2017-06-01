(** * Dependent Product Category *)
Require Import Category.Core Category.Strict.
Require Import Types.Forall.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

(** ** Definition of [∀], or [∏], for categories *)
Section pi.
  Context `{Funext}.
  Variable A : Type.
  Variable P : A -> PreCategory.

  Definition pi : PreCategory.
    refine (@Build_PreCategory
              (forall a : A, P a)
              (fun s d => forall a : A, morphism (P a) (s a) (d a))
              (fun x => fun a => identity (x a))
              (fun s d d' m2 m1 => fun a => m2 a o m1 a)
              _
              _
              _
              _);
    abstract (
        repeat (intro || apply path_forall);
        auto with morphism
      ).
  Defined.
End pi.

Local Notation "'forall'  x .. y , P" := (forall x, .. (forall y, P) ..) : type_scope.
Local Notation "'forall'  x .. y , P" := (pi (fun x => .. (pi (fun y => P)) .. )) : category_scope.

(** ** The product of strict categories is strict *)
Global Instance isstrict_category_pi
       `{Funext}
       `{forall a : A, IsStrictCategory (P a)}
: IsStrictCategory (forall a, P a).
Proof.
  typeclasses eauto.
Qed.

Local Set Warnings Append "-notation-overridden".
Module Export CategoryPiNotations.
  Notation "'forall'  x .. y , P" := (forall x, .. (forall y, P) ..)%type : type_scope.
  Notation "'forall'  x .. y , P" := (pi (fun x => .. (pi (fun y => P)) .. )) : category_scope.
End CategoryPiNotations.
