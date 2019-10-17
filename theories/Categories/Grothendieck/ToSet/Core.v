(** * Grothendieck Construction of a functor to Set *)
Require Import Category.Core Functor.Core.
Require Import SetCategory.Core.
Require Import Basics.Trunc HSet Types.Sigma TruncType Types.Record.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section Grothendieck.
  Context `{Funext}.

  (**
     Quoting Wikipedia:

     The Grothendieck construction is an auxiliary construction used
     in the mathematical field of category theory.

     Let

<<
     F : C → Set
>>

     be a functor from any small category to the category of sets.
     The Grothendieck construct for [F] is the category [Γ F] whose
     objects are pairs [(c, x)], where [c : C] is an object and [x : F
     c] is an element, and for which the set [Hom (Γ F) (c1, x1) (c2,
     x2)] is the set of morphisms [f : c1 → c2] in [C] such that
     [F₁ f x1 = x2].  *)

  Variable C : PreCategory.
  Variable F : Functor C set_cat.

  Record Pair :=
    {
      c : C;
      x : F c
    }.

  Definition issig_pair : { c : C | F c } <~> Pair.
  Proof.
    issig.
  Defined.

  Local Notation morphism s d :=
    { f : morphism C s.(c) d.(c)
    | F _1 f s.(x) = d.(x) }.

  Definition compose_H s d d'
             (m1 : morphism d d')
             (m2 : morphism s d)
  : (F _1 (m1 .1 o m2 .1)) s.(x) = d'.(x).
  Proof.
    etransitivity; [ | exact (m1.2) ].
    etransitivity; [ | apply ap; exact (m2.2) ].
    match goal with
      | [ |- ?f ?x = ?g (?h ?x) ] => change (f x = (g o h) x)
    end.
    match goal with
      | [ |- ?f ?x = ?g ?x ] => apply (@apD10 _ _ f g)
    end.
    apply (composition_of F).
  Defined.

  Definition compose s d d'
             (m1 : morphism d d')
             (m2 : morphism s d)
  : morphism s d'.
  Proof.
    exists (m1.1 o m2.1).
    apply compose_H.
  Defined.

  Definition identity_H s
    := apD10 (identity_of F s.(c)) s.(x).

  Definition identity s : morphism s s.
  Proof.
    exists 1.
    apply identity_H.
  Defined.

  Global Arguments compose_H : simpl never.
  Global Arguments identity_H : simpl never.
  Global Arguments identity _ / .
  Global Arguments compose _ _ _ _ _ / .

  (** ** Category of elements *)
  Definition category : PreCategory.
  Proof.
    refine (@Build_PreCategory
              Pair
              (fun s d => morphism s d)
              identity
              compose
              _
              _
              _
              _);
    abstract (
        repeat intro;
        apply path_sigma_uncurried; simpl;
        ((exists (associativity _ _ _ _ _ _ _ _))
           || (exists (left_identity _ _ _ _))
           || (exists (right_identity _ _ _ _)));
        exact (center _)
      ).
  Defined.

  (** ** First projection functor *)
  Definition pr1 : Functor category C
    := Build_Functor
         category C
         c
         (fun s d => @pr1 _ _)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).
End Grothendieck.
