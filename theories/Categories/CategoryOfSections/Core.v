(** * Category of sections *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Strict.
Require Import Functor.Identity NaturalTransformation.Identity.
Require Import NaturalTransformation.Paths NaturalTransformation.Composition.Core.
Require Import Functor.Paths.
Require Import Trunc Types.Sigma.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.


Local Open Scope functor_scope.

Section FunctorSectionCategory.
  Context `{Funext}.

  Variables C D : PreCategory.
  Variable R : Functor C D.

  (** There is a category [Sect(R)] of sections of [R]. *)

  (** ** Section of a functor *)
  Record SectionOfFunctor :=
    {
      section_of_functor_morphism :> Functor D C;
      section_of_functor_issect : R o section_of_functor_morphism = 1
    }.

  Local Notation section_of_functor_sigT :=
    { section_of_functor_morphism : Functor D C
    | R o section_of_functor_morphism = 1 }.

  Lemma section_of_functor_sig
  : section_of_functor_sigT <~> SectionOfFunctor.
  Proof.
    issig.
  Defined.

  Local Open Scope natural_transformation_scope.

  (** ** Definition of category of sections of a functor *)
  Definition category_of_sections : PreCategory.
  Proof.
    refine (@Build_PreCategory
              SectionOfFunctor
              (fun F G => NaturalTransformation F G)
              (fun F => 1)
              (fun _ _ _ T U => T o U)
              _
              _
              _
              _);
    abstract (path_natural_transformation; auto with morphism).
  Defined.
End FunctorSectionCategory.

Global Instance isstrict_category_of_sections `{Funext}
      `{IsStrictCategory C, IsStrictCategory D}
      (F : Functor C D)
: IsStrictCategory (category_of_sections F) | 20.
Proof.
  eapply trunc_equiv; [ | apply section_of_functor_sig ].
  typeclasses eauto.
Qed.
