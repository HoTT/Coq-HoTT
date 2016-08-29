(** * Dependent Product; oplax limit of a functor to Cat *)
Require Import Category.Core Functor.Core.
Require Import Cat.Core.
Require Grothendieck.ToCat.
Require Import CategoryOfSections.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

Section dependent_product.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable P : PreCategory -> Type.
  (*Context `{forall C, IsHProp (P C)}.*)
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation cat := (@sub_pre_cat _ P HF).

  Variable F : Functor C cat.

  (** Quoting http://mathoverflow.net/questions/137689/explicit-description-of-the-oplax-limit-of-a-functor-to-cat:

      The oplax limit is the category of sections for the functor from
      the Grothendieck construction to the base category.

      The strong limit is the category of cartesian sections
      (every arrow in the base category gets mapped to a cartesian
      one).

      Notice how this goes along very well with the interpretation as
      dependent product and as ∀: The set theoretic product is just
      the set of sections into the disjoint union.

      Given a strong functor [F : X → Cat] we denote the Grothendieck
      construction by [Gr F].

      There is a canonical functor [π : Gr F → X]. Sections of this
      functor are functors [s : X → Gr F] such that [s ∘ π = id]. *)

  Definition dependent_product : PreCategory
    := category_of_sections (Grothendieck.ToCat.pr1 F).
End dependent_product.

Notation Pi := dependent_product.
