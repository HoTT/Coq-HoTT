Require Import Category.Core Functor.Core HomFunctor Category.Morphisms Category.Dual Functor.Dual Category.Prod Functor.Prod NaturalTransformation.Core SetCategory.Core Functor.Composition.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

Section full_faithful.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor C D.

  (** TODO(JasonGross): Come up with a better name and location for this. *)
  Definition induced_hom_natural_transformation
  : NaturalTransformation (hom_functor C) (hom_functor D o (F^op, F)).
  Proof.
    refine (Build_NaturalTransformation
              (hom_functor C)
              (hom_functor D o (F^op, F))
              (fun sd : object (C^op * C) =>
                 morphism_of F (s := _) (d := _))
              _
           ).
    abstract (
        repeat (intros [] || intro);
        simpl in *;
          repeat (apply path_forall; intro);
        unfold compose, Overture.compose;
        simpl;
        rewrite !composition_of;
        reflexivity
      ).
  Defined.

  Class IsFull
    := is_full
       : forall x y : C,
           IsEpimorphism (induced_hom_natural_transformation (x, y)).
  Class IsFaithful
    := is_faithful
       : forall x y : C,
           IsMonomorphism (induced_hom_natural_transformation (x, y)).

  Class IsFullyFaithful
    := is_fully_faithful
       : forall x y : C,
           IsIsomorphism (induced_hom_natural_transformation (x, y)).

  Global Instance isfull_isfullyfaithful `{IsFullyFaithful}
  : IsFull.
  Proof.
    intros ? ?; hnf in * |- .
    typeclasses eauto.
  Qed.

  Global Instance isfaithful_isfullyfaithful `{IsFullyFaithful}
  : IsFaithful.
  Proof.
    intros ? ?; hnf in * |- .
    typeclasses eauto.
  Qed.

  Lemma isfullyfaithful_isfull_isfaithful_helper `{IsFull} `{IsFaithful}
        (H' : forall x y (m : morphism set_cat x y),
                IsEpimorphism m
                -> IsMonomorphism m
                -> IsIsomorphism m)
  : IsFullyFaithful.
  Proof.
    intros ? ?; hnf in * |- .
    apply H'; eauto.
  Qed.

  (** TODO(JasonGross): find or prove a lemma saying epi + mono -> iso *)
  (*Global Instance isfullyfaithful_isfull_isfaithful `{IsFull} `{IsFaithful}
  : IsFullyFaithful.
  Proof.
    apply isfullyfaithful_isfull_isfaithful_helper.
    (* We need epi + mono -> iso here *)
  Qed.*)
  (* Depends on injective + surjective -> isomorphism, and epi = surj, mono = inj *)
End full_faithful.
