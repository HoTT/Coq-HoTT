Require Import Category.Core Functor.Core HomFunctor Category.Morphisms Category.Dual Functor.Dual Category.Prod Functor.Prod NaturalTransformation.Core SetCategory.Core Functor.Composition.Core.
Require Import hit.epi types.Universe HSet hit.iso Overture FunextVarieties.

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
          repeat (apply (@path_forall Funext_downward_closed); intro);
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
End full_faithful.

Section fully_faithful_helpers.
  Context `{fs0 : Funext}.
  Variables x y : hSet.
  Variable m : x -> y.

  Lemma isisomorphism_isequiv_set_cat
        `{H' : IsEquiv _ _ m}
  : IsIsomorphism (m : morphism set_cat x y).
  Proof.
    exists (m^-1)%equiv;
    apply (@path_forall Funext_downward_closed); intro;
    destruct H';
    simpl in *;
    eauto.
  Qed.

  Let isequiv_isepi_ismono_helper ua : isepi m -> ismono m -> IsEquiv m
    := @isequiv_isepi_ismono ua fs0 x y m.

  Definition isequiv_isepimorphism_ismonomorphism
        `{Univalence}
        (Hepi : IsEpimorphism (m : morphism set_cat x y))
        (Hmono : IsMonomorphism (m : morphism set_cat x y))
  : @IsEquiv _ _ m
    := @isequiv_isepi_ismono_helper _ Hepi Hmono.

  (** TODO: Figure out why Universe inconsistencies don't respect delta expansion. *)
  (*Definition isequiv_isepimorphism_ismonomorphism'
        `{fs1 : Funext} `{Univalence}
        (Hepi : IsEpimorphism (m : morphism set_cat x y))
        (Hmono : IsMonomorphism (m : morphism set_cat x y))
  : @IsEquiv _ _ m
    := @isequiv_isepi_ismono _ fs0 fs1 x y m Hepi Hmono.*)
End fully_faithful_helpers.

Global Instance isfullyfaithful_isfull_isfaithful
       `{Univalence} `{fs0 : Funext} `{fs1 : Funext} `{fs2 : Funext}
       `{Hfull : @IsFull fs0 C D F}
       `{Hfaithful : @IsFaithful fs1 C D F}
: @IsFullyFaithful fs2 C D F
  := fun x y => @isisomorphism_isequiv_set_cat
                  _ _ _ _
                  (@isequiv_isepimorphism_ismonomorphism
                     _ _ _ _ _
                     (Hfull x y)
                     (Hfaithful x y)).
