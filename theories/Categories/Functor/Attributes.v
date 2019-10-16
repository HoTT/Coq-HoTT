(** * Attributes of functors (full, faithful, split essentially surjective) *)
Require Import Category.Core Functor.Core HomFunctor Category.Morphisms Category.Dual Functor.Dual Category.Prod Functor.Prod NaturalTransformation.Core SetCategory.Core Functor.Composition.Core.
Require Import Basics.Trunc HIT.epi Types.Universe HSet HIT.iso HoTT.Truncations UnivalenceImpliesFunext TruncType.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

Section full_faithful.
  Context `{Funext}.
  Variables C D : PreCategory.
  Variable F : Functor C D.

  (** ** Natural transformation [hom_C(─, ─) → hom_D(Fᵒᵖ(─), F(─))] *)
  (** TODO(JasonGross): Come up with a better name and location for this. *)
  Definition induced_hom_natural_transformation
  : NaturalTransformation (hom_functor C) (hom_functor D o (F^op, F)).
  Proof.
    refine (Build_NaturalTransformation
              (hom_functor C)
              (hom_functor D o (F^op, F))
              (fun (sd : object (C^op * C)) m => (F _1 m)%morphism)
              _
           ).
    abstract (
        repeat (intros [] || intro);
        simpl in *;
          repeat (apply path_forall; intro);
        simpl;
        rewrite !composition_of;
        reflexivity
      ).
  Defined.

  (** ** Full *)
  Class IsFull
    := is_full
       : forall x y : C,
           IsEpimorphism (induced_hom_natural_transformation (x, y)).
  (** ** Faithful *)
  Class IsFaithful
    := is_faithful
       : forall x y : C,
           IsMonomorphism (induced_hom_natural_transformation (x, y)).

  (** ** Fully Faithful *)
  Class IsFullyFaithful
    := is_fully_faithful
       : forall x y : C,
           IsIsomorphism (induced_hom_natural_transformation (x, y)).

  (** ** Fully Faithful → Full *)
  Global Instance isfull_isfullyfaithful `{IsFullyFaithful}
  : IsFull.
  Proof.
    intros ? ?; hnf in * |- .
    typeclasses eauto.
  Qed.

  (** ** Fully Faithful → Faithful *)
  Global Instance isfaithful_isfullyfaithful `{IsFullyFaithful}
  : IsFaithful.
  Proof.
    intros ? ?; hnf in * |- .
    typeclasses eauto.
  Qed.

  (** ** Full * Faithful → Fully Faithful *)
  (** We start with a helper method, which assumes that epi * mono → iso, and ten prove this assumption *)
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
  Context `{ua : Univalence}.
  Variables x y : hSet.
  Variable m : x -> y.

  Lemma isisomorphism_isequiv_set_cat
        `{H' : IsEquiv _ _ m}
  : IsIsomorphism (m : morphism set_cat x y).
  Proof.
    exists (m^-1)%core;
    apply path_forall; intro;
    destruct H';
    simpl in *;
    eauto.
  Qed.

  Definition isequiv_isepimorphism_ismonomorphism
             (Hepi : IsEpimorphism (m : morphism set_cat x y))
             (Hmono : IsMonomorphism (m : morphism set_cat x y))
  : @IsEquiv _ _ m
    (* NB: This depends on the (arguably accidental) fact that `ismono` and `isepi` from HoTT core are *definitionally* identical to the specialization of `IsMonomorphism` and `IsEpimorphism` to the category of sets. *)
    := @isequiv_isepi_ismono _ x y m Hepi Hmono.
End fully_faithful_helpers.

Global Instance isfullyfaithful_isfull_isfaithful
       `{Univalence}
       `{Hfull : @IsFull _ C D F}
       `{Hfaithful : @IsFaithful _ C D F}
: @IsFullyFaithful _ C D F
  := fun x y => @isisomorphism_isequiv_set_cat
                  _ _ _ _
                  (@isequiv_isepimorphism_ismonomorphism
                     _ _ _ _
                     (Hfull x y)
                     (Hfaithful x y)).

(** ** Split Essentially Surjective *)
(** Quoting the HoTT Book:

    We say a functor [F : A → B] is _split essentially surjective_ if
    for all [b : B] there exists an [a : A] such that [F a ≅ b]. *)

Class IsSplitEssentiallySurjective A B (F : Functor A B)
  := is_split_essentially_surjective
     : forall b : B, exists a : A, F a <~=~> b.

(** ** Essentially Surjective *)
(** Quoting the HoTT Book:

    A functor [F : A → B] is _split essentially surjective_ if for all
    [b : B] there _merely_ exists an [a : A] such that [F a ≅ b]. *)
Class IsEssentiallySurjective A B (F : Functor A B)
  := is_essentially_surjective
     : forall b : B, hexists (fun a : A => F a <~=~> b).

(** ** Weak Equivalence *)
(** Quoting the HoTT Book:

    We say [F] is a _weak equivalence_ if it is fully faithful and
    essentially surjective. *)
Class IsWeakEquivalence `{Funext} A B (F : Functor A B)
  := { is_fully_faithful__is_weak_equivalence :> IsFullyFaithful F;
       is_essentially_surjective__is_weak_equivalence :> IsEssentiallySurjective F }.
