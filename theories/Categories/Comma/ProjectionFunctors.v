(** * Functoriality of the comma category construction with projection functors *)
Require Import Category.Core Functor.Core.
Require Import Category.Prod Functor.Prod.Core.
Require Import Category.Dual Functor.Dual.
Require Import Functor.Composition.Core Functor.Identity.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Functors NatCategory.
Require Import FunctorCategory.Core.
Require Import Cat.Core.
Require Import Functor.Paths.
Require Comma.Core.
Local Set Warnings Append "-notation-overridden". (* work around bug #5567, https://coq.inria.fr/bugs/show_bug.cgi?id=5567, notation-overridden,parsing should not trigger for only printing notations *)
Import Comma.Core.
Local Set Warnings Append "notation-overridden".
Require Import Comma.InducedFunctors Comma.Projection.
Require ProductLaws ExponentialLaws.Law1.Functors ExponentialLaws.Law4.Functors.
Require Import Types.Prod Types.Forall PathGroupoids HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

(** ** Functor from [(A → C)ᵒᵖ × (B → C)] to [cat / (A × B)] *)
(** It sends [S : A → C ← B : T] to the category [(S / T)] and its projection functor to [A × B]. *)
Section comma.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation Cat := (@sub_pre_cat _ P HF).

  Variables A B C : PreCategory.

  Hypothesis PAB : P (A * B).
  Hypothesis P_comma : forall (S : Functor A C) (T : Functor B C),
                         P (S / T).

  Local Open Scope morphism_scope.

  Definition comma_category_projection_functor_object_of
             (ST : object ((A -> C)^op * (B -> C)))
  : Cat / !((A * B; PAB) : Cat).
  Proof.
    exists (Datatypes.fst ST / Datatypes.snd ST; P_comma _ _) (center _).
    exact (comma_category_projection (Datatypes.fst ST) (Datatypes.snd ST)).
  Defined.

  Definition comma_category_projection_functor_morphism_of
             s d (m : morphism ((A -> C)^op * (B -> C)) s d)
  : morphism (Cat / !((A * B; PAB) : Cat))
             (comma_category_projection_functor_object_of s)
             (comma_category_projection_functor_object_of d).
  Proof.
    hnf.
    refine (CommaCategory.Build_morphism
              (comma_category_projection_functor_object_of s)
              (comma_category_projection_functor_object_of d)
              (comma_category_induced_functor m)
              (center _)
              _).
    simpl.
    destruct_head_hnf Datatypes.prod.
    path_functor.
  Defined.

  Local Ltac comma_laws_t :=
    repeat (apply path_forall || intro);
    simpl;
    rewrite !transport_forall_constant;
    transport_path_forall_hammer;
    simpl;
    destruct_head Datatypes.prod;
    simpl in *;
    apply CommaCategory.path_morphism;
    simpl;
    repeat match goal with
             | [ |- context[?f _ _ _ _ _ _ _ (transport ?P ?p ?z)] ]
               => simpl rewrite (@ap_transport
                                   _ P _ _ _ p
                                   (fun _ => f _ _ _ _ _ _ _)
                                   z)
             | [ |- context[transport (fun y => ?f (?fa _ _ _ _ _ y) ?x)] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f y x) (fa _ _ _ _ _))
             | [ |- context[transport (fun y => ?f ?x (?fa _ _ _ _ _ y))] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f x y) (fa _ _ _ _ _))
           end;
    unfold comma_category_induced_functor_object_of_identity;
    unfold comma_category_induced_functor_object_of_compose;
    simpl;
    rewrite ?CommaCategory.ap_a_path_object', ?CommaCategory.ap_b_path_object';
    try reflexivity.

  Lemma comma_category_projection_functor_identity_of x
  : comma_category_projection_functor_morphism_of (Category.Core.identity x)
    = 1.
  Proof.
    apply CommaCategory.path_morphism; simpl; [ | reflexivity ].
    path_functor.
    exists (path_forall _ _ (comma_category_induced_functor_object_of_identity _)).
    comma_laws_t.
  Qed.

  Lemma comma_category_projection_functor_composition_of s d d' m m'
  : comma_category_projection_functor_morphism_of
      (@Category.Core.compose _ s d d' m' m)
    = (comma_category_projection_functor_morphism_of m')
        o (comma_category_projection_functor_morphism_of m).
  Proof.
    apply CommaCategory.path_morphism; simpl; [ | reflexivity ].
    path_functor.
    simpl.
    exists (path_forall _ _ (comma_category_induced_functor_object_of_compose m' m)).
    comma_laws_t.
  Qed.

  Definition comma_category_projection_functor
  : Functor ((A -> C)^op * (B -> C))
            (Cat / !((A * B; PAB) : Cat))
    := Build_Functor ((A -> C)^op * (B -> C))
                     (Cat / !((A * B; PAB) : Cat))
                     comma_category_projection_functor_object_of
                     comma_category_projection_functor_morphism_of
                     comma_category_projection_functor_composition_of
                     comma_category_projection_functor_identity_of.
End comma.

Section slice_category_projection_functor.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation Cat := (@sub_pre_cat _ P HF).

  Variables C D : PreCategory.

  Hypothesis P1C : P (1 * C).
  Hypothesis PC1 : P (C * 1).
  Hypothesis PC : P C.
  Hypothesis P_comma : forall (S : Functor C D) (T : Functor 1 D), P (S / T).
  Hypothesis P_comma' : forall (S : Functor 1 D) (T : Functor C D), P (S / T).

  Local Open Scope functor_scope.
  Local Open Scope category_scope.

  Local Notation inv D := (@ExponentialLaws.Law1.Functors.inverse _ terminal_category _ _ _ D).

  (** ** Functor [(C → D)ᵒᵖ → D → (cat / C)] *)
  Definition slice_category_projection_functor
  : object (((C -> D)^op) -> (D -> (Cat / ((C; PC) : Cat)))).
  Proof.
    refine ((ExponentialLaws.Law4.Functors.inverse _ _ _) _).
    refine (_ o (Functor.Identity.identity (C -> D)^op,
                 inv D)).
    refine (_ o @comma_category_projection_functor _ P HF C 1 D PC1 P_comma).
    refine (cat_over_induced_functor _).
    hnf.
    exact (ProductLaws.Law1.functor _).
  Defined.

  Definition coslice_category_projection_functor
  : object ((C -> D)^op -> (D -> (Cat / ((C; PC) : Cat)))).
  Proof.
    refine ((ExponentialLaws.Law4.Functors.inverse _ _ _) _).
    refine (_ o (Functor.Identity.identity (C -> D)^op,
                 inv D)).
    refine (_ o @comma_category_projection_functor _ P HF C 1 D PC1 P_comma).
    refine (cat_over_induced_functor _).
    hnf.
    exact (ProductLaws.Law1.functor _).
  Defined.

  (** ** Functor [(C → D) → Dᵒᵖ → (cat / C)] *)
  Definition slice_category_projection_functor'
  : object ((C -> D) -> (D^op -> (Cat / ((C; PC) : Cat)))).
  Proof.
    refine ((ExponentialLaws.Law4.Functors.inverse _ _ _) _).
    refine (_ o (Functor.Identity.identity (C -> D),
                 (inv D)^op)).
    refine (_ o ProductLaws.Swap.functor _ _).
    refine (_ o @comma_category_projection_functor _ P HF 1 C D P1C P_comma').
    refine (cat_over_induced_functor _).
    hnf.
    exact (ProductLaws.Law1.functor' _).
  Defined.

  Definition coslice_category_projection_functor'
  : object ((C -> D) -> (D^op -> (Cat / ((C; PC) : Cat)))).
  Proof.
    refine ((ExponentialLaws.Law4.Functors.inverse _ _ _) _).
    refine (_ o (Functor.Identity.identity (C -> D),
                 (inv D)^op)).
    refine (_ o ProductLaws.Swap.functor _ _).
    refine (_ o @comma_category_projection_functor _ P HF 1 C D P1C P_comma').
    refine (cat_over_induced_functor _).
    hnf.
    exact (ProductLaws.Law1.functor' _).
  Defined.
End slice_category_projection_functor.
