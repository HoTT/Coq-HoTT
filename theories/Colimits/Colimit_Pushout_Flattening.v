Require Import Basics.
Require Import Types.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.
Require Import Diagrams.DDiagram.
Require Import Diagrams.Span.
Require Import Diagrams.Cocone.
Require Import Colimits.Colimit.
Require Import Colimits.Colimit_Pushout.
Require Import Colimits.Colimit_Flattening.

(** * Pushout case *)

(** We show the flattening lemma in the case of the pushout. *)

Section POCase.
  Context `{Univalence} {A B C} {f: A -> B} {g: A -> C}.

  Context (A0 : A -> Type) (B0 : B -> Type) (C0 : C -> Type)
          (f0 : forall x, A0 x <~> B0 (f x)) (g0 : forall x, A0 x <~> C0 (g x)).

  Definition POCase_P : PO f g -> Type.
  Proof.
    simple refine (PO_rec Type B0 C0 _).
    cbn; intro x. eapply path_universe_uncurried.
    etransitivity.
    - symmetry. apply f0.
    - apply g0.
  Defined.

  Definition POCase_E : DDiagram (span f g).
  Proof.
    simple refine (Build_Diagram _ _ _); cbn.
    - intros [[] x]; revert x. 
      + exact A0.
      + destruct b; assumption.
    - intros [[[]|[]] x] [[[]|[]] y]; cbn; intros [[] p].
      + exact (fun y => p # (f0 x y)).
      + exact (fun y => p # (g0 x y)).
  Defined.

  Global Instance POCase_HE : Equifibered POCase_E.
  Proof.
    apply Build_Equifibered.
    intros [[]|[]] [[]|[]] [] x; compute.
    - exact (equiv_isequiv (f0 x)).
    - exact (equiv_isequiv (g0 x)).
  Defined.

  Definition PO_flattening
    : PO (functor_sigma f f0) (functor_sigma g g0) <~> exists x, POCase_P x.
  Proof.
    assert (PO (functor_sigma f f0) (functor_sigma g g0)
            = Colimit (diagram_sigma POCase_E)). {
      unfold PO; apply ap.
      serapply path_diagram; cbn.
      - intros [|[]]; cbn. all: reflexivity.
      - intros [[]|[]] [[]|[]] [] x; cbn in *.
        all: reflexivity. }
    rewrite X; clear X.
    transitivity (exists x, E' (span f g) POCase_E POCase_HE x).
    - apply flattening_lemma.
    - apply equiv_functor_sigma_id.
      intro x.
      assert (E' (span f g) POCase_E POCase_HE x = POCase_P x). {
        unfold E', POCase_P, PO_rec.
        f_ap. serapply path_cocone.
        - intros [[]|[]] y; cbn.
          1: apply path_universe_uncurried; apply g0.
          all: reflexivity.
        - intros [[]|[]] [[]|[]] []; cbn.
          + intro y; simpl; hott_simpl.
            unfold path_universe.
            rewrite <- path_universe_V_uncurried.
            refine (path_universe_compose (f0 y)^-1 (g0 y))^. 
          + intros; apply concat_Vp. }
      rewrite X. reflexivity.
  Defined.

End POCase.
