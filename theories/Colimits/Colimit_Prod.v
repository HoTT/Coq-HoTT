Require Import Basics.
Require Import Types.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.
Require Import Colimits.Colimit.
Require Import Colimits.Colimit_Sigma.
Require Import Diagrams.Graph.

(** * Colimit of product by a constant type *)

(** Given a diagram [D], one of his colimits [Q] and a type [A], one can consider the diagram of the products of the types of [D] and [A]. Then, a colimit of such a diagram is [A * Q]. *)

(** This is the constant case of the file [Colimit_Sigma] and we reuse its results. *)

Section ColimitProd.

  Context `{Funext} {G : Graph} (D : Diagram G) (A : Type).

  Definition prod_diagram : Diagram G.
  Proof.
    serapply Build_Diagram.
    - exact (fun i => A * (D i)).
    - simpl; intros i j f x.
      exact (fst x, D _f f (snd x)).
  Defined.

  Definition diagram_equiv_prod_sigma
    : sigma_diagram (fun _ : A => D) ~d~ prod_diagram.
  Proof.
    unshelve econstructor.
    - serapply Build_DiagramMap; cbn.
      + intro i; apply equiv_sigma_prod0.
      + reflexivity.
    - intro i; cbn.
      apply equiv_sigma_prod0.
  Defined.

  Lemma iscolimit_prod {Q : Type} (HQ : IsColimit D Q)
  : IsColimit prod_diagram (A * Q).
  Proof.
    eapply iscolimit_postcompose_equiv.
    - apply equiv_sigma_prod0.
    - eapply iscolimit_precompose_equiv.
      + symmetry; apply diagram_equiv_prod_sigma.
      + by apply iscolimit_sigma.
  Defined.

End ColimitProd.
