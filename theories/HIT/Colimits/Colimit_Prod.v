Require Import HoTT.Basics HoTT.Types.
Require Import Colimits.Diagram Colimits.Colimit Colimits.Colimit_Sigma.

(** * Colimit of product by a constant type *)

(** Given a diagram [D], one of his colimits [Q] and a type [A], one can consider the diagram of the products of the types of [D] and [A]. Then, a colimit of such a diagram is [A * Q]. *)

(** This is the constant case of the file [Colimit_Sigma] and we reuse its results. *)

Section ColimitProd.
  Context `{Funext} {G: graph} (D: diagram G) (A: Type).

  Definition prod_diag : diagram G.
  Proof.
    simple refine (Build_diagram _ _ _).
    - exact (fun i => A * (D i)).
    - simpl; intros i j f x. exact (fst x, D _f f (snd x)).
  Defined.

  Definition diagram_equiv_prod_sigma
    : sigma_diag (fun _ : A => D) ~d~ prod_diag.
  Proof.
    unshelve econstructor.
    - serapply Build_diagram_map; cbn.
      + intro i; apply equiv_sigma_prod0.
      + reflexivity.
    - intro i; cbn.
      apply equiv_sigma_prod0.
  Defined.

  Lemma is_colimit_prod {Q: Type} (HQ: is_colimit D Q)
  : is_colimit prod_diag (A * Q).
  Proof.
    eapply postcompose_equiv_is_colimit.
    - apply equiv_sigma_prod0.
    - eapply precompose_equiv_is_colimit.
      + symmetry; apply diagram_equiv_prod_sigma.
      + by apply is_colimit_sigma.
  Defined.
End ColimitProd.
