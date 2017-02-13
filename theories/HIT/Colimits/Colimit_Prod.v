Require Import HoTT.Basics HoTT.Types.
Require Import Colimits.Diagram Colimits.Colimit Colimits.Colimit_Sigma.

Section ColimitProd.
  Context `{Funext} {G: graph} (D: diagram G) (A: Type).

  Definition prod_diag : diagram G.
  Proof.
    simple refine (Build_diagram _ _ _).
    exact (fun i => A * (D i)).
    simpl; intros i j f x. exact (fst x, D _f f (snd x)).
  Defined.

  Definition diagram_map_prod_sigma
    : diagram_map (sigma_diag (fun _ : A => D)) prod_diag.
  Proof.
    simple refine (Build_diagram_map _ _).
    exact (fun i x => (x.1, x.2)).
    reflexivity.
  Defined.
 
  Lemma is_colimit_prod {Q: Type} (HQ: is_colimit D Q)
  : is_colimit prod_diag (A * Q).
  Proof.
    simple refine (postcompose_equiv_is_colimit (Q := sig (fun _ : A => Q)) _ _).
    apply equiv_sigma_prod0.
    simple refine (precompose_equiv_is_colimit
                     (D2 := sigma_diag (fun _ : A => D)) _ _). {
      simple refine (Build_diagram_equiv _ _).
      - simple refine (Build_diagram_map _ _).
        intros i. apply equiv_sigma_prod0.
        reflexivity.
      - intros i. simpl.
        simple refine (isequiv_inverse (equiv_sigma_prod0 A (D i))). }
    simple refine (is_colimit_sigma _ _). intros y; exact HQ.
  Defined.
End ColimitProd.