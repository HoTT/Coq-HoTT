Require Import Basics.
Require Import Types.
Require Import Diagrams.Diagram.
Require Import Diagrams.Graph.
Require Import Diagrams.Cocone.
Require Import Diagrams.DDiagram.
Require Import Colimits.Colimit.
Require Import UnivalenceImpliesFunext.

Local Open Scope path_scope.

(** * Flattening lemma *)

(** This file provide a proof of the flattening lemma for colimits. This lemma describes the type [sig E'] when [E' : colimit D -> Type] is a type family defined by recusrion on a colimit. *)
(** The flattening lemma in the case of W-types is presented in section 6.12 of the HoTT book. *)
(** A good intuition is given by the pushout's case (see above). *)

Section Flattening.
  (** ** Equifibered diagrams *)

  Context `{Univalence} {G : Graph} (D : Diagram G)
    (E : DDiagram D) `(Equifibered _ _ E).

  Let E_f {i j : G} (g : G i j) (x : D i) : E (i; x) -> E (j; (D _f g) x)
      := @arr _ E (i; x) (j; D _f g x) (g; 1).

  (** Now, given an equifibered diagram and using univalence, one can define a type family [E' : colimit D -> Type] by recusrion on the colimit. *)

  Definition E' : Colimit D -> Type.
  Proof.
    apply Colimit_rec. simple refine (Build_Cocone _ _).
    - exact (fun i x => E (i; x)).
    - intros i j g x; cbn.
      symmetry.
      serapply (path_universe (E_f _ _)).
  Defined.

  (** ** Helper lemmas *)

  Definition transport_E' {i j : G} (g : G i j)  (x : D i) (y : E (i; x))
    : transport E' (colimp i j g x) (E_f g x y) = y.
  Proof.
    refine (transport_idmap_ap _ _ _ _ _ _ @ _).
    srefine (transport2 idmap _ _ @ _).
    2: apply Colimit_rec_beta_colimp; cbn.
    apply (moveR_transport_V idmap).
    symmetry; apply transport_path_universe.
  Defined.

  Definition transport_E'_V {i j : G} (g : G i j)  (x : D i) (y : E (i; x))
    : transport E' (colimp i j g x)^ y = E_f g x y.
  Proof.
    apply moveR_transport_V.
    symmetry.
    apply transport_E'.
  Defined.

  Definition transport_E'_V_E' {i j : G} (g : G i j)  (x : D i) (y : E (i; x))
    : transport_E' g x y
      = ap (transport E' (colimp i j g x)) (transport_E'_V g x y)^
        @ transport_pV E' (colimp i j g x) y.
  Proof.
    rewrite moveR_transport_V_V, inv_V.
    symmetry; apply ap_transport_transport_pV.
  Defined.

  (** ** Main result *)

  (** We define the cocone over the sigma diagram to [sig E']. *)

  Definition cocone_E' : Cocone (diagram_sigma E) (sig E').
  Proof.
    serapply Build_Cocone; cbn.
    - intros i w.
      exists (colim i w.1); cbn.
      exact w.2.
    - intros i j g x; cbn.
      serapply path_sigma'.
      + apply colimp.
      + apply transport_E'.
  Defined.

  (** And we directly prove than it is universal. *)

  Local Opaque path_sigma ap11.

  Global Instance unicocone_cocone_E' : UniversalCocone cocone_E'.
  Proof.
    serapply Build_UniversalCocone.
    intro Z; serapply isequiv_adjointify.
    - intros [q qq]; cbn in *.
      intros [x y]; revert x y.
      serapply Colimit_ind; cbn.
      + intros i x y; exact (q i (x; y)).
      + intros i j g x; cbn.
        funext y.
        refine (transport_arrow_toconst _ _ _ @ _).
        refine (_ @ qq i j g (x; y)).
        cbn; f_ap.
        refine (path_sigma' _ 1 _); cbn.
        apply transport_E'_V.
    - intros [q qq].
      serapply path_cocone.
      + intros i x; reflexivity.
      + intros i j g [x y].
        rewrite concat_1p, concat_p1.
        cbn; rewrite ap_path_sigma.
        cbn; rewrite Colimit_ind_beta_colimp.
        rewrite ap10_path_forall.
        hott_simpl.
        refine (_ @ concat_1p _).
        refine (_ @@ 1).
        match goal with |- ap _ ?X @ _ = _ => set X end.
        assert (transport_E'_V g x y = p^).
        { subst p.
          exact (moveL_transport_V_V E' _ _ _ _)^. }
        rewrite X.
        clearbody p; clear.
        set (E_f g x y) in *.
        destruct p.
        reflexivity.
    - intro f.
      funext [x y].
      revert x y; cbn.
      serapply Colimit_ind; cbn.
      + reflexivity.
      + intros i j g x; cbn.
        funext y.
        rewrite transport_forall; cbn.
        rewrite transport_paths_FlFr.
        match goal with |- (_ @ ?pp) @ _ = _ => set pp end.
        cbn in p.
        assert (p = 1).
        { subst p.
          match goal with |- transportD E' ?C _ _ _ = _ => set (C2:=C) end.
          rewrite (transportD_is_transport _ (fun w => C2 w.1 w.2)).
          subst C2; cbn.
          rewrite transport_paths_FlFr.
          rewrite concat_p1.
          apply moveR_Vp.
          rewrite concat_p1.
          rewrite ap_path_sigma.
          cbn.
          rewrite Colimit_ind_beta_colimp.
          rewrite ap10_path_forall.
          hott_simpl.
          rewrite ap11_is_ap10_ap01.
          cbn.
          rewrite concat_1p.
          rewrite (ap_compose (fun y => (colim j ((D _f g) x); y)) f).
          cbn.
          rewrite (ap_compose (fun x0 : exists x0 : D j, E (j; x0)
            => (colim j (pr1 x0); pr2 x0)) f).
          rewrite <- !ap_pp.
          apply (ap (ap f)).
          match goal with |- _ = (ap ?ff ?pp1 @ ?pp2) @ ?pp3
            => set (p1 := pp1) end.
          assert (p1 = ap (transport E' (colimp i j g x)^)
            (transport_pV E' (colimp i j g x) y)^).
          { subst p1; clear.
            etransitivity.
            1: serapply moveL_transport_V_1.
            etransitivity.
            { serapply inverse2.
              2: serapply transport_VpV. }
            symmetry; apply ap_V. }
          rewrite X; clear X p1.
          rewrite <- ap_compose; cbn.
          rewrite (ap_path_sigma (fun x => E (j; x))
            (fun x y => (colim j x; y))).
          cbn; rewrite !concat_p1, concat_pp_p, ap_V.
          apply moveL_Vp.
          match goal with |- ?pp1 @ _ = ?pp2 @ _
            => set (p1 := pp1); set (p2 := pp2) end; cbn in *.
          assert (p1 = path_sigma' E' 1 (transport_Vp _ _ _)).
          {  subst p1.
            rewrite <- ap_existT.
            rewrite (ap_compose (transport E' (colimp i j g x)^)
              (fun v => (colim j ((D _f g) x); v))).
            f_ap; set (colimp i j g x).
            clear; symmetry.
            apply transport_VpV. }
          rewrite X; clear p1 X.
          assert (p2 = path_sigma' E' 1 (transport_E'_V _ _ _))
            by reflexivity.
          rewrite X; clear p2 X.
          rewrite <- !path_sigma_pp_pp'; f_ap.
          rewrite concat_p1, concat_pp_p.
          refine (1 @@ _).
          apply moveL_Mp.
          rewrite <- ap_V, <- ap_pp.
          srefine (_ @ _).
          - refine (ap (transport E' (colimp i j g x)) _).
            refine ((transport_E'_V _ _ _)^ @ _).
            refine (ap _ (transport_pV _ _ _)).
          - f_ap.
            refine (1 @@ _).
            apply transport_VpV.
          - set (transport E' (colimp i j g x)
              (transport E' (colimp i j g x)^ y)).
            rewrite ap_pp, <- ap_compose.
            refine (_ @ (transport_E'_V_E' _ _ _)^).
            refine (1 @@ _).
            subst e.
            refine (_ @ (transport_pVp _ _ _)^).
            rewrite ap_compose.
            f_ap; symmetry.
            apply transport_VpV. }
        rewrite X; hott_simpl.
  Defined.

  (** The flattening lemma follows by colimit unicity. *)

  Definition flattening_lemma : Colimit (diagram_sigma E) <~> sig E'.
  Proof.
    serapply colimit_unicity.
    3: apply iscolimit_colimit.
    erapply Build_IsColimit.
    apply unicocone_cocone_E'.
  Defined.

End Flattening.
