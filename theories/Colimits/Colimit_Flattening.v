Require Import Basics.
Require Import Types.
Require Import Diagrams.Diagram.
Require Import Diagrams.Graph.
Require Import Diagrams.Cocone.
Require Import Diagrams.DDiagram.
Require Import Colimits.Colimit.

Local Open Scope path_scope.

(** * Flattening lemma *)

(** This file provides a proof of the flattening lemma for colimits. This lemma describes the type [sig E'] when [E' : colimit D -> Type] is a type family defined by recursion on a colimit. The flattening lemma in the case of coequalizers is presented in section 6.12 of the HoTT book and is in Colimits/Coeq.v. *)
(** TODO: See whether there's a straightforward way to deduce the flattening lemma for general colimits from the version for coequalizers. *)

Section Flattening.
  (** ** Equifibered diagrams *)

  Context `{Univalence} {G : Graph} (D : Diagram G)
    (E : DDiagram D) `(Equifibered _ _ E).

  Let E_f {i j : G} (g : G i j) (x : D i) : E (i; x) -> E (j; (D _f g) x)
      := @arr _ E (i; x) (j; D _f g x) (g; 1).

  (** Now, given an equifibered diagram and using univalence, one can define a type family [E' : colimit D -> Type] by recursion on the colimit. *)

  Definition E' : Colimit D -> Type.
  Proof.
    apply Colimit_rec. simple refine (Build_Cocone _ _).
    - exact (fun i x => E (i; x)).
    - intros i j g x; cbn.
      symmetry.
      srapply (path_universe (E_f _ _)).
  Defined.

  (** ** Helper lemmas *)

  Definition transport_E' {i j : G} (g : G i j)  (x : D i) (y : E (i; x))
    : transport E' (colimp i j g x) (E_f g x y) = y.
  Proof.
    refine (transport_idmap_ap _ _ _ @ _).
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
    srapply Build_Cocone; cbn.
    - intros i w.
      exists (colim i w.1); cbn.
      exact w.2.
    - intros i j g x; cbn.
      srapply path_sigma'.
      + apply colimp.
      + apply transport_E'.
  Defined.

  (** And we directly prove that it is universal.  We break the proof into parts to slightly speed it up. *)

  Local Opaque path_sigma ap11.

  Local Definition cocone_extends Z: Cocone (diagram_sigma E) Z -> ((sig E') -> Z).
  Proof.
    intros [q qq]; cbn in *.
    intros [x y]; revert x y.
    srapply Colimit_ind; cbn.
    + intros i x y; exact (q i (x; y)).
    + intros i j g x; cbn.
      funext y.
      refine (transport_arrow_toconst _ _ _ @ _).
      refine (_ @ qq i j g (x; y)).
      cbn; f_ap.
      refine (path_sigma' _ 1 _); cbn.
      apply transport_E'_V.
  Defined.

  Local Definition cocone_isretr Z
    : cocone_postcompose cocone_E' o cocone_extends Z == idmap.
  Proof.
    intros [q qq].
    srapply path_cocone.
    + intros i x; reflexivity.
    + intros i j g [x y].
      rewrite concat_1p, concat_p1.
      cbn; rewrite ap_path_sigma.
      simpl.
      rewrite Colimit_ind_beta_colimp.
      rewrite ap10_path_forall.
      rewrite concat_pp_p, concat_V_pp.
      refine (_ @ concat_1p _).
      refine (concat_p_pp _ _ _ @ _).
      refine (_ @@ 1).
      match goal with |- ap _ ?X @ _ = _ => set (p := X) end.
      assert (r : transport_E'_V g x y = p^).
      { subst p.
        exact (moveL_transport_V_V E' _ _ _ _)^. }
      rewrite r; clear r.
      destruct p.
      reflexivity.
  Defined. (* 0.1s *)

  Local Definition cocone_issect Z
    : cocone_extends Z o cocone_postcompose cocone_E' == idmap.
  Proof.
    intro f.
    funext [x y].
    revert x y.
    srapply Colimit_ind.
    + cbn; reflexivity.
    + intros i j g x; cbn.
      funext y.
      set (L := cocone_extends Z (cocone_postcompose cocone_E' f)).
      refine (transport_forall _ _ _ @ _).
      nrapply (transport_paths_FlFr' (f:=fun y0 => L (_; y0))).
      lhs nrapply concat_p1.
      lhs_V nrapply concat_1p.
      refine (_^ @@ 1).
      lhs rapply (transportD_is_transport E' (fun w => L w = f w)).
      nrapply transport_paths_FlFr'; apply equiv_p1_1q.
      rewrite ap_path_sigma.
      rewrite Colimit_ind_beta_colimp.
      rewrite ap10_path_forall.
      simpl.
      clear L.
      rewrite concat_pp_p, concat_V_pp.
      rewrite ap11_is_ap10_ap01.
      cbn.
      rewrite concat_1p.
      rewrite (ap_compose (fun y => (colim j ((D _f g) x); y)) f).
      rewrite (ap_compose (fun x0 : exists x0 : D j, E (j; x0)
        => (colim j (pr1 x0); pr2 x0)) f).
      rewrite <- ! (ap_pp f).
      apply (ap (ap f)).
      symmetry.
      refine (_ @ concat_pp_p _ _ _).
      match goal with |- _ = (ap ?ff ?pp1 @ ?pp2) @ ?pp3
        => set (p1 := pp1) end.
      assert (p1eq : p1 = ap (transport E' (colimp i j g x)^)
        (transport_pV E' (colimp i j g x) y)^).
      { subst p1; clear.
        etransitivity.
        1: srapply moveL_transport_V_1.
        etransitivity.
        1: nrapply inverse2; snrapply transport_VpV.
        symmetry; apply ap_V. }
      rewrite p1eq; clear p1eq p1.
      rewrite <- ap_compose; cbn.
      rewrite (ap_path_sigma (fun x => E (j; x))
        (fun x y => (colim j x; y))).
      cbn; rewrite !concat_p1, concat_pp_p, ap_V.
      apply moveL_Vp.
      match goal with |- ?pp1 @ _ = ?pp2 @ _
        => set (p1 := pp1);
          change pp2 with (path_sigma' E' 1
                            (transport_E'_V g x
                               (transport E' (colimp i j g x) (transport E' (colimp i j g x)^ y)))) end.
      assert (p1eq : p1 = path_sigma' E' 1 (transport_Vp _ _ _)).
      { subst p1.
        rewrite <- ap_exist.
        rewrite (ap_compose (transport E' (colimp i j g x)^)
          (fun v => (colim j ((D _f g) x); v))).
        f_ap; set (p := colimp i j g x).
        clear; symmetry.
        apply transport_VpV. }
      rewrite p1eq; clear p1eq p1.
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
      - set (e := transport E' (colimp i j g x)
          (transport E' (colimp i j g x)^ y)).
        rewrite ap_pp, <- ap_compose.
        refine (_ @ (transport_E'_V_E' _ _ _)^).
        refine (1 @@ _).
        subst e.
        refine (_ @ (transport_pVp _ _ _)^).
        rewrite ap_compose.
        f_ap; symmetry.
        apply transport_VpV.
  Defined. (* TODO: a little slow, 0.40s *)

  Global Instance unicocone_cocone_E' : UniversalCocone cocone_E'.
  Proof.
    srapply Build_UniversalCocone.
    intro Z; srapply isequiv_adjointify.
    - exact (cocone_extends Z).
    - exact (cocone_isretr Z).
    - exact (cocone_issect Z).
  Defined.

  (** The flattening lemma follows by colimit unicity. *)

  Definition flattening_lemma : Colimit (diagram_sigma E) <~> sig E'.
  Proof.
    srapply colimit_unicity.
    3: apply iscolimit_colimit.
    rapply Build_IsColimit.
    apply unicocone_cocone_E'.
  Defined.

End Flattening.
(* TODO: ending the section is a bit slow (0.2s).  But simply removing the Section (and changing "Let" to "Local Definition") causes the whole file to be much slower.  It should be possible to remove the section without making the whole file slower. *)
