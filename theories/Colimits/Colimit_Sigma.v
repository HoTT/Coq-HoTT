Require Import Basics.
Require Import Types.
Require Import Diagrams.Diagram.
Require Import Diagrams.Graph.
Require Import Diagrams.Cocone.
Require Import Colimits.Colimit.

(** * Colimit of the dependent sum of a family of diagrams *)

(** Given a family diagram [D(y)], and a colimit [Q(y)] of each diagram, one can consider the diagram of the sigmas of the types of the [D(y)]s. Then, a colimit of such a diagram is the sigma of the [Q(y)]s. *)

Section ColimitSigma.

  Context `{Funext} {G : Graph} {Y : Type} (D : Y -> Diagram G).

  (** The diagram of the sigmas. *)

  Definition sigma_diagram : Diagram G.
  Proof.
    serapply Build_Diagram.
    - exact (fun i => {y: Y & D y i}).
    - simpl; intros i j g x.
      exact (x.1; D x.1 _f g x.2).
  Defined.

  (** The embedding, for a particular [y], of [D(y)] in the sigma diagram. *)

  Definition sigma_diagram_map (y: Y) : DiagramMap (D y) sigma_diagram.
  Proof.
    serapply Build_DiagramMap.
    { intros i x.
      exists y.
      exact x. }
    reflexivity.
  Defined.

  Context {Q : Y -> Type}.

  (** The sigma of a family of cocones. *)

  Definition sigma_cocone (C : forall y, Cocone (D y) (Q y))
    : Cocone sigma_diagram (sig Q).
  Proof.
    serapply Build_Cocone; simpl; intros i x.
    1: exact (x.1; legs (C x.1) i x.2).
    simpl; intros g x'.
    serapply path_sigma'.
    1: reflexivity.
    apply legs_comm.
  Defined.

  (** The main result: [sig Q] is a colimit of the diagram of sigma types. *)

  Lemma iscolimit_sigma (HQ : forall y, IsColimit (D y) (Q y))
  : IsColimit sigma_diagram (sig Q).
  Proof.
    pose (SigmaC := sigma_cocone (fun y => HQ y)).
    serapply (Build_IsColimit SigmaC).
    serapply Build_UniversalCocone.
    intros X; serapply isequiv_adjointify.
    - intros CX x.
      serapply (cocone_postcompose_inv (HQ x.1) _ x.2).
      serapply (cocone_precompose _ CX).
      apply sigma_diagram_map.
    - intro CX.
      pose (CXy := fun y => cocone_precompose (sigma_diagram_map y) CX).
      change (cocone_postcompose SigmaC
        (fun x => cocone_postcompose_inv (HQ x.1) (CXy x.1) x.2) = CX).
      serapply path_cocone; simpl.
      + intros i x.
        change (legs (cocone_postcompose (HQ x.1)
                 (cocone_postcompose_inv (HQ x.1) (CXy x.1))) i x.2 = CX i x).
        exact (ap10 (apD10 (ap legs (eisretr
          (cocone_postcompose (HQ x.1)) (CXy _))) i) x.2).
      + intros i j g [y x]; simpl.
        set (py := (eisretr (cocone_postcompose (HQ y)) (CXy y))).
        set (py1 := ap legs py).
        specialize (apD legs_comm py); intro py2.
          simpl in *.
          rewrite (path_forall _ _(transport_forall_constant _ _)) in py2.
          apply apD10 in py2; specialize (py2 i); simpl in py2.
          rewrite (path_forall _ _(transport_forall_constant _ _)) in py2.
          apply apD10 in py2; specialize (py2 j); simpl in py2.
          rewrite (path_forall _ _(transport_forall_constant _ _)) in py2.
          apply apD10 in py2; specialize (py2 g); simpl in py2.
          rewrite (path_forall _ _(transport_forall_constant _ _)) in py2.
          apply apD10 in py2; specialize (py2 x); simpl in py2.
          rewrite transport_paths_FlFr in py2.
          rewrite concat_1p, concat_pp_p in py2.
          apply moveL_Mp in py2.
        rewrite (ap_path_sigma_1p
          (fun x01 x02 => cocone_postcompose_inv (HQ x01) (CXy x01) x02)).
        (* Set Printing Coercions. (* to understand what happens *)   *)
        subst py1.
        etransitivity.
        * etransitivity.
          2:exact py2.
          apply ap.
          rewrite (ap_compose legs (fun x0 => x0 i x)).
          rewrite (ap_apply_lD2 _ i x).
          reflexivity.
        * apply ap10, ap.
          rewrite (ap_compose legs (fun x0 => x0 j _)).
          rewrite (ap_apply_lD2 _ j _).
          reflexivity.
    - intros f.
      apply path_forall; intros [y x]; simpl.
      rewrite <- cocone_precompose_postcompose.
      serapply (apD10 (g := fun x => f (y; x)) _ x).
      serapply equiv_moveR_equiv_V.
      serapply path_cocone.
      1: reflexivity.
      intros i j g x'; simpl.
      hott_simpl.
      exact (ap_compose _ _ _)^.
  Defined.

End ColimitSigma.

(** ** Sigma diagrams and diagram maps / equivalences *)

Section SigmaDiagram.

  Context {G : Graph} {Y : Type} (D1 D2 : Y -> Diagram G).

  Definition sigma_diagram_functor (m : forall y, DiagramMap (D1 y) (D2 y))
  : DiagramMap (sigma_diagram D1) (sigma_diagram D2).
  Proof.
    serapply Build_DiagramMap.
    - intros i.
      serapply (functor_sigma idmap _).
      intros y; apply m.
    - intros i j g x; simpl in *.
    serapply path_sigma'.
    1: reflexivity.
    simpl.
    apply (DiagramMap_comm (m x.1)).
  Defined.

  Definition sigma_diag_functor_equiv (m : forall y, (D1 y) ~d~ (D2 y))
    : (sigma_diagram D1) ~d~ (sigma_diagram D2).
  Proof.
    serapply (Build_diagram_equiv (sigma_diagram_functor m)).
    intros i.
    serapply isequiv_functor_sigma.
    intros y; apply m.
  Defined.

End SigmaDiagram.
