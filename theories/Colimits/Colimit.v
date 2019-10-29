Require Import Basics.
Require Import Types.
Require Import Diagrams.Diagram.
Require Import Diagrams.Graph.
Require Import Diagrams.Cocone.
Require Import Diagrams.ConstantDiagram.

Local Open Scope path_scope.
Generalizable All Variables.

(** This file contains the definition of colimits, and functoriality results on colimits. *)

(** * Colimits *)

(** A colimit is the extremity of a cocone. *)

Class IsColimit `(D: Diagram G) (Q: Type) := {
  iscolimit_cocone :> Cocone D Q;
  iscolimit_unicocone : UniversalCocone iscolimit_cocone;
}.

Coercion iscolimit_cocone : IsColimit >-> Cocone.

Arguments Build_IsColimit {G D Q} C H : rename.
Arguments iscolimit_cocone {G D Q} C : rename.
Arguments iscolimit_unicocone {G D Q} H : rename.

(** [cocone_postcompose_inv] is defined for convenience: it is only the inverse of [cocone_postcompose]. It allows to recover the map [h] from a cocone [C']. *)

Definition cocone_postcompose_inv `{D: Diagram G} {Q X}
  (H : IsColimit D Q) (C' : Cocone D X) : Q -> X
  := @equiv_inv _ _ _ (iscolimit_unicocone H X) C'.

(** * Existence of colimits *)

(** Whatever the diagram considered, there exists a colimit of it. The existence is given by the HIT [colimit]. *)

(** ** Definition of the HIT *)

Module Export Colimit.

  Private Inductive Colimit {G : Graph} (D : Diagram G) : Type :=
    | colim : forall i, D i -> Colimit D.

  Arguments colim {G D} i x.

  Axiom colimp : forall {G : Graph} {D : Diagram G} i j (f : G i j) (x : D i),
      colim j (D _f f x) = colim i x.

  Definition Colimit_ind {G : Graph} {D : Diagram G} (P : Colimit D -> Type)
    (q : forall i x, P (colim i x))
    (pp_q : forall (i j: G) (g: G i j) (x: D i),
      (@colimp G D i j g x) # (q j (D _f g x)) = q i x)
    : forall w, P w
    := fun w => match w with colim i a => fun _ => q _ a end pp_q.

  Axiom Colimit_ind_beta_colimp : forall {G : Graph} {D : Diagram G}
    (P : Colimit D -> Type) (q : forall i x, P (colim i x))
    (pp_q : forall (i j: G) (g: G i j) (x: D i),
      @colimp G D i j g x # q _ (D _f g x) = q _ x)
    (i j : G) (g : G i j) (x : D i),
    apD (Colimit_ind P q pp_q) (colimp i j g x) = pp_q i j g x.

  Definition Colimit_rec {G : Graph} {D : Diagram G} (P : Type) (C : Cocone D P)
    : Colimit D -> P.
  Proof.
    serapply (Colimit_ind _ C).
    intros i j g x.
    refine (transport_const _ _ @ _).
    apply legs_comm.
  Defined.

  Definition Colimit_rec_beta_colimp {G : Graph} {D : Diagram G}
    (P : Type) (C : Cocone D P) (i j : G) (g: G i j) (x: D i)
    : ap (Colimit_rec P C) (colimp i j g x) = legs_comm C i j g x.
  Proof.
    unfold Colimit_rec, Colimit_ind.
    eapply (cancelL (transport_const (colimp i j g x) _)).
    serapply ((apD_const (Colimit_ind (fun _ => P) C _) (colimp i j g x))^ @ _).
    serapply (Colimit_ind_beta_colimp (fun _ => P) C _ i j g x).
  Defined.

End Colimit.

(** Colimit_rec is an equivalence *)

Global Instance isequiv_colimit_rec `{Funext} {G : Graph}
  {D : Diagram G} (P : Type) : IsEquiv (Colimit_rec (D:=D) P).
Proof.
  serapply isequiv_adjointify.
  { intro f.
    serapply Build_Cocone.
    1: intros i g; apply f, (colim i g).
    intros i j g x.
    apply ap, colimp. }
  { intro.
    apply path_forall.
    serapply Colimit_ind.
    1: reflexivity.
    intros ????; cbn.
    rewrite transport_paths_FlFr.
    rewrite Colimit_rec_beta_colimp.
    hott_simpl. }
  { intros [].
    serapply path_cocone.
    1: reflexivity.
    intros ????; cbn.
    rewrite Colimit_rec_beta_colimp.
    hott_simpl. }
Defined.

Definition equiv_colimit_rec `{Funext} {G : Graph} {D : Diagram G} (P : Type)
  : Cocone D P <~> (Colimit D -> P) := BuildEquiv _ _ _ (isequiv_colimit_rec P).

(** And we can now show that the HIT is actually a colimit. *)

Definition cocone_colimit {G : Graph} (D : Diagram G) : Cocone D (Colimit D)
  := Build_Cocone colim colimp.

Global Instance unicocone_colimit `{Funext} {G : Graph} (D : Diagram G)
  : UniversalCocone (cocone_colimit D).
Proof.
  serapply Build_UniversalCocone; intro Y.
  serapply (isequiv_adjointify _ (Colimit_rec Y) _ _).
  - intros C.
    serapply path_cocone.
    1: reflexivity.
    intros i j f x; simpl.
    refine (concat_p1 _ @ _ @ (concat_1p _)^).
    apply Colimit_rec_beta_colimp.
  - intro f.
    apply path_forall.
    serapply Colimit_ind.
    1: reflexivity.
    intros i j g x; simpl.
    rewrite transport_paths_FlFr.
    rewrite Colimit_rec_beta_colimp.
    refine (ap (fun x => concat x _) (concat_p1 _) @ _).
    apply concat_Vp.
Defined.

Global Instance iscolimit_colimit `{Funext} {G : Graph} (D : Diagram G)
  : IsColimit D (Colimit D) := Build_IsColimit _ (unicocone_colimit D).

(** * Functoriality of colimits *)

Section FunctorialityColimit.

  Context `{Funext} {G : Graph}.

  (** Colimits are preserved by composition with a (diagram) equivalence. *)

  Definition iscolimit_precompose_equiv {D1 D2 : Diagram G}
    (m : D1 ~d~ D2) {Q : Type}
    : IsColimit D2 Q -> IsColimit D1 Q.
  Proof.
    intros HQ.
    serapply (Build_IsColimit (cocone_precompose m HQ) _).
    apply cocone_precompose_equiv_universality, HQ.
  Defined.

  Definition iscolimit_postcompose_equiv {D: Diagram G} `(f: Q <~> Q')
    : IsColimit D Q -> IsColimit D Q'.
  Proof.
    intros HQ.
    serapply (Build_IsColimit (cocone_postcompose HQ f) _).
    apply cocone_postcompose_equiv_universality, HQ.
  Defined.

  (** A diagram map [m] : [D1] => [D2] induces a map between any two colimits of [D1] and [D2]. *)

  Definition functoriality_colimit {D1 D2 : Diagram G} (m : DiagramMap D1 D2)
    {Q1 Q2} (HQ1 : IsColimit D1 Q1) (HQ2 : IsColimit D2 Q2)
    : Q1 -> Q2 := cocone_postcompose_inv HQ1 (cocone_precompose m HQ2).

  (** And this map commutes with diagram map. *)

  Definition functoriality_colimit_commute {D1 D2 : Diagram G}
    (m : DiagramMap D1 D2) {Q1 Q2}
    (HQ1 : IsColimit D1 Q1) (HQ2: IsColimit D2 Q2)
    : cocone_precompose m HQ2
      = cocone_postcompose HQ1 (functoriality_colimit m HQ1 HQ2)
    := (eisretr (cocone_postcompose HQ1) _)^.

  (** ** Colimits of equivalent diagrams *)

  (** Now we have than two equivalent diagrams have equivalent colimits. *)

  Context {D1 D2 : Diagram G} (m : D1 ~d~ D2) {Q1 Q2}
    (HQ1 : IsColimit D1 Q1) (HQ2 : IsColimit D2 Q2).

  Definition functoriality_colimit_eissect
    : Sect (functoriality_colimit (diagram_equiv_inv m) HQ2 HQ1)
           (functoriality_colimit m HQ1 HQ2).
  Proof.
    apply ap10.
    serapply (equiv_inj (cocone_postcompose HQ2) _).
    1: apply HQ2.
    etransitivity.
    2:symmetry; apply cocone_postcompose_identity.
    etransitivity.
    1: apply cocone_postcompose_comp.
    rewrite eisretr, cocone_precompose_postcompose, eisretr.
    rewrite cocone_precompose_comp, diagram_inv_is_section.
    apply cocone_precompose_identity.
  Defined.

  Definition functoriality_colimit_eisretr
    : Sect (functoriality_colimit m HQ1 HQ2)
           (functoriality_colimit (diagram_equiv_inv m) HQ2 HQ1).
  Proof.
    apply ap10.
    serapply (equiv_inj (cocone_postcompose HQ1) _).
    1: apply HQ1.
    etransitivity.
    2:symmetry; apply cocone_postcompose_identity.
    etransitivity.
    1: apply cocone_postcompose_comp.
    rewrite eisretr, cocone_precompose_postcompose, eisretr.
    rewrite cocone_precompose_comp, diagram_inv_is_retraction.
    apply cocone_precompose_identity.
  Defined.

  Global Instance isequiv_functoriality_colimit
    : IsEquiv (functoriality_colimit m HQ1 HQ2)
    := isequiv_adjointify _ _
      functoriality_colimit_eissect functoriality_colimit_eisretr.

  Definition functoriality_colimit_equiv : Q1 <~> Q2
    := BuildEquiv _ _ _ isequiv_functoriality_colimit.

End FunctorialityColimit.

(** * Unicity of colimits *)

(** A particuliar case of the functoriality result is that all colimits of a diagram are equivalent (and hence equal in presence of univalence). *)

Theorem colimit_unicity `{Funext} {G : Graph} {D : Diagram G} {Q1 Q2 : Type}
  (HQ1 : IsColimit D Q1) (HQ2 : IsColimit D Q2)
  : Q1 <~> Q2.
Proof.
  serapply functoriality_colimit_equiv.
  serapply (Build_diagram_equiv (diagram_idmap D)).
Defined.

(** * Colimits are left adjoint to constant diagram *)

Theorem colimit_adjoint `{Funext} {G : Graph} {D : Diagram G} {C : Type}
  : (Colimit D -> C) <~> DiagramMap D (diagram_const C).
Proof.
  symmetry.
  refine (equiv_colimit_rec C oE _).
  apply equiv_diagram_const_cocone.
Defined.

