Require Import Basics Types.
Require Import Diagrams.Diagram.
Require Import Diagrams.Graph.
Require Import Diagrams.Cocone.
Require Import Diagrams.ConstantDiagram.
Require Import Colimits.Coeq.

Local Open Scope path_scope.
Generalizable All Variables.

(** This file contains the definition of colimits, and functoriality results on colimits. *)

(** * Colimits *)

(** A colimit is the extremity of a cocone. *)

Class IsColimit `(D: Diagram G) (Q: Type) := {
  iscolimit_cocone : Cocone D Q;
  iscolimit_unicocone : UniversalCocone iscolimit_cocone;
}.
(* Use :> and remove the two following lines,
   once Coq 8.16 is the minimum required version. *)
#[export] Existing Instance iscolimit_cocone.
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

(** ** Definition of the HIT 
<<
  HIT Colimit {G : Graph} (D : Diagram G) : Type :=
  | colim : forall i, D i -> Colimit D
  | colimp : forall i j (f : G i j) (x : D i) : colim j (D _f f x) = colim i x
  .
>>
*)

(** A colimit is just the coequalizer of the source and target maps of the diagram. *)
(** The source type in the coequalizer ought to be:
<<
{x : sig D & {y : sig D & {f : G x.1 y.1 & D _f f x.2 = y.2}}}
>>
However we notice that the path type forms a contractible component, so we can use the more efficient:
<<
{x : sig D & {j : G & G x.1 j}}
>>
*)
Definition Colimit {G : Graph} (D : Diagram G) : Type :=
  @Coeq
    {x : sig D & {j : G & G x.1 j}}
    (sig D)
    (fun t => t.1)
    (fun t => (t.2.1; D _f t.2.2 t.1.2))
  .

Definition colim {G : Graph} {D : Diagram G} (i : G) (x : D i) : Colimit D :=
  coeq (i ; x).

Definition colimp {G : Graph} {D : Diagram G} (i j : G) (f : G i j) (x : D i)
  : colim j (D _f f x) = colim i x
  := (cglue ((i; x); j; f))^.

Definition Colimit_ind {G : Graph} {D : Diagram G} (P : Colimit D -> Type)
(q : forall i x, P (colim i x))
(pp_q : forall (i j : G) (g: G i j) (x : D i),
  (@colimp G D i j g x) # (q j (D _f g x)) = q i x)
: forall w, P w.
Proof.
  srapply Coeq_ind.
  - intros [x i].
    exact (q x i).
  - intros [[i x] [j f]].
    cbn in f; cbn.
    apply moveR_transport_p.
    symmetry.
    exact (pp_q _ _ _ _).
Defined.

Definition Colimit_ind_beta_colimp {G : Graph} {D : Diagram G}
  (P : Colimit D -> Type) (q : forall i x, P (colim i x))
  (pp_q : forall (i j: G) (g: G i j) (x: D i),
    @colimp G D i j g x # q _ (D _f g x) = q _ x)
  (i j : G) (g : G i j) (x : D i)
  : apD (Colimit_ind P q pp_q) (colimp i j g x) = pp_q i j g x.
Proof.
  refine (apD_V _ _ @ _).
  apply moveR_equiv_M.
  apply moveR_equiv_M.
  refine (Coeq_ind_beta_cglue _ _ _ _ @ _).
  symmetry.
  apply moveL_transport_p_V.
Defined.

Definition Colimit_rec {G : Graph} {D : Diagram G} (P : Type) (C : Cocone D P)
  : Colimit D -> P.
Proof.
  srapply (Colimit_ind _ C).
  intros i j g x.
  refine (transport_const _ _ @ _).
  apply legs_comm.
Defined.

Definition Colimit_rec_beta_colimp {G : Graph} {D : Diagram G}
  (P : Type) (C : Cocone D P) (i j : G) (g: G i j) (x: D i)
  : ap (Colimit_rec P C) (colimp i j g x) = legs_comm C i j g x.
Proof.
  rapply (cancelL (transport_const (colimp i j g x) _)).
  srapply ((apD_const (Colimit_ind (fun _ => P) C _) (colimp i j g x))^ @ _).
  srapply (Colimit_ind_beta_colimp (fun _ => P) C _ i j g x).
Defined.

Arguments colim : simpl never.
Arguments colimp : simpl never.

(** Colimit_rec is an equivalence *)

Global Instance isequiv_colimit_rec `{Funext} {G : Graph}
  {D : Diagram G} (P : Type) : IsEquiv (Colimit_rec (D:=D) P).
Proof.
  srapply isequiv_adjointify.
  { intro f.
    srapply Build_Cocone.
    1: intros i g; apply f, (colim i g).
    intros i j g x.
    apply ap, colimp. }
  { intro.
    apply path_forall.
    srapply Colimit_ind.
    1: reflexivity.
    intros ????; cbn.
    nrapply transport_paths_FlFr'.
    apply equiv_p1_1q.
    apply Colimit_rec_beta_colimp. }
  { intros [].
    srapply path_cocone.
    1: reflexivity.
    intros ????; cbn.
    rewrite Colimit_rec_beta_colimp.
    hott_simpl. }
Defined.

Definition equiv_colimit_rec `{Funext} {G : Graph} {D : Diagram G} (P : Type)
  : Cocone D P <~> (Colimit D -> P) := Build_Equiv _ _ _ (isequiv_colimit_rec P).

(** And we can now show that the HIT is actually a colimit. *)

Definition cocone_colimit {G : Graph} (D : Diagram G) : Cocone D (Colimit D)
  := Build_Cocone colim colimp.

Global Instance unicocone_colimit `{Funext} {G : Graph} (D : Diagram G)
  : UniversalCocone (cocone_colimit D).
Proof.
  srapply Build_UniversalCocone; intro Y.
  srapply (isequiv_adjointify _ (Colimit_rec Y) _ _).
  - intros C.
    srapply path_cocone.
    1: reflexivity.
    intros i j f x; simpl.
    apply equiv_p1_1q.
    apply Colimit_rec_beta_colimp.
  - intro f.
    apply path_forall.
    srapply Colimit_ind.
    1: reflexivity.
    intros i j g x; simpl.
    nrapply (transport_paths_FlFr' (g:=f)).
    apply equiv_p1_1q.
    apply Colimit_rec_beta_colimp.
Defined.

Global Instance iscolimit_colimit `{Funext} {G : Graph} (D : Diagram G)
  : IsColimit D (Colimit D) := Build_IsColimit _ (unicocone_colimit D).

(** ** Functoriality of concrete colimits *)

(** We will capitalize [Colimit] to indicate that these definitions relate to the concrete colimit defined above.  Below, we will also get functoriality for abstract colimits, without the capital C.  However, to apply those results to the concrete colimit uses [iscolimit_colimit], which requires [Funext], so it is also useful to give direct proofs of some facts. *)

Definition functor_Colimit {G : Graph} {D1 D2 : Diagram G} (m : DiagramMap D1 D2)
  : Colimit D1 -> Colimit D2.
Proof.
  apply Colimit_rec.
  refine (cocone_precompose m (cocone_colimit D2)).
Defined.

Definition functor_Colimit_homotopy {G : Graph} {D1 D2 : Diagram G}
  {m1 m2 : DiagramMap D1 D2} (h_obj : forall i, m1 i == m2 i)
  (h_comm : forall i j (g : G i j) x,
      DiagramMap_comm m1 g x @ h_obj j (D1 _f g x)
      = ap (D2 _f g) (h_obj i x) @ DiagramMap_comm m2 g x)
  : functor_Colimit m1 == functor_Colimit m2.
Proof.
  (* The proof is very similar to the proof of [functor_coeq_homotopy], but it's not clear if we can easily reuse that here. We'd have to redefine [functor_Colimit] using [functor_coeq], and that is more awkward. *)
  snrapply Colimit_ind.
  - intros i x; simpl.
    apply ap, h_obj.
  - intros i j g x; simpl.
    Open Scope long_path_scope.
    nrapply (transport_paths_FlFr' (colimp i j g x)); simpl.
    rewrite 2 Colimit_rec_beta_colimp; simpl.
    rewrite ap_V.
    lhs nrapply concat_pp_p.
    apply moveR_Vp.
    rewrite ! concat_p_pp.
    rewrite <- 2 ap_pp.
    rewrite h_comm.
    rewrite concat_pp_V.
    rewrite <- ap_compose.
    exact (concat_Ap (colimp i j g) (h_obj i x))^.
    Close Scope long_path_scope.
Qed.

(** ** Functoriality of abstract colimits *)

Section FunctorialityColimit.

  Context `{Funext} {G : Graph}.

  (** Colimits are preserved by composition with a (diagram) equivalence. *)

  Definition iscolimit_precompose_equiv {D1 D2 : Diagram G}
    (m : D1 ~d~ D2) {Q : Type}
    : IsColimit D2 Q -> IsColimit D1 Q.
  Proof.
    intros HQ.
    srapply (Build_IsColimit (cocone_precompose m HQ) _).
    apply cocone_precompose_equiv_universality, HQ.
  Defined.

  Definition iscolimit_postcompose_equiv {D: Diagram G} `(f: Q <~> Q')
    : IsColimit D Q -> IsColimit D Q'.
  Proof.
    intros HQ.
    srapply (Build_IsColimit (cocone_postcompose HQ f) _).
    apply cocone_postcompose_equiv_universality, HQ.
  Defined.

  (** A diagram map [m] : [D1] => [D2] induces a map between any two colimits of [D1] and [D2]. *)

  Definition functor_colimit {D1 D2 : Diagram G} (m : DiagramMap D1 D2)
    {Q1 Q2} (HQ1 : IsColimit D1 Q1) (HQ2 : IsColimit D2 Q2)
    : Q1 -> Q2 := cocone_postcompose_inv HQ1 (cocone_precompose m HQ2).

  (** And this map commutes with diagram map. *)

  Definition functor_colimit_commute {D1 D2 : Diagram G}
    (m : DiagramMap D1 D2) {Q1 Q2}
    (HQ1 : IsColimit D1 Q1) (HQ2: IsColimit D2 Q2)
    : cocone_precompose m HQ2
      = cocone_postcompose HQ1 (functor_colimit m HQ1 HQ2)
    := (eisretr (cocone_postcompose HQ1) _)^.

  (** ** Colimits of equivalent diagrams *)

  (** Now we have than two equivalent diagrams have equivalent colimits. *)

  Context {D1 D2 : Diagram G} (m : D1 ~d~ D2) {Q1 Q2}
    (HQ1 : IsColimit D1 Q1) (HQ2 : IsColimit D2 Q2).

  Definition functor_colimit_eissect
    : functor_colimit m HQ1 HQ2
      o functor_colimit (diagram_equiv_inv m) HQ2 HQ1 == idmap.
  Proof.
    apply ap10.
    srapply (equiv_inj (cocone_postcompose HQ2) _).
    1: apply HQ2.
    etransitivity.
    2:symmetry; apply cocone_postcompose_identity.
    etransitivity.
    1: apply cocone_postcompose_comp.
    rewrite eisretr, cocone_precompose_postcompose, eisretr.
    rewrite cocone_precompose_comp, diagram_inv_is_section.
    apply cocone_precompose_identity.
  Defined.

  Definition functor_colimit_eisretr
    : functor_colimit (diagram_equiv_inv m) HQ2 HQ1
      o functor_colimit m HQ1 HQ2 == idmap.
  Proof.
    apply ap10.
    srapply (equiv_inj (cocone_postcompose HQ1) _).
    1: apply HQ1.
    etransitivity.
    2:symmetry; apply cocone_postcompose_identity.
    etransitivity.
    1: apply cocone_postcompose_comp.
    rewrite eisretr, cocone_precompose_postcompose, eisretr.
    rewrite cocone_precompose_comp, diagram_inv_is_retraction.
    apply cocone_precompose_identity.
  Defined.

  Global Instance isequiv_functor_colimit
    : IsEquiv (functor_colimit m HQ1 HQ2)
    := isequiv_adjointify _ _
      functor_colimit_eissect functor_colimit_eisretr.

  Definition equiv_functor_colimit : Q1 <~> Q2
    := Build_Equiv _ _ _ isequiv_functor_colimit.

End FunctorialityColimit.

(** * Unicity of colimits *)

(** A particuliar case of the functoriality result is that all colimits of a diagram are equivalent (and hence equal in presence of univalence). *)

Theorem colimit_unicity `{Funext} {G : Graph} {D : Diagram G} {Q1 Q2 : Type}
  (HQ1 : IsColimit D Q1) (HQ2 : IsColimit D Q2)
  : Q1 <~> Q2.
Proof.
  srapply equiv_functor_colimit.
  srapply (Build_diagram_equiv (diagram_idmap D)).
Defined.

(** * Colimits are left adjoint to constant diagram *)

Theorem colimit_adjoint `{Funext} {G : Graph} {D : Diagram G} {C : Type}
  : (Colimit D -> C) <~> DiagramMap D (diagram_const C).
Proof.
  symmetry.
  refine (equiv_colimit_rec C oE _).
  apply equiv_diagram_const_cocone.
Defined.

