From HoTT Require Import Basics Types.
Require Import Pointed.Core Pointed.pSusp.
Require Import Colimits.Pushout.
Require Import WildCat.Coproducts WildCat.Products.
Require Import Homotopy.Suspension.
Require Import Truncations.Core Truncations.Connectedness.
Require Import Extensions Modalities.ReflectiveSubuniverse.

(** * Wedge sums *)

Local Open Scope pointed_scope.

Definition Wedge@{i j k | i <= k, j <= k} (X : pType@{i}) (Y : pType@{j}) : pType@{k}
  := [Pushout@{Set i j k} (fun _ : Unit => point X) (fun _ => point Y), pushl (point X)].

Notation "X \/ Y" := (Wedge X Y) : pointed_scope.

Definition wglue {X Y : pType}
  : pushl (point X) = (pushr (point Y)) :> (X \/ Y) := pglue tt.

Definition wedge_inl {X Y : pType} : X ->* X \/ Y
  := Build_pMap pushl 1.

Definition wedge_inr {X Y : pType} : Y ->* X \/ Y
  := Build_pMap pushr wglue^.

(** Wedge recursion into an unpointed type. *)
Definition wedge_rec' {X Y : pType} {Z : Type}
  (f : X -> Z) (g : Y -> Z) (w : f pt = g pt)
  : Wedge X Y -> Z
  := Pushout_rec Z f g (fun _ => w).

Definition wedge_rec {X Y : pType} {Z : pType} (f : X ->* Z) (g : Y ->* Z)
  : X \/ Y ->* Z
  := Build_pMap (wedge_rec' f g (point_eq f @ (point_eq g)^)) (point_eq f).

Definition wedge_rec_beta_wglue {X Y Z : pType} (f : X ->* Z) (g : Y ->* Z)
  : ap (wedge_rec f g) wglue = point_eq f @ (point_eq g)^
  := Pushout_rec_beta_pglue _ f g _ tt.

Definition wedge_rec_beta_inl {X Y : pType} {Z : pType} (f : X ->* Z) (g : Y ->* Z)
  : wedge_rec f g o* wedge_inl ==* f.
Proof.
  snapply Build_pHomotopy.
  1: reflexivity.
  cbn beta; symmetry.
  exact (concat_pp_V 1 (point_eq f)).
Defined.

Definition wedge_rec_beta_inr {X Y : pType} {Z : pType} (f : X ->* Z) (g : Y ->* Z)
  : wedge_rec f g o* wedge_inr ==* g.
Proof.
  snapply Build_pHomotopy.
  1: reflexivity.
  cbn -[wedge_rec].
  rhs napply concat_pp_p.
  rhs napply (ap_V _ _ @@ 1).
  apply moveL_Vp.
  lhs napply concat_p1.
  napply wedge_rec_beta_wglue.
Defined.

Definition wedge_pr1 {X Y : pType} : X \/ Y ->* X
  := wedge_rec pmap_idmap pconst.

Definition wedge_pr2 {X Y : pType} : X \/ Y ->* Y
  := wedge_rec pconst pmap_idmap.

Definition wedge_incl (X Y : pType) : X \/ Y ->* X * Y
  := pprod_corec _ wedge_pr1 wedge_pr2.

Definition wedge_incl_beta_wglue {X Y : pType}
  : ap (@wedge_incl X Y) wglue = 1.
Proof.
  lhs_V napply eta_path_prod.
  napply (ap011 _ (x':=1) (y':=1)).
  - lhs_V napply (ap_compose (wedge_incl X Y) _ wglue).
    napply wedge_rec_beta_wglue.
  - lhs_V napply (ap_compose (wedge_incl X Y) _ wglue).
    napply wedge_rec_beta_wglue.
Defined.

Definition wedge_ind {X Y : pType} (P : X \/ Y -> Type)
  (f : forall x, P (wedge_inl x)) (g : forall y, P (wedge_inr y))
  (w : wglue # f pt = g pt)
  : forall xy, P xy.
Proof.
  napply (Pushout_ind P f g).
  intros [].
  exact w.
Defined.

Definition wedge_ind_beta_wglue {X Y : pType} (P : X \/ Y -> Type)
  (f : forall x, P (wedge_inl x)) (g : forall y, P (wedge_inr y))
  (w : wglue # f pt = g pt)
  : apD (wedge_ind P f g w) wglue = w
  := Pushout_ind_beta_pglue P _ _ _ _.

Definition wedge_ind_FlFr {X Y Z : pType} {f g : X \/ Y -> Z}
  (l : f o wedge_inl == g o wedge_inl)
  (r : f o wedge_inr == g o wedge_inr)
  (w : ap f wglue @ r pt = l pt @ ap g wglue)
  : f == g.
Proof.
  napply (wedge_ind _ l r).
  transport_paths FlFr.
  exact w.
Defined.

Definition wedge_ind_FFl {X Y Z W : pType} (f : X \/ Y -> Z) (g : Z -> W)
  {y : W}
  (l : forall x, g (f (wedge_inl x)) = y)
  (r : forall x, g (f (wedge_inr x)) = y)
  (w : l pt = ap g (ap f wglue) @ r pt)
  : forall x, g (f x) = y.
Proof.
  napply (wedge_ind _ l r); simpl.
  transport_paths FFl.
  exact w.
Defined.

Definition wedge_ind_FFlr {X Y Z : pType} (f : X \/ Y -> Z) (g : Z -> X \/ Y)
  (l : g o f o wedge_inl == wedge_inl)
  (r : g o f o wedge_inr == wedge_inr)
  (w : ap g (ap f wglue) @ r pt = l pt @ wglue)
  : g o f == idmap.
Proof.
  napply (wedge_ind _ l r); simpl.
  transport_paths FFlr.
  exact w.
Defined.

(** 1-universal property of wedge. *)
Lemma wedge_up X Y Z (f g : X \/ Y ->* Z)
  (p : f o* wedge_inl ==* g o* wedge_inl)
  (q : f o* wedge_inr ==* g o* wedge_inr)
  : f ==* g.
Proof.
  snapply Build_pHomotopy.
  - napply (wedge_ind_FlFr p q).
    lhs napply (1 @@ dpoint_eq q).
    rhs napply (dpoint_eq p @@ 1).
    clear p q; simpl.
    rhs napply (((concat_1p _) @@ ap inverse (concat_1p _)) @@ 1).
    lhs napply concat_p_pp.
    apply moveR_pV.
    lhs napply (1 @@ (ap_V _ _ @@ 1)).
    lhs napply concat_p_Vp.
    rhs napply concat_p_pp.
    rhs napply ((1 @@ ap_V _ _) @@ 1).
    rhs napply (concat_pp_V _ _ @@ 1).
    by apply moveL_pM.
  - simpl.
    lhs exact (dpoint_eq p); simpl.
    exact (concat_1p _ @@ ap inverse (concat_1p _)).
Defined.

Instance hasbinarycoproducts : HasBinaryCoproducts pType.
Proof.
  intros X Y.
  snapply Build_BinaryCoproduct.
  - exact (X \/ Y).
  - exact wedge_inl.
  - exact wedge_inr.
  - exact (@wedge_rec X Y).
  - exact (@wedge_rec_beta_inl X Y).
  - exact (@wedge_rec_beta_inr X Y).
  - exact (wedge_up X Y).
Defined.

(** *** Lemmas about wedge functions *)

Lemma wedge_pr1_inl {X Y} : wedge_pr1 o* (@wedge_inl X Y) ==* pmap_idmap.
Proof.
  reflexivity.
Defined.

Lemma wedge_pr1_inr {X Y} : wedge_pr1 o* (@wedge_inr X Y) ==* pconst.
Proof.
  snapply Build_pHomotopy.
  1: reflexivity.
  symmetry; simpl.
  do 2 lhs napply concat_p1.
  lhs napply (ap_V _ wglue).
  exact (inverse2 (wedge_rec_beta_wglue pmap_idmap pconst)).
Defined.

Lemma wedge_pr2_inl {X Y} : wedge_pr2 o* (@wedge_inl X Y) ==* pconst.
Proof.
  reflexivity.
Defined.

Lemma wedge_pr2_inr {X Y} : wedge_pr2 o* (@wedge_inr X Y) ==* pmap_idmap.
Proof.
  snapply Build_pHomotopy.
  1: reflexivity.
  symmetry; simpl.
  do 2 lhs napply concat_p1.
  lhs napply (ap_V _ wglue).
  exact (inverse2 (wedge_rec_beta_wglue pconst pmap_idmap)).
Defined.

(** Wedge of an indexed family of pointed types *)

(** Note that the index type is not necessarily pointed. An empty wedge is the unit type which is the zero object in the category of pointed types. *)
Definition FamilyWedge (I : Type) (X : I -> pType) : pType.
Proof.
  snapply Build_pType.
  - srefine (Pushout (A := I) (B := sig X) (C := pUnit) _ _).
    + exact (fun i => (i; pt)).
    + exact (fun _ => pt).
  - apply pushr.
    exact pt.
Defined.

Definition fwedge_in' (I : Type) (X : I -> pType)
  : forall i, X i ->* FamilyWedge I X
  := fun i => Build_pMap (fun x => pushl (i; x)) (pglue i).

(** We have an inclusion map [pushl : sig X -> FamilyWedge X].  When [I] is pointed, so is [sig X], and then this inclusion map is pointed. *)
Definition fwedge_in (I : pType) (X : I -> pType)
  : psigma (pointed_fam X) ->* FamilyWedge I X
  := Build_pMap pushl (pglue pt).

(** Recursion principle for the wedge of an indexed family of pointed types. *)
Definition fwedge_rec (I : Type) (X : I -> pType) (Z : pType)
  (f : forall i, X i ->* Z)
  : FamilyWedge I X ->* Z.
Proof.
  snapply Build_pMap.
  - snapply Pushout_rec.
    + exact (sig_rec f).
    + exact pconst.
    + intros i.
      exact (point_eq (f i)).
  - exact idpath.
Defined.

Instance hasallcoproducts_ptype : HasAllCoproducts pType.
Proof.
  intros I X.
  snapply Build_Coproduct.
  - exact (FamilyWedge I X).
  - exact (fwedge_in' I X).
  - exact (fwedge_rec I X).
  - intros Z f i.
    snapply Build_pHomotopy.
    1: reflexivity.
    simpl.
    apply moveL_pV.
    apply equiv_1p_q1.
    symmetry.
    exact (Pushout_rec_beta_pglue Z _ (unit_name pt) (fun i => point_eq (f i)) _).
  - intros Z f g h.
    snapply Build_pHomotopy.
    + snapply Pushout_ind.
      * intros [i x].
        napply h.
      * intros [].
        exact (point_eq _ @ (point_eq _)^).
      * intros i; cbn.
        transport_paths FlFr.
        lhs napply concat_p_pp.
        apply moveR_pV.
        rhs napply concat_pp_p.
        apply moveL_pM.
        symmetry.
        exact (dpoint_eq (h i)).
    + reflexivity.
Defined.

(** Wedge inclusions into the product can be defined if the indexing type has decidable paths. This is because we need to choose which factor a given wedge summand should land in. *)
Definition fwedge_incl `{Funext} (I : Type) `(DecidablePaths I) (X : I -> pType)
  : FamilyWedge I X ->* pproduct X
  := cat_coprod_prod X.

(** ** The pinch map on the suspension *)

(** Given a suspension, there is a natural map from the suspension to the wedge of the suspension with itself. This is known as the pinch map.

This is the image to keep in mind:
<<
                                    *
                                   /|\
                                  / | \
    Susp X                       /  |  \
                                /   |   \
       *                       * merid(x)*
      /|\                       \   |   /
     / | \                       \  |  /
    /  |  \                       \ | /
   /   |   \      Pinch            \|/
  * merid(x)*   ---------->         *
   \   |   /                       /|\
    \  |  /                       / | \
     \ | /                       /  |  \
      \|/                       /   |   \
       *                       * merid(x)*
                                \   |   /
                                 \  |  /
                                  \ | /
                                   \|/
                                    *
>>

Note that this is only a conceptual picture as we aren't working with "reduced suspensions". This means we have to track back along [merid pt] making this map a little trickier to imagine. *)

(** The pinch map for a suspension. *)
Definition psusp_pinch (X : pType) : psusp X ->* psusp X \/ psusp X.
Proof.
  refine (Build_pMap (Susp_rec pt pt _) idpath).
  intros x.
  refine (ap wedge_inl _ @ wglue @ ap wedge_inr _ @ wglue^).
  1,2: exact (loop_susp_unit X x).
Defined.

(** It should compute when [ap]ed on a merid. *)
Definition psusp_pinch_beta_merid {X : pType} (x : X)
  : ap (psusp_pinch X) (merid x)
    = ap wedge_inl (loop_susp_unit X x) @ wglue
    @ ap wedge_inr (loop_susp_unit X x) @ wglue^.
Proof.
  rapply Susp_rec_beta_merid.
Defined.

(** Doing wedge projections on the pinch map gives the identity. *)
Definition wedge_pr1_psusp_pinch {X}
  : wedge_pr1 o* psusp_pinch X ==* @pmap_idmap (psusp X).
Proof.
  snapply Build_pHomotopy.
  - snapply Susp_ind_FlFr.
    + reflexivity.
    + exact (merid pt).
    + intros x.
      rhs napply concat_1p.
      rhs napply ap_idmap.
      apply moveR_pM.
      change (?t = _) with (t = loop_susp_unit X x).
      lhs napply (ap_compose (psusp_pinch X)).
      lhs napply (ap _ (psusp_pinch_beta_merid x)).
      lhs napply ap_pV.
      apply moveR_pV.
      rhs napply (whiskerL _ (wedge_rec_beta_wglue _ _)).
      lhs napply ap_pp.
      lhs napply (ap (fun x => _ @ x)).
      { lhs_V napply ap_compose.
        apply ap_const. }
      lhs napply concat_p1.
      lhs napply ap_pp.
      lhs napply (ap (fun x => _ @ x) (wedge_rec_beta_wglue _ _)).
      f_ap.
      lhs_V napply (ap_compose wedge_inl).
      apply ap_idmap.
  - reflexivity.
Defined.

Definition wedge_pr2_psusp_pinch {X}
  : wedge_pr2 o* psusp_pinch X ==* @pmap_idmap (psusp X).
Proof.
  snapply Build_pHomotopy.
  - snapply Susp_ind_FlFr.
    + reflexivity.
    + exact (merid pt).
    + intros x.
      rhs napply concat_1p.
      rhs napply ap_idmap.
      apply moveR_pM.
      change (?t = _) with (t = loop_susp_unit X x).
      lhs napply (ap_compose (psusp_pinch X)).
      lhs napply (ap _ (psusp_pinch_beta_merid x)).
      lhs napply ap_pV.
      apply moveR_pV.
      rhs napply (whiskerL _ (wedge_rec_beta_wglue _ _)).
      lhs napply ap_pp.
      lhs napply (ap (fun x => _ @ x) _).
      { lhs_V napply ap_compose.
        apply ap_idmap. }
      rhs napply concat_p1.
      apply moveR_pM.
      lhs napply ap_pp.
      rhs napply concat_pV.
      lhs napply (ap _ (wedge_rec_beta_wglue _ _)).
      apply moveR_pM.
      lhs_V napply (ap_compose wedge_inl).
      rapply ap_const.
  - reflexivity.
Defined.

(** ** Connectivity of wedge inclusion *)

Definition extension_wedge_incl {X Y : pType} (P : X * Y -> Type)
  (d : forall a : X \/ Y, P (wedge_incl X Y a))
  (f : forall (x : X) (y : Y), P (x, y))
  (p : forall (x : X), f x pt = d (wedge_inl x))
  (q : forall (y : Y), f pt y = d (wedge_inr y))
  (pq : p pt
        = q pt
            @ ((apD d wglue)^
                 @ transport_compose_path_ap P (wedge_incl X Y) (wedge_incl_beta_wglue) _))
  : ExtensionAlong (wedge_incl X Y) P d.
Proof.
  exists (prod_ind _ f).
  napply (wedge_ind _ p q).
  lhs napply (transport_paths_FlFr_D wglue).
  apply moveR_pM.
  apply moveR_Vp.
  unshelve lhs napply ap_homotopic_id.
  1: exact (transport_compose_path_ap P (wedge_incl X Y) wedge_incl_beta_wglue).
  change (prod_ind P f (wedge_incl X Y (pushl pt))) with (f pt pt).
  apply moveR_pV.
  rhs napply concat_pp_p.
  rhs napply (1 @@ concat_pp_p _ _ _).
  nrefine (_ @@ pq).
  symmetry.
  lhs napply apD_compose.
  unfold transport_compose_path_ap.
  apply whiskerL.
  lhs napply (apD02 _ wedge_incl_beta_wglue).
  apply concat_p1.
Defined.

Definition conn_map_wedge_incl `{Univalence} {m n : trunc_index} (X Y : pType)
  `{!IsConnected m.+1 X, !IsConnected n.+1 Y}
  : IsConnMap (m +2+ n) (wedge_incl X Y).
Proof.
  apply conn_map_from_extension_elim.
  intros P h d.
  snapply extension_wedge_incl.
  - rapply (wedge_incl_elim _ _ (fun x y => P (x, y)) (d o wedge_inr) (d o wedge_inl)).
    lhs_V exact (apD d wglue).
    exact (transport_compose_path_ap P (wedge_incl X Y) wedge_incl_beta_wglue _).
  - napply wedge_incl_comp2.
  - napply wedge_incl_comp1.
  - napply wedge_incl_comp3.
Defined.

(** A more elementary fact is that a wedge of [n]-connected types is [n]-connected. *)
Definition isconnected_wedge `{Univalence} (n : trunc_index) (X Y : pType)
  `{IsConnected n X} `{IsConnected n Y}
  : IsConnected n (Wedge X Y).
Proof.
  destruct n.
  1: exact _.
  apply isconnected_from_elim.
  intros C H' f.  exists (f pt).
  intro x; symmetry; revert x.
  snapply wedge_ind; cbn.
  - by rapply conn_point_elim.
  - rapply conn_point_elim.
    apply ap, wglue.
  - transport_paths Fr.
    rewrite 2 conn_point_elim_comp.
    apply concat_1p.
Defined.
