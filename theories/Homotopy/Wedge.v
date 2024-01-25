Require Import Basics Types.
Require Import Pointed.Core.
Require Import Colimits.Pushout.
Require Import WildCat.

(* Here we define the Wedge sum of two pointed types *)

Local Open Scope pointed_scope.

Definition Wedge (X Y : pType) : pType
  := [Pushout (fun _ : Unit => point X) (fun _ => point Y), pushl (point X)].

Notation "X \/ Y" := (Wedge X Y) : pointed_scope.

Definition wedge_inl {X Y} : X $-> X \/ Y.
Proof.
  snrapply Build_pMap.
  - exact (fun x => pushl x).
  - reflexivity.
Defined.

Definition wedge_inr {X Y} : Y $-> X \/ Y.
Proof.
  snrapply Build_pMap.
  - exact (fun x => pushr x).
  - symmetry.
    by rapply pglue.
Defined.

Definition wglue {X Y : pType}
  : pushl (point X) = (pushr (point Y) : X \/ Y) := pglue tt.

Definition wedge_rec {X Y Z : pType} (f : X $-> Z) (g : Y $-> Z)
  : X \/ Y $-> Z.
Proof.
  snrapply Build_pMap.
  - snrapply Pushout_rec.
    + exact f.
    + exact g.
    + by pelim f g.
  - exact (point_eq f).
Defined.

Definition wedge_incl {X Y : pType} : X \/ Y -> X * Y :=
 Pushout_rec _ (fun x => (x, point Y)) (fun y => (point X, y)) 
  (fun _ : Unit => idpath).

(** 1-universal property of wedge. *)
(** TODO: remove rewrites. For some reason pelim is not able to immediately abstract the goal so some shuffling around is necessery. *)
Lemma wedge_up X Y Z (f g : X \/ Y $-> Z)
  : f $o wedge_inl $== g $o wedge_inl
  -> f $o wedge_inr $== g $o wedge_inr
  -> f $== g.
Proof.
  intros p q.
  snrapply Build_pHomotopy.
  - snrapply (Pushout_ind _ p q).
    intros [].
    simpl.
    refine (transport_paths_FlFr _ _ @ _).
    refine (concat_pp_p _ _ _ @ _).
    apply moveR_Vp.
    refine (whiskerR (dpoint_eq p) _ @ _).
    refine (_ @ whiskerL _ (dpoint_eq q)^).
    clear p q.
    simpl.
    apply moveL_Mp.
    rewrite ? ap_V.
    rewrite ? inv_pp.
    hott_simpl.
  - simpl; pelim p q.
    hott_simpl.
Defined.

Global Instance hasbinarycoproducts : HasBinaryCoproducts pType.
Proof.
  intros X Y.
  snrapply Build_BinaryCoproduct.
  - exact (X \/ Y).
  - exact wedge_inl.
  - exact wedge_inr.
  - intros Z f g.
    by apply wedge_rec.
  - intros Z f g.
    snrapply Build_pHomotopy.
    1: reflexivity.
    by simpl; pelim f.
  - intros Z f g.
    snrapply Build_pHomotopy.
    1: reflexivity.
    simpl.
    apply moveL_pV.
    apply moveL_pM.
    refine (_ @ (ap_V _ (pglue tt))^).
    apply moveR_Mp.
    apply moveL_pV.
    apply moveR_Vp.
    refine (Pushout_rec_beta_pglue _ f g _ _  @ _).
    simpl.  
    by pelim f g.
  - intros Z f g p q.
    by apply wedge_up.
Defined.

(** Wedge of an indexed family of pointed types *)

(** Note that the index type is not necesserily pointed. An empty wedge is the unit type which is the zero object in the category of pointed types. *)
Definition FamilyWedge (I : Type) (X : I -> pType) : pType.
Proof.
  snrapply Build_pType.
  - srefine (Pushout (A := sig (fun _ : I => pUnit)) (B := sig X) (C := pUnit) _ _).
    + snrapply functor_sigma.
      1: exact idmap.
      intros i.
      exact (fun _ => pt).
    + exact (fun _ => pt).
  - apply pushr.
    exact pt.
Defined.

(** We have an inclusion map [pushl : sig X -> FamilyWedge X].  When [I] is pointed, so is [sig X], and then this inclusion map is pointed. *)
Definition fwedge_in (I : pType) (X : I -> pType)
  : psigma (pointed_fam X) $-> FamilyWedge I X.
Proof.
  snrapply Build_pMap.
  - exact pushl.
  - exact (pglue (pt; pt)).
Defined.

(** Recursion principle for the wedge of an indexed family of pointed types. *)
Definition fwedge_rec (I : Type) (X : I -> pType) (Z : pType)
  (f : forall i, X i $-> Z)
  : FamilyWedge I X $-> Z.
Proof.
  snrapply Build_pMap.
  - snrapply Pushout_rec.
    + apply (sig_rec _ _ _ f).
    + exact pconst.
    + intros [i ?].
      exact (point_eq (f i)).
  - exact idpath.
Defined.

(** Wedge inclusions into the product can be defined if the indexing type has decidable paths. This is because we need to choose which factor a given wedge should land. This makes it somewhat awkward to work with, however in practice we typically only care about decidable index sets. *) 
Definition fwedge_incl `{Funext} (I : Type) `(DecidablePaths I) (X : I -> pType)
  : FamilyWedge I X $-> pproduct X.
Proof.
  snrapply fwedge_rec.
  intro i.
  snrapply pproduct_corec.
  intro a.
  destruct (dec_paths i a).
  - destruct p; exact pmap_idmap.
  - exact pconst.
Defined.
