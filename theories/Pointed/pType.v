(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics Types.
Require Import Pointed.Core.
Require Import WildCat.
Require Import pHomotopy pMap pEquiv.
Require Import UnivalenceImpliesFunext.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** * pType as a wild category *)

Global Instance is01cat_ptype : Is01Cat pType
  := Build_Is01Cat pType pMap (@pmap_idmap) (@pmap_compose).

Global Instance is01cat_pmap (A B : pType) : Is01Cat (A ->* B).
Proof.
  srapply (Build_Is01Cat (A ->* B) (@pHomotopy A B)).
  - reflexivity.
  - intros a b c f g; transitivity b; assumption.
Defined.

Global Instance is0gpd_pmap (A B : pType) : Is0Gpd (A ->* B).
Proof.
  srapply Build_Is0Gpd.
  intros; symmetry; assumption.
Defined.

Global Instance is1cat_ptype : Is1Cat pType.
Proof.
  econstructor.
  - intros A B C h; rapply Build_Is0Functor.
    intros f g p; cbn.
    apply pmap_postwhisker; assumption.
  - intros A B C h; rapply Build_Is0Functor.
    intros f g p; cbn.
    apply pmap_prewhisker; assumption.
  - intros ? ? ? ? f g h; exact (pmap_compose_assoc h g f).
  - intros ? ? f; exact (pmap_postcompose_idmap f).
  - intros ? ? f; exact (pmap_precompose_idmap f).
Defined.

Global Instance hasmorext_ptype `{Funext} : HasMorExt pType.
Proof.
  srapply Build_HasMorExt; intros A B f g.
  refine (isequiv_homotopic (equiv_path_pmap f g)^-1 _).
  intros []; reflexivity.
Defined.


Global Instance hasequivs_ptype : HasEquivs pType.
Proof.
  srapply (Build_HasEquivs _ _ _ pEquiv (fun A B f => IsEquiv f));
    intros A B f; cbn; intros.
  - exact f.
  - exact _.
  - exact (Build_pEquiv _ _ f _).
  - reflexivity.
  - exact ((Build_pEquiv _ _ f _)^-1*).
  - apply peissect.
  - cbn. refine (peisretr (Build_pEquiv _ _ f _)).
  - rapply (isequiv_adjointify f g).
    + intros x; exact (pointed_htpy r x).
    + intros x; exact (pointed_htpy s x).
Defined.

Global Instance isunivalent_ptype `{Univalence} : IsUnivalent1Cat pType.
Proof.
  srapply Build_IsUnivalent1Cat; intros A B.
  refine (isequiv_homotopic (equiv_path_ptype A B)^-1 _).
  intros []; apply path_pequiv.
  cbn.
  srefine (Build_pHomotopy _ _).
  - intros x; reflexivity.
  - cbn.
    (* Some messy path algebra here. *)
Abort.
