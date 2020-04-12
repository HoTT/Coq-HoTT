(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics Types.
Require Import Pointed.Core.
Require Import WildCat.
Require Import pHomotopy pMap pEquiv.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** * pType as a wild category *)

Global Instance isgraph_ptype : IsGraph pType
  := Build_IsGraph pType pMap.

Global Instance is01cat_ptype : Is01Cat pType
  := Build_Is01Cat pType _ (@pmap_idmap) (@pmap_compose).

Global Instance isgraph_pmap (A B : pType) : IsGraph (A $-> B)
  := Build_IsGraph _ (@pHomotopy A (pfam_const B)).

Global Instance is01cat_pmap (A B : pType) : Is01Cat (A $-> B).
Proof.
  econstructor.
  - reflexivity.
  - intros a b c f g; transitivity b; assumption.
Defined.

Global Instance is0gpd_pmap (A B : pType) : Is0Gpd (A $-> B).
Proof.
  srapply Build_Is0Gpd.
  intros; symmetry; assumption.
Defined.

Global Instance is0functor_ptype_postcomp (a b c : pType) (g : b $-> c)
  : Is0Functor (cat_postcomp a g).
Proof.
  apply Build_Is0Functor.
  intros x y z.
  by apply pmap_postwhisker.
Defined.

Global Instance is0functor_ptype_precomp (a b c : pType) (g : a $-> b)
  : Is0Functor (cat_precomp c g).
Proof.
  apply Build_Is0Functor.
  intros x y z.
  by apply pmap_prewhisker.
Defined.

Global Instance is1cat_ptype : Is1Cat pType.
Proof.
  refine (Build_Is1Cat pType _ _ _ _ _ _ _ _ _ _).
  - intros ? ? ? ? f g h; exact (pmap_compose_assoc h g f).
  - intros ? ? f; exact (pmap_postcompose_idmap f).
  - intros ? ? f; exact (pmap_precompose_idmap f).
Defined.

Global Instance hasmorext_ptype `{Funext} : HasMorExt pType.
Proof.
  srapply Build_HasMorExt; intros A B f g.
  refine (isequiv_homotopic (equiv_path_pmap f g)^-1%equiv _).
  intros []; reflexivity.
Defined.

Global Instance hasequivs_ptype : HasEquivs pType.
Proof.
  srapply (Build_HasEquivs _ _ _ _ pEquiv (fun A B f => IsEquiv f));
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
Abort.
