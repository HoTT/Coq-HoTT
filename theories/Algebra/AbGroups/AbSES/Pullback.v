Require Import Basics Types HSet HFiber Limits.Pullback Cubical.PathSquare.
Require Import WildCat Pointed Homotopy.ExactSequence.
Require Import AbGroups.AbelianGroup AbGroups.AbPullback AbSES.Core.

Local Open Scope abses_scope.

(** * Pullbacks of short exact sequences *)

(** A short exact sequence [A -> E -> B] can be pulled back along a map [B' -> B]. We start by defining the underlying map, then the pointed version. *)
Definition abses_pullback0 {A B B' : AbGroup} (f : B' $-> B)
  : AbSES B A -> AbSES B' A.
Proof.
  intro E.
  snrapply (Build_AbSES (ab_pullback (projection E) f)
                        (grp_pullback_corec _ _ (inclusion _) grp_homo_const _)
                        (grp_pullback_pr2 (projection _) f)).
  - intro x.
    nrefine (_ @ (grp_homo_unit f)^).
    apply isexact_inclusion_projection.
  - exact (cancelL_isembedding (g:= grp_pullback_pr1 _ _)).
  - rapply conn_map_pullback'.
  - snrapply Build_IsExact.
    + srapply Build_pHomotopy.
      * reflexivity.
      * apply path_ishprop.
    + nrefine (cancelR_equiv_conn_map
                 _ _ (hfiber_pullback_along_pointed f (projection _) (grp_homo_unit _))).
      nrefine (conn_map_homotopic _ _ _ _ (conn_map_isexact (IsExact:=isexact_inclusion_projection _))).
      intro a.
      by apply path_sigma_hprop.
Defined.

(** ** The universal property of [abses_pullback_morphism] *)

(** The natural map from the pulled back sequence. *)
Definition abses_pullback_morphism {A B B' : AbGroup} (E : AbSES B A) (f : B' $-> B)
  : AbSESMorphism (abses_pullback0 f E) E.
Proof.
  snrapply (Build_AbSESMorphism grp_homo_id _ f).
  - apply grp_pullback_pr1.
  - reflexivity.
  - apply pullback_commsq.
Defined.

(** Any map [f : E -> F] of short exact sequences factors (uniquely) through [abses_pullback F f3]. *)
Definition abses_pullback_morphism_corec {A B X Y : AbGroup}
           {E : AbSES B A} {F : AbSES Y X} (f : AbSESMorphism E F)
  : AbSESMorphism E (abses_pullback0 (component3 f) F).
Proof.
  snrapply (Build_AbSESMorphism (component1 f) _ grp_homo_id).
  - apply (grp_pullback_corec (projection F) (component3 f)
                              (component2 f) (projection E)).
    apply right_square.
  - intro x; cbn.
    snrapply path_sigma; cbn.
    + apply left_square.
    + refine (transport_sigma' _ _ @ _); cbn.
      apply path_sigma_hprop; cbn; symmetry.
      apply iscomplex_abses.
  - reflexivity.
Defined.

(** The original map factors via the induced map. *)
Definition abses_pullback_morphism_corec_beta `{Funext} {A B X Y : AbGroup}
           {E : AbSES B A} {F : AbSES Y X} (f : AbSESMorphism E F)
  : f = absesmorphism_compose (abses_pullback_morphism F (component3 f))
                              (abses_pullback_morphism_corec f).
Proof.
  apply (equiv_ap issig_AbSESMorphism^-1 _ _).
  srapply path_sigma_hprop.
  1: apply path_prod.
  1: apply path_prod.
  all: by apply equiv_path_grouphomomorphism.
Defined.

Definition abses_component1_trivial_pullback' `{Funext} {A B B' : AbGroup}
           {E : AbSES B A} {F : AbSES B' A} (f : AbSESMorphism E F)
           (h : component1 f == grp_homo_id)
  : E $== abses_pullback0 (component3 f) F.
Proof.
  pose (g := (abses_pullback_morphism_corec f)).
  rapply equiv_path_abses_data.
  exists (component2 g); split.
  - intro a; cbn.
    apply equiv_path_pullback_hset; split; cbn.
    + exact ((left_square f a)^ @ ap _ (h a)).
    + apply iscomplex_abses.
  - reflexivity.
Defined.

(** In particular, if [component1] of a morphism is the identity, then it exhibits the domain as the pullback of the codomain. *)
Definition abses_component1_trivial_pullback `{Univalence} {A B B' : AbGroup}
           {E : AbSES B A} {F : AbSES B' A}
           (f : AbSESMorphism E F) (h : component1 f == grp_homo_id)
  : E = abses_pullback0 (component3 f) F
  := equiv_path_abses_iso (abses_component1_trivial_pullback' f h).
