From HoTT Require Import Basics Types.
Require Import Universes.HSet.
Require Import Truncations.Core Connectedness SeparatedTrunc.
Require Import Algebra.Groups.Group Subgroup Algebra.AbGroups.Centralizer.
Require Import Pointed WildCat WildCat.Core.
Require Import Homotopy.ClassifyingSpace.Core.
Require Import Colimits.Quotient GraphQuotient.
Require Import Cubical.PathSquare.
Require Import Homotopy.HomotopyGroup.
Export Homotopy.ClassifyingSpace.Core.ClassifyingSpaceNotation.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** * Mapping spaces between classifying spaces *)

(** The type of pointed maps [B G ->* B H] is known to be equivalent to the set [G $-> H]. In this file, we compute [Pi 0] and [Pi 1] of the general function type [B G -> B H]. *)

(** ** Connected components of [B G -> B H] *)

(** The set of representations is the set of conjugacy classes of group homomorphisms. *)
Definition groupreps (G H : Group) : Type
  := @Quotient (G $-> H) (conj_grp_homo).

(** We show that the set of connected components of [B G -> B H] is in bijection with [groupreps G H]. *)

(** [fmap B] sends conjugation to the identity map. Therefore, it induces a map [groupreps G H -> Trunc 0 (B G -> B H)]. *)
Definition idmap_fmap_grp_conj {G : Group} (g : G)
  : fmap B (grp_conj g) == idmap.
Proof.
  srapply ClassifyingSpace_ind_hset.
  - cbn. exact (bloop g).
  - intro x.
    rapply equiv_sq_dp^-1.
    snapply equiv_sq_path.
    rewrite ClassifyingSpace_rec_beta_bloop.
    rhs_V rapply bloop_pp.
    rewrite ap_idmap.
    lhs_V rapply bloop_pp.
    symmetry; exact (ap bloop (grp_inv_gV_g _ g)).
Defined.

Definition groupreps_to_pi0_map_bg `{ua : Univalence} (G H : Group)
  : groupreps G H -> Trunc 0 (B G -> B H).
Proof.
  srefine (Quotient_rec _ _ _ _); cbn beta.
  - intro f.
    apply tr.
    exact (fmap B f).
  - intros a b hr.
    strip_truncations; destruct hr as [h r].
    apply ap.
    apply path_forall.
    lhs' exact (fmap2 (g:=grp_conj h $o b) B r).
    lhs' exact (fmap_comp B b (grp_conj h)).
    intro x.
    exact (idmap_fmap_grp_conj h _).
Defined.

(** We first show that [groupreps_to_pi0_map_bg] is an embedding. *)
Definition isemb_groupreps_to_pi0_map_bg `{ua : Univalence} {G H : Group}
  : IsEmbedding (groupreps_to_pi0_map_bg G H).
Proof.
  apply isembedding_isinj_hset.
  rapply Quotient_ind2_hprop.
  intros u v p.
  srapply path_quotient.
  apply (equiv_path_Tr _ _)^-1 in p.
  strip_truncations; apply tr.
  pose (h := equiv_g_loops_bg^-1 (ap10 p bbase)).
  exists h.
  intro x.
  simpl.
  apply (equiv_inj equiv_g_loops_bg).
  simpl.
  rewrite 2 bloop_pp.
  rewrite bloop_inv.
  (* [h] is defined by applying [equiv_g_loops_bg^-1] and [bloop] is the inverse of that function. *)
  rewrite eisretr.
  rewrite <- 2 ap_fmap_b_beta_bloop.
  exact (ap_homotopic (ap10 p) (bloop x)).
Defined.

(** When [Y] is connected, every function [X -> Y] is merely pointed, so [pointed_fun] is a surjection. *)
Instance issurj_pointed_fun_conn `{Univalence} {X Y : pType} `{IsConnected 0 Y}
  : IsSurjection (pointed_fun : (X ->* Y) -> (X -> Y)).
Proof.
  apply (cancelR_issurjection (issig_pmap X Y)); cbn.
  rapply conn_map_pr1.
Defined.

(** It follows that [groupreps_to_pi0_map_bg] is surjective.  By definition, we have a commutative diagram
<<
               fmap B             pointed_fun
        G $-> H   <~>   (BG ->* BH)  ---------->  (BG -> BH)
           |                                      |
  class_of |                                      | tr
           v                                      v
        groupreps G H ------------------> Tr 0 (BG -> BH)
                     groupreps_to_pi0_map_bg
>>
    To show that [groupreps_to_pi0_map_bg] is surjective, it suffices to show that this is true after precomposition with [class_of] and so we just need to show that the other three maps are surjective.  Rocq can prove these by typeclass search, with one hint for [tr]. *)
Definition issurj_groupreps_to_pi0_map_bg `{ua : Univalence} {G H : Group}
  : IsSurjection (groupreps_to_pi0_map_bg G H).
Proof.
  apply (cancelR_issurjection (class_of _)).
  change (IsConnMap (Tr (-1)) (tr (n:=0) o pointed_fun o fmap (a:=G) (b:=H) B)).
  pose (@isconnmap_pred' 0). (* [tr] is in fact 0-connected, so we give this hint. *)
  exact _.
Defined.

Instance isequiv_groupreps_to_pi0_map_bg `{ua : Univalence} (G H : Group)
  : IsEquiv (groupreps_to_pi0_map_bg G H).
Proof.
  apply isequiv_surj_emb.
  - exact issurj_groupreps_to_pi0_map_bg.
  - exact isemb_groupreps_to_pi0_map_bg.
Defined.

Definition equiv_groupreps_to_pi0_map_bg `{ua : Univalence} (G H : Group)
  : (groupreps G H) <~> Pi 0 [B G -> B H, fun x => bbase]
  := Build_Equiv _ _ _ (isequiv_groupreps_to_pi0_map_bg G H).

(** ** The fundamental group of [B G -> B H] *)

(** We show that [Pi 1 [B G -> B H, fmap B v]] is equivalent to the centralizer of the image of [v]. *)

(** The map in one direction is induced by [fmap11_B] applied to the subgroup inclusion and [v]. *)
Definition b_centralizer_grp_image_to_map_bg {G H : Group} (v : G $-> H)
  : B (subtype_centralizer_subgroup (grp_image v)) -> (B G -> B H).
Proof.
  napply (fmap11_B (subgroup_incl _) v).
  intros [h ch] g; cbn.
  symmetry.
  strip_truncations.
  exact (ch (v g) (tr (g; idpath))).
Defined.

Definition centralizer_grp_image_to_loops_map_bg {G H : Group} (v : G $-> H)
  : subtype_centralizer_subgroup (grp_image v)
      -> loops [B G -> B H, fmap B v]
  := fun x => ap (b_centralizer_grp_image_to_map_bg v) (bloop x).

Definition centralizer_grp_image_to_pi1_map_bg {G H : Group} (v : G $-> H)
  : subtype_centralizer_subgroup (grp_image v)
      -> Pi 1 [B G -> B H, fmap B v]
  := tr o (centralizer_grp_image_to_loops_map_bg v).

(** We now define the inverse. *)
Definition pi1_map_bg_to_centralizer_group_image `{ua : Univalence}
  {G H : Group} (v : G $-> H)
  : Pi 1 [B G -> B H, fmap B v]
    $-> subtype_centralizer_subgroup (grp_image v).
Proof.
  (* It's enough to define a group homomorphism to [H] whose image is in the centralizer. *)
  snapply subgroup_corec.
  - refine (_^-1$ $o _).
    (* For the homomorphism to [H], it's enough to define a homomorphism to [LoopGroup (B H)]. *)
    1: exact grp_iso_g_loopgroup_bg.
    (* And for that, [ap10] does the trick. *)
    snapply Build_GroupHomomorphism.
    + intro p.
      strip_truncations; change (pointed_fun (fmap B v) = (fmap B v)) in p.
      exact (ap10 p bbase).
    + intros p q.
      strip_truncations; change (pointed_fun (fmap B v) = fmap B v) in p, q.
      cbn.
      exact (ap10_pp p q bbase).
  (* Now we need to show that the image of our homomorphism is in the centralizer. *)
  - intro p.
    strip_truncations; change (pointed_fun (fmap B v) = (fmap B v)) in p.
    cbn.
    apply tr.
    intros h sh.
    snapply (centralizer_iso grp_iso_g_loopgroup_bg); cbn.
    rewrite (eisretr bloop).
    strip_truncations.
    destruct sh as [g []]; clear h.
    rewrite <- ap_fmap_b_beta_bloop.
    unfold centralizer.
    cbn; napply concat_Ap.
Defined.

Instance isequiv_pi1_map_bg_to_centralizer_group_image `{ua : Univalence}
  {G H : Group} (v : G $-> H)
  : IsEquiv (pi1_map_bg_to_centralizer_group_image v).
Proof.
  srapply isequiv_adjointify.
  - exact (centralizer_grp_image_to_pi1_map_bg v).
  - intros [h ch]; strip_truncations.
    apply path_sigma_hprop; cbn.
    apply moveR_equiv_V.
    napply ClassifyingSpace_rec2_beta_bloop1_bbase.
  - intro u.
    strip_truncations.
    change (pointed_fun (fmap B v) = (fmap B v)) in u.
    unfold centralizer_grp_image_to_pi1_map_bg.
    apply ap.
    unfold centralizer_grp_image_to_loops_map_bg.
    apply (equiv_inj ap10).
    apply path_forall.
    rapply ClassifyingSpace_ind_hprop.
    lhs napply ClassifyingSpace_rec2_beta_bloop1_bbase.
    cbn.
    apply eisretr.
Defined.

Definition equiv_pi1_map_bg_to_centralizer_group_image `{ua : Univalence}
  {G H : Group} (v : G $-> H)
  : GroupIsomorphism
    (Pi 1 [B G -> B H, fmap B v])
    (subtype_centralizer_subgroup (grp_image v))
  := Build_GroupIsomorphism _ _ _ (isequiv_pi1_map_bg_to_centralizer_group_image v).

(** As a corollary, we can compute the homotopy groups of any function type of the form [X -> B G], where [X] is a pointed connected type. *)

Definition pi0_map_bg_groupreps_pi1 `{Univalence}
  (X : pType) (G : Group) `{IsConnected 0 X}
  : groupreps (Pi 1 X) G <~> Tr 0 (X -> B G).
Proof.
  refine (Trunc_functor_equiv 0 (equiv_map_bg X G) oE _).
  srapply equiv_groupreps_to_pi0_map_bg.
Defined.

Definition pi1_map_bg_groupreps_pi1 `{Univalence}
  (X : pType) (G : Group) `{IsConnected 0 X} (v : Pi 1 X $-> G)
  : GroupIsomorphism
      (Pi 1 [X -> B G, equiv_bg_pi1_adjoint X G v])
      (subtype_centralizer_subgroup (grp_image v)).
Proof.
  refine (grp_iso_compose (equiv_pi1_map_bg_to_centralizer_group_image v) _).
  srapply groupiso_pi_functor.
  symmetry.
  srapply Build_pEquiv'.
  - exact (equiv_map_bg X G).
  - unfold "pt".
    unfold ispointed_type.
    reflexivity.
Defined.
