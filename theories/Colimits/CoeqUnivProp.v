Require Import Basics.Overture.
Require Import Basics.Tactics.
Require Import Basics.PathGroupoids.
Require Import Types.Paths.
Require Import Colimits.Coeq.
Require Import Cubical.DPath.
Require Import WildCat.Core.
Require Import WildCat.Displayed.
Require Import WildCat.Equiv.
Require Import WildCat.EquivGpd.
Require Import WildCat.Forall.
Require Import WildCat.Paths.
Require Import WildCat.ZeroGroupoid.

(** Using wild 0-groupoids, the universal property can be proven without funext.  A simple equivalence of 0-groupoids between [Coeq f g -> P] and [{ h : A -> P & h o f == h o g }] would not carry all the higher-dimensional information, but if we generalize it to dependent functions, then it does suffice. *)
Section UnivProp.
  Context {B A : Type} (f g : B -> A) (P : Coeq f g -> Type).

  (** The domain of the equivalence is the fully-applied type of [Coeq_ind]: sections of [P] over [Coeq f g] *)
  Definition Coeq_ind_type := forall z : Coeq f g, P z.

  Local Instance isgraph_Coeq_ind_type : IsGraph Coeq_ind_type.
  Proof.
    apply isgraph_forall; intros; apply isgraph_paths.
  Defined.

  Local Instance is01cat_Coeq_ind_type: Is01Cat Coeq_ind_type.
  Proof.
    apply is01cat_forall; intros; apply is01cat_paths.
  Defined.

  Local Instance is0gpd_Coeq_ind_type: Is0Gpd Coeq_ind_type.
  Proof.
    apply is0gpd_forall; intros; apply is0gpd_paths.
  Defined.

  Definition Coeq_ind_map := forall a : A, P (coeq a).

  Local Instance isgraph_Coeq_ind_map : IsGraph Coeq_ind_map.
  Proof.
    apply isgraph_forall. intros; apply isgraph_paths.
  Defined.

  Local Instance is01cat_Coeq_ind_map : Is01Cat Coeq_ind_map.
  Proof.
    apply is01cat_forall; intros; apply is01cat_paths.
  Defined.

  Local Instance is0gpd_Coeq_ind_map : Is0Gpd Coeq_ind_map.
  Proof.
    apply is0gpd_forall; intros; apply is0gpd_paths.
  Defined.

  (** The codomain of the equivalence is a sigma-groupoid of this family. *)
  Definition Coeq_ind_data' (h : Coeq_ind_map)
    := forall b : B, DPath P (cglue b) (h (f b)) (h (g b)).

  (** We consider [Coeq_ind_data'] to be a displayed 0-groupoid over [Coeq_ind_map], where objects over [h : forall a : A, P (coeq a)] are homotopies [h o f == h o g] and morphisms over [p : h == k] are witnesses that p commutes with the homotopies over [h] and [k]. *)
  Local Instance isdgraph_Coeq_ind_data' : IsDGraph Coeq_ind_data'.
  Proof.
    intros h k p r s.
    exact (forall b, ap (transport P (cglue b)) (p (f b)) @ s b = r b @ p (g b)).
  Defined.

  Local Instance isd01cat_Coeq_ind_data' : IsD01Cat Coeq_ind_data'.
  Proof.
    nrapply Build_IsD01Cat.
    - intros h h' b; exact (concat_1p_p1 _).
    - intros h k j p q h' k' j' p' q' b.
      lhs nrapply ap_pp_p.
      lhs nrapply (whiskerL _ (p' b)).
      lhs nrapply concat_p_pp.
      lhs nrapply (whiskerR (q' b)).
      nrapply concat_pp_p.
  Defined.

  Local Instance isd0gpd_Coeq_ind_data' : IsD0Gpd Coeq_ind_data'.
  Proof.
    intros h k p r s p' b.
    lhs nrapply (whiskerR (ap_V _ _)).
    nrapply moveL_pV.
    lhs nrapply concat_pp_p.
    lhs nrapply (whiskerL _ (p' b)^).
    lhs nrapply concat_p_pp.
    lhs nrapply (whiskerR (concat_Vp _)).
    nrapply concat_1p.
  Defined.

  (** The codomain of the equivalence, consisting of input data for [Coeq_ind]. *)
  Definition Coeq_ind_data := sig Coeq_ind_data'.

  Local Instance isgraph_Coeq_ind_data : IsGraph Coeq_ind_data.
  Proof.
    rapply isgraph_total.
  Defined.

  Local Instance is01cat_Coeq_ind_data : Is01Cat Coeq_ind_data.
  Proof.
    rapply is01cat_total.
  Defined.

  Local Instance is0gpd_Coeq_ind_data : Is0Gpd Coeq_ind_data.
  Proof.
    rapply is0gpd_total.
  Defined.

  Definition Coeq_ind_inv : Coeq_ind_type -> Coeq_ind_data.
  Proof.
    intros h.
    exists (h o coeq).
    intros b.
    exact (apD h (cglue b)).
  Defined.

  Local Instance is0functor_Coeq_ind_inv : Is0Functor Coeq_ind_inv.
  Proof.
    nrapply Build_Is0Functor.
    intros h k p.
    exists (p o coeq).
    intros b.
    nrapply moveL_pM.
    exact ((apD_homotopic p (cglue b))^).
  Defined.

  Local Instance issurjinj_Coeq_ind_inv : IsSurjInj Coeq_ind_inv.
  Proof.
    nrapply Build_IsSurjInj.
    - intros [h r].
      exists (Coeq_ind P h r).
      exists (fun a => idpath).
      intros b.
      nrefine (concat_1p _ @ _ @ (concat_p1 _)^).
      symmetry.
      nrapply Coeq_ind_beta_cglue.
    - intros h k [p p'].
      snrapply Coeq_ind.
      1: exact p.
      intros b; specialize (p' b).
      lhs nrapply transport_paths_FlFr_D.
      lhs nrapply concat_pp_p.
      lhs nrapply (whiskerL _ p').
      lhs nrapply concat_p_pp.
      lhs nrapply (whiskerR (concat_Vp _)).
      nrapply concat_1p.
  Defined.

  Definition equiv_0gpd_Coeq_ind
    : Build_ZeroGpd Coeq_ind_type _ _ _ $<~> Build_ZeroGpd Coeq_ind_data _ _ _.
  Proof.
    snrapply Build_CatEquiv.
    1: rapply Build_Morphism_0Gpd.
    rapply isequiv_0gpd_issurjinj.
  Defined.

End UnivProp.
