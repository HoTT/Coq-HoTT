Require Import WildCat.
Require Import Spaces.Nat.Core.
(* Some of the material in abstract_algebra and canonical names could be selectively exported to the user, as is done in Groups/Group.v. *)
Require Import Classes.interfaces.canonical_names.
Require Import Algebra.Groups.Kernel Algebra.Groups.Image Algebra.Groups.QuotientGroup.
Require Import Algebra.AbGroups.AbelianGroup Algebra.AbGroups.Biproduct.
Require Import Rings.Ring.

Declare Scope module_scope.

(** * Left modules over a ring. *)

(** TODO: Right modules? We can treat right modules as left modules over the opposite ring. *)

(** ** Definition *)

(** An abelian group [M] is a left [R]-module when equipped with the following data: *) 
Class IsLeftModule (R : Ring) (M : AbGroup) := {
  (** A function [lact] (left-action) that takes an element [r : R] and an element [m : M] and returns an element [lact r m : M]. *)
  lact : R -> M -> M;
  (** Actions distribute on the left over addition in the abelian group. That is [lact r (m + n) = lact r m + lact r n]. *)
  lact_left_dist :: LeftHeteroDistribute lact (+) (+);
  (** Actions distribute on the right over addition in the ring. That is [lact (r + s) m = lact r m + lact s m]. *)
  lact_right_dist :: RightHeteroDistribute lact (+) (+);
  (** Actions are associative. That is [lact (r * s) m = lact r (lact s m)]. *)
  lact_assoc :: HeteroAssociative lact lact lact (.*.);
  (** Actions preserve the multiplicative identity. That is [lact 1 m = m]. *)
  lact_unit :: LeftIdentity lact 1;
}.

(** TODO: notation for action. *)

(** A left R-module is an abelian group equipped with a left R-module structure. *)
Record LeftModule (R : Ring) := {
  lm_carrier :> AbGroup;
  lm_lact :: IsLeftModule R lm_carrier;
}.

Section ModuleAxioms.
  Context {R : Ring} {M : LeftModule R} (r s : R) (m n : M).
  (** Here we state the module axioms in a readable form for direct use. *)

  Definition lm_dist_l : lact r (m + n) = lact r m + lact r n := lact_left_dist r m n.
  Definition lm_dist_r : lact (r + s) m = lact r m + lact s m := lact_right_dist r s m.
  Definition lm_assoc : lact r (lact s m) = lact (r * s) m := lact_assoc r s m.
  Definition lm_unit : lact 1 m = m := lact_unit m.
  
End ModuleAxioms.

(** ** Facts about left modules *)

Section ModuleFacts.
  Context {R : Ring} {M : LeftModule R} (r : R) (m : M).
  
  (** Here are some quick facts that hold in modules. *) 

  (** The action of zero is zero. *) 
  Definition lm_zero_l : lact 0 m = 0.
  Proof.
    apply (grp_cancelL1 (z := lact 0 m)).
    lhs_V nrapply lm_dist_r.
    f_ap.
    apply rng_plus_zero_r.
  Defined.
  
  (** The action on zero is zero. *)
  Definition lm_zero_r : lact r (0 : M) = 0.
  Proof.
    apply (grp_cancelL1 (z := lact r 0)).
    lhs_V nrapply lm_dist_l.
    f_ap.
    apply grp_unit_l.
  Defined.

  (** The action of [-1] is the additive inverse. *)
  Definition lm_minus_one : lact (-1) m = -m.
  Proof.
     apply grp_moveL_1V.
     lhs nrapply (ap (_ +) (lm_unit m)^).
     lhs_V nrapply lm_dist_r.
     rhs_V nrapply lm_zero_l.
     f_ap.
     apply grp_inv_l.
  Defined.

End ModuleFacts.

(** ** Left Submodules *)

(** A subgroup of a left R-module is a left submodule if it is closed under the action of R. *)
Class IsLeftSubmodule {R : Ring} {M : LeftModule R} (N : M -> Type) := {
  ils_issubgroup :: IsSubgroup N;
  is_left_submodule : forall r m, N m -> N (lact r m);
}.

(** A left submodule is a subgroup of the abelian group closed under the action of R. *)
Record LeftSubmodule {R : Ring} (M : LeftModule R) := {
  lsm_carrier :> M -> Type;
  lsm_submodule :: IsLeftSubmodule lsm_carrier;
}.

Definition subgroup_leftsubmodule {R : Ring} {M : LeftModule R}
  : LeftSubmodule M -> Subgroup M
  := fun N => Build_Subgroup M N _.
Coercion subgroup_leftsubmodule : LeftSubmodule >-> Subgroup.

(** Submodules inherit the R-module structure of their parent. *)
Global Instance isleftmodule_leftsubmodule {R : Ring}
  {M : LeftModule R} (N : LeftSubmodule M)
  : IsLeftModule R N.
Proof.
  snrapply Build_IsLeftModule.
  - intros r [n n_in_N].
    exists (lact r n).
    by apply lsm_submodule.
  - intros r [n] [m]; apply path_sigma_hprop.
    apply lact_left_dist.
  - intros r s [n]; apply path_sigma_hprop.
    apply lact_right_dist.
  - intros r s [n]; apply path_sigma_hprop.
    apply lact_assoc.
  - intros [n]; apply path_sigma_hprop.
    apply lact_unit.
Defined.

(** Any left submodule of a left R-module is a left R-module. *)
Definition leftmodule_leftsubmodule {R : Ring}
  {M : LeftModule R} (N : LeftSubmodule M)
  : LeftModule R
  := Build_LeftModule R N _.
Coercion leftmodule_leftsubmodule : LeftSubmodule >-> LeftModule.

(** The submodule criterion. This is a convenient way to build submodules. *)
Definition Build_IsLeftSubmodule' {R : Ring} {M : LeftModule R} 
  (H : M -> Type) `{forall x, IsHProp (H x)}
  (z : H zero)
  (c : forall r n m, H n -> H m -> H (n + lact r m))
  : IsLeftSubmodule H.
Proof.
  snrapply Build_IsLeftSubmodule.
  - snrapply Build_IsSubgroup'.
    + exact _.
    + exact z.
    + intros x y hx hy.
      change (sg_op ?x ?y) with (x + y).
      pose proof (p := c (-1) x y hx hy).
      rewrite lm_minus_one in p.
      exact p.
  - intros r m hm.
    rewrite <- (grp_unit_l).
    by apply c.
Defined.

Definition Build_LeftSubmodule' {R : Ring} {M : LeftModule R}
  (H : M -> Type) `{forall x, IsHProp (H x)}
  (z : H zero)
  (c : forall r n m, H n -> H m -> H (n + lact r m))
  : LeftSubmodule M.
Proof.
  pose (p := Build_IsLeftSubmodule' H z c).
  snrapply Build_LeftSubmodule.
  1: snrapply (Build_Subgroup _ H).
  2: exact p.
  rapply ils_issubgroup.
Defined.

(** ** Left R-module homomorphisms *)

(** A left module homomorphism is a group homomorphism that commutes with the action of R. *)
Record LeftModuleHomomorphism {R : Ring} (M N : LeftModule R) := {
  lm_homo_map :> GroupHomomorphism M N;
  lm_homo_lact : forall r m, lm_homo_map (lact r m) = lact r (lm_homo_map m);
}.

Definition lm_homo_id {R : Ring} (M : LeftModule R) : LeftModuleHomomorphism M M.
Proof.
  snrapply Build_LeftModuleHomomorphism.
  - exact grp_homo_id.
  - reflexivity.
Defined.

Definition lm_homo_compose {R : Ring} {M N L : LeftModule R}
  : LeftModuleHomomorphism N L -> LeftModuleHomomorphism M N
  -> LeftModuleHomomorphism M L.
Proof.
  intros f g.
  snrapply Build_LeftModuleHomomorphism.
  - exact (grp_homo_compose f g).
  - intros r m.
    rhs_V nrapply lm_homo_lact.
    apply (ap f).
    apply lm_homo_lact.
Defined.

(** Smart constructor for building left module homomorphisms from a map. *)
Definition Build_LeftModuleHomomorphism' {R : Ring} {M N : LeftModule R}
  (f : M -> N) (p : forall r x y, f (lact r x + y) = lact r (f x) + f y)
  : LeftModuleHomomorphism M N.
Proof.
  snrapply Build_LeftModuleHomomorphism.
  - snrapply Build_GroupHomomorphism.
    + exact f.
    + intros x y.
      rewrite <- (lm_unit (f x)).
      set (lact 1 (f x)).
      rewrite <- (lm_unit x).
      apply p.
  - intros r m.
    simpl.
    rewrite <- (grp_unit_r (lact r m)).
    rewrite p.
    rhs_V nrapply grp_unit_r.
    apply grp_cancelL.
    specialize (p 1 0 0).
    rewrite 2 lm_unit in p.
    apply (grp_cancelL1 (z := f 0)).
    lhs_V nrapply p.
    apply ap.
    apply grp_unit_l.
Defined.

Record LeftModuleIsomorphism {R : Ring} (M N : LeftModule R) := {
  lm_iso_map :> LeftModuleHomomorphism M N;
  isequiv_lm_iso_map :: IsEquiv lm_iso_map;
}.

Definition Build_LeftModuleIsomorphism' {R : Ring} (M N : LeftModule R)
  (f : GroupIsomorphism M N) (p : forall r x, f (lact r x) = lact r (f x))
  : LeftModuleIsomorphism M N.
Proof.
  snrapply Build_LeftModuleIsomorphism.
  - snrapply Build_LeftModuleHomomorphism.
    + exact f.
    + exact p.
  - exact _.
Defined.

Definition lm_iso_inverse {R : Ring} {M N : LeftModule R}
  : LeftModuleIsomorphism M N -> LeftModuleIsomorphism N M.
Proof.
  intros f.
  snrapply Build_LeftModuleIsomorphism.
  - snrapply Build_LeftModuleHomomorphism'.
    + exact f^-1.
    + intros r m n.
      apply moveR_equiv_V. 
      rhs nrapply grp_homo_op.
      symmetry.
      f_ap.
      2: apply eisretr.
      lhs nrapply lm_homo_lact.
      apply ap.
      apply eisretr.
  - exact _.
Defined.

(** ** Category of left R-modules *)

(** TODO: define as a displayed category over Ring *)

Global Instance isgraph_leftmodule {R : Ring} : IsGraph (LeftModule R)
  := Build_IsGraph _ LeftModuleHomomorphism.

Global Instance is01cat_leftmodule {R : Ring} : Is01Cat (LeftModule R)
  := Build_Is01Cat _ _ lm_homo_id (@lm_homo_compose R).

Global Instance is2graph_leftmodule {R : Ring} : Is2Graph (LeftModule R)
  := fun M N => isgraph_induced (@lm_homo_map R M N).

Global Instance is1cat_leftmodule {R : Ring} : Is1Cat (LeftModule R).
Proof.
  snrapply Build_Is1Cat.
  - intros M N; rapply is01cat_induced.
  - intros M N; rapply is0gpd_induced.
  - intros M N L h.
    snrapply Build_Is0Functor.
    intros f g p m.
    exact (ap h (p m)).
  - intros M N L f.
    snrapply Build_Is0Functor.
    intros g h p m.
    exact (p (f m)).
  - simpl; reflexivity.
  - simpl; reflexivity.
  - simpl; reflexivity.
Defined.

Global Instance hasequivs_leftmodule {R : Ring} : HasEquivs (LeftModule R).
Proof.
  snrapply Build_HasEquivs.
  - exact LeftModuleIsomorphism.
  - intros M N; exact IsEquiv.
  - intros M N f; exact f.
  - simpl; exact _.
  - apply Build_LeftModuleIsomorphism.
  - reflexivity.
  - intros M N; apply lm_iso_inverse.
  - intros M N f; apply eissect.
  - intros M N f; apply eisretr.
  - intros M N f g fg gf.
    exact (isequiv_adjointify f g fg gf).
Defined.

(** ** Kernel of module homomorphism *)

Global Instance isleftsubmodule_grp_kernel {R : Ring}
  {M N : LeftModule R} (f : M $-> N)
  : IsLeftSubmodule (grp_kernel f).
Proof.
  srapply Build_IsLeftSubmodule.
  intros r m n.
  lhs nrapply lm_homo_lact.
  rhs_V nrapply (lm_zero_r r).
  apply ap.
  exact n.
Defined.

Definition lm_kernel {R : Ring} {M N : LeftModule R} (f : M $-> N)
  : LeftSubmodule M
  := Build_LeftSubmodule _ _ (grp_kernel f) _.

(** ** Image of module homomorphism *)

Global Instance isleftsubmodule_grp_image {R : Ring}
  {M N : LeftModule R} (f : M $-> N)
  : IsLeftSubmodule (grp_image f).
Proof.
  srapply Build_IsLeftSubmodule.
  intros r m; apply Trunc_functor; intros [n p].
  exists (lact r n).
  lhs nrapply lm_homo_lact.
  apply ap.
  exact p.
Defined.

Definition lm_image {R : Ring} {M N : LeftModule R} (f : M $-> N)
  : LeftSubmodule N
  := Build_LeftSubmodule _ _ (grp_image f) _.

(** ** Quotient Modules *)

(** The quotient abelian group of a module and a submodule has a natural ring action. *)
Global Instance isleftmodule_quotientabgroup {R : Ring}
  (M : LeftModule R) (N : LeftSubmodule M)
  : IsLeftModule R (QuotientAbGroup M N).
Proof.
  snrapply Build_IsLeftModule.
  - intros r.
    snrapply quotient_abgroup_rec.
    + refine (grp_quotient_map $o _). 
      snrapply Build_GroupHomomorphism.
      * exact (lact r).
      * intros x y.
        apply lm_dist_l.
    + intros n Nn; simpl.
      apply qglue.
      apply issubgroup_in_inv_op.
      2: apply issubgroup_in_unit.
      by apply is_left_submodule.
  - intros r m n; revert m.
    snrapply Quotient_ind_hprop; [exact _ | intros m; revert n].
    snrapply Quotient_ind_hprop; [exact _ | intros n; simpl].
    rapply ap.
    apply lm_dist_l.
  - intros r s.
    snrapply Quotient_ind_hprop; [exact _| intros m; simpl].
    rapply ap.
    apply lm_dist_r.
  - intros r s.
    snrapply Quotient_ind_hprop; [exact _| intros m; simpl].
    rapply ap.
    apply lm_assoc.
  - snrapply Quotient_ind_hprop; [exact _| intros m; simpl].
    rapply ap.
    apply lm_unit.
Defined.

(** We can therefore form the quotient module of a module by its submodule. *)
Definition QuotientLeftModule {R : Ring} (M : LeftModule R) (N : LeftSubmodule M)
  : LeftModule R
  := Build_LeftModule R (QuotientAbGroup M N) _.

Infix "/" := QuotientLeftModule : module_scope.
  
(** ** First Isomorphism Theorem *)

Local Open Scope module_scope.
Local Open Scope wc_iso_scope.

Definition rng_first_iso `{Funext} {R : Ring} {M N : LeftModule R} (f : M $-> N)
  : M / lm_kernel f ≅ lm_image f.
Proof.
  snrapply Build_LeftModuleIsomorphism'.
  1: rapply abgroup_first_iso.
  intros r.
  srapply Quotient_ind_hprop; intros m.
  apply path_sigma_hprop; simpl.
  apply lm_homo_lact.
Defined.

(** ** Direct products *)

(** TODO: generalise to biproducts *)
(** The direct product of modules *)
Definition lm_prod {R : Ring} : LeftModule R -> LeftModule R -> LeftModule R.
Proof.
  intros M N.
  snrapply (Build_LeftModule R (ab_biprod M N)).
  snrapply Build_IsLeftModule.
  - intros r.
    apply functor_prod; exact (lact r).
  - intros r m n.
    apply path_prod; apply lm_dist_l.
  - intros r m n.
    apply path_prod; apply lm_dist_r.
  - intros r s m.
    apply path_prod; apply lm_assoc.
  - intros r.
    apply path_prod; apply lm_unit.
Defined.

Definition lm_prod_fst {R : Ring} {M N : LeftModule R} : lm_prod M N $-> M.
Proof.
  snrapply Build_LeftModuleHomomorphism.
  - apply grp_prod_pr1.
  - reflexivity.
Defined.

Definition lm_prod_snd {R : Ring} {M N : LeftModule R} : lm_prod M N $-> N.
Proof.
  snrapply Build_LeftModuleHomomorphism.
  - apply grp_prod_pr2.
  - reflexivity.
Defined.

Definition lm_prod_corec {R : Ring} {M N : LeftModule R} (L : LeftModule R)
  (f : L $-> M) (g : L $-> N)
  : L $-> lm_prod M N.
Proof.
  snrapply Build_LeftModuleHomomorphism.
  - apply (grp_prod_corec f g).
  - intros r l.
    apply path_prod; apply lm_homo_lact.
Defined.

Global Instance hasbinaryproducts_leftmodule {R : Ring}
  : HasBinaryProducts (LeftModule R).
Proof.
  intros M N.
  snrapply Build_BinaryProduct.
  - exact (lm_prod M N).
  - exact lm_prod_fst.
  - exact lm_prod_snd.
  - exact lm_prod_corec.
  - cbn; reflexivity.
  - cbn; reflexivity.
  - intros L f g p q a.
    exact (path_prod' (p a) (q a)).
Defined.
