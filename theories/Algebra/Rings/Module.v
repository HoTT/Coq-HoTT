From HoTT.WildCat Require Import Core Equiv Induced Products.
Require Import Spaces.Nat.Core.
(* Some of the material in abstract_algebra and canonical names could be selectively exported to the user, as is done in Groups/Group.v. *)
Require Import Classes.interfaces.canonical_names.
Require Import Algebra.Groups.QuotientGroup.
Require Import Algebra.AbGroups.AbelianGroup Algebra.AbGroups.Biproduct.
Require Import Rings.Ring.

Declare Scope module_scope.
Local Open Scope module_scope.

(** * Modules over a ring. *)

(** ** Left Modules *)

(** An abelian group [M] is a left [R]-module when equipped with the following data: *) 
Class IsLeftModule (R : Ring) (M : AbGroup) := {
  (** A function [lact] (left-action) that takes an element [r : R] and an element [m : M] and returns an element [lact r m : M], which we also denote [r *L m]. *)
  lact : R -> M -> M;
  (** Actions distribute on the left over addition in the abelian group. That is [r *L (m + n) = r *L m + r *L n]. *)
  lact_left_dist :: LeftHeteroDistribute lact (+) (+);
  (** Actions distribute on the right over addition in the ring. That is [(r + s) *L m = r *L m + s *L m]. *)
  lact_right_dist :: RightHeteroDistribute lact (+) (+);
  (** Actions are associative. That is [(r * s) *L m = r *L (s *L m)]. *)
  lact_assoc :: HeteroAssociative lact lact lact (.*.);
  (** Actions preserve the multiplicative identity. That is [1 *L m = m]. *)
  lact_unit :: LeftIdentity lact 1;
}.

Infix "*L" := lact : module_scope.

(** A left R-module is an abelian group equipped with a left R-module structure. *)
Record LeftModule (R : Ring) := {
  lm_carrier :> AbGroup;
  lm_lact :: IsLeftModule R lm_carrier;
}.

Section LeftModuleAxioms.
  Context {R : Ring} {M : LeftModule R} (r s : R) (m n : M).
  (** Here we state the module axioms in a readable form for direct use. *)

  Definition lm_dist_l : r *L (m + n) = r *L m + r *L n := lact_left_dist r m n.
  Definition lm_dist_r : (r + s) *L m = r *L m + s *L m := lact_right_dist r s m.
  Definition lm_assoc : r *L (s *L m) = (r * s) *L m := lact_assoc r s m.
  Definition lm_unit : 1 *L m = m := lact_unit m.
  
End LeftModuleAxioms.

(** ** Facts about left modules *)

Section LeftModuleFacts.
  Context {R : Ring} {M : LeftModule R} (r : R) (m : M).
  
  (** Here are some quick facts that hold in modules. *) 

  (** The left action of zero is zero. *) 
  Definition lm_zero_l : 0 *L m = 0.
  Proof.
    apply (grp_cancelL1 (z := lact 0 m)).
    lhs_V napply lm_dist_r.
    f_ap.
    apply rng_plus_zero_r.
  Defined.
  
  (** The left action on zero is zero. *)
  Definition lm_zero_r : r *L (0 : M) = 0.
  Proof.
    apply (grp_cancelL1 (z := lact r 0)).
    lhs_V napply lm_dist_l.
    f_ap.
    apply grp_unit_l.
  Defined.

  (** The left action of [-1] is the additive inverse. *)
  Definition lm_minus_one : -1 *L m = -m.
  Proof.
     apply grp_moveL_1V.
     lhs napply (ap (_ +) (lm_unit m)^).
     lhs_V napply lm_dist_r.
     rhs_V napply lm_zero_l.
     f_ap.
     apply grp_inv_l.
  Defined.
 
  (** The left action of [r] on the additive inverse of [m] is the additive inverse of the left action of [r] on [m]. *)
  Definition lm_neg : r *L -m = - (r *L m).
  Proof.
    apply grp_moveL_1V.
    lhs_V napply lm_dist_l.
    rhs_V napply lm_zero_r.
    f_ap.
    apply grp_inv_l.
  Defined.

End LeftModuleFacts.

(** Every ring [R] is a left [R]-module over itself. *)
Instance isleftmodule_ring (R : Ring) : IsLeftModule R R.
Proof.
  rapply Build_IsLeftModule.
Defined.

(** ** Right Modules *)

(** An abelian group [M] is a right [R]-module when it is a left [R^op]-module. *)
Class IsRightModule (R : Ring) (M : AbGroup)
  := isleftmodule_op_isrightmodule :: IsLeftModule (rng_op R) M.
  
(** [ract] (right-action) that takes an element [m : M] and an element [r : R] and returns an element [ract m r : M] which we also denote [m *R r]. *)
Definition ract {R : Ring} {M : AbGroup} `{!IsRightModule R M}
  : M -> R -> M
  := fun m r => lact (R:=rng_op R) r m.

Infix "*R" := ract.

(** A right module is a left module over the opposite ring. *)
Definition RightModule (R : Ring) := LeftModule (rng_op R).

(** Right modules are right modules. *)
Instance rm_ract {R : Ring} {M : RightModule R} : IsRightModule R M
  := lm_lact (rng_op R) M.

Section RightModuleAxioms.
  Context {R : Ring} {M : RightModule R} (m n : M) (r s : R).
  (** Here we state the module axioms in a readable form for direct use. *)

  Definition rm_dist_r : (m + n) *R r = m *R r + n *R r
    := lm_dist_l (R:=rng_op R) r m n.
  Definition rm_dist_l : m *R (r + s) = m *R r + m *R s
    := lm_dist_r (R:=rng_op R) r s m.
  Definition rm_assoc : (m *R r) *R s = m *R (r * s)
    := lm_assoc (R:=rng_op R) s r m.
  Definition rm_unit : m *R 1 = m
    := lm_unit (R:=rng_op R) m.
  
End RightModuleAxioms.

(** ** Facts about right modules *)

Section RightModuleFacts.
  Context {R : Ring} {M : RightModule R} (m : M) (r : R).

  (** The right action on zero is zero. *)
  Definition rm_zero_l : (0 : M) *R r = 0
    := lm_zero_r (R:=rng_op R) r.

  (** The right action of zero is zero. *)
  Definition rm_zero_r : m *R 0 = 0
    := lm_zero_l (R:=rng_op R) m.

  (** The right action of [-1] is the additive inverse. *)
  Definition rm_minus_one : m *R -1 = -m
    := lm_minus_one (R:=rng_op R) m. 

  (** The right action of [r] on the additive inverse of [m] is the additive inverse of the right action of [r] on [m]. *)
  Definition rm_neg : -m *R r = - (m *R r)
    := lm_neg (R:=rng_op R) r m. 

End RightModuleFacts.

(** Every ring [R] is a right [R]-module over itself. *)
Instance isrightmodule_ring (R : Ring) : IsRightModule R R
  := isleftmodule_ring (rng_op R).

(** ** Submodules *)

(** A subgroup of a left R-module is a left submodule if it is closed under the action of R. *)
Class IsLeftSubmodule {R : Ring} {M : LeftModule R} (N : M -> Type) := {
  ils_issubgroup :: IsSubgroup N;
  is_left_submodule : forall r m, N m -> N (r *L m);
}.

(** A subgroup of a right R-module is a right submodule if it is a left submodule over the opposite ring. *)
Class IsRightSubmodule {R : Ring} {M : RightModule R} (N : M -> Type)
  := isleftsubmodule_op_isrightsubmodule :: IsLeftSubmodule (R:=rng_op R) N.

(** A left submodule is a subgroup of the abelian group closed under the left action of R. *)
Record LeftSubmodule {R : Ring} (M : LeftModule R) := {
  lsm_carrier :> M -> Type;
  lsm_submodule :: IsLeftSubmodule lsm_carrier;
}.

(** A right submodule is a subgroup of the abelian group closed under the right action of R. *)
Definition RightSubmodule {R : Ring} (M : RightModule R)
  := LeftSubmodule (R:=rng_op R) M.

Definition subgroup_leftsubmodule {R : Ring} {M : LeftModule R}
  : LeftSubmodule M -> Subgroup M
  := fun N => Build_Subgroup M N _.
Coercion subgroup_leftsubmodule : LeftSubmodule >-> Subgroup.

Definition subgroup_rightsubmodule {R : Ring} {M : RightModule R}
  : RightSubmodule M -> Subgroup M
  := idmap.
Coercion subgroup_rightsubmodule : RightSubmodule >-> Subgroup.

(** Left submodules inherit the left R-module structure of their parent. *)
Instance isleftmodule_leftsubmodule {R : Ring}
  {M : LeftModule R} (N : LeftSubmodule M)
  : IsLeftModule R N.
Proof.
  snapply Build_IsLeftModule.
  - intros r [n n_in_N].
    exists (r *L n).
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

(** Right submodules inherit the right R-module structure of their parent. *)
Instance isrightmodule_rightsubmodule {R : Ring}
  {M : RightModule R} (N : RightSubmodule M)
  : IsRightModule R N
  := isleftmodule_leftsubmodule (R:=rng_op R) N.

(** Any left submodule of a left R-module is a left R-module. *)
Definition leftmodule_leftsubmodule {R : Ring}
  {M : LeftModule R} (N : LeftSubmodule M)
  : LeftModule R
  := Build_LeftModule R N _.
Coercion leftmodule_leftsubmodule : LeftSubmodule >-> LeftModule.

(** Any right submodule of a right R-module is a right R-module. *)
Definition rightmodule_rightsubmodule {R : Ring}
  {M : RightModule R} (N : RightSubmodule M)
  : RightModule R
  := N.
Coercion rightmodule_rightsubmodule : RightSubmodule >-> RightModule.

(** The submodule criterion. This is a convenient way to build submodules. *)
Definition Build_IsLeftSubmodule' {R : Ring} {M : LeftModule R} 
  (H : M -> Type) `{forall x, IsHProp (H x)}
  (z : H zero)
  (c : forall r n m, H n -> H m -> H (n + r *L m))
  : IsLeftSubmodule H.
Proof.
  snapply Build_IsLeftSubmodule.
  - snapply Build_IsSubgroup'.
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

Definition Build_IsRightSubmodule' {R : Ring} {M : RightModule R} 
  (H : M -> Type) `{forall x, IsHProp (H x)}
  (z : H zero)
  (c : forall r n m, H n -> H m -> H (n + ract m r))
  : IsRightSubmodule H
  := Build_IsLeftSubmodule' (R:=rng_op R) H z c.

Definition Build_LeftSubmodule' {R : Ring} {M : LeftModule R}
  (H : M -> Type) `{forall x, IsHProp (H x)}
  (z : H zero)
  (c : forall r n m, H n -> H m -> H (n + r *L m))
  : LeftSubmodule M.
Proof.
  pose (p := Build_IsLeftSubmodule' H z c).
  snapply Build_LeftSubmodule.
  1: snapply (Build_Subgroup _ H).
  2: exact p.
  rapply ils_issubgroup.
Defined.

Definition Build_RightSubmodule {R : Ring} {M : RightModule R}
  (H : M -> Type) `{forall x, IsHProp (H x)}
  (z : H zero)
  (c : forall r n m, H n -> H m -> H (n + m *R r))
  : RightSubmodule M
  := Build_LeftSubmodule' (R:=rng_op R) H z c.

(** ** R-module homomorphisms *)

(** A left module homomorphism is a group homomorphism that commutes with the left action of R. *)
Record LeftModuleHomomorphism {R : Ring} (M N : LeftModule R) := {
  lm_homo_map :> GroupHomomorphism M N;
  lm_homo_lact : forall r m, lm_homo_map (r *L m) = r *L lm_homo_map m;
}.

Definition RightModuleHomomorphism {R : Ring} (M N : RightModule R)
  := LeftModuleHomomorphism (R:=rng_op R) M N.

Definition rm_homo_map {R : Ring} {M N : RightModule R}
  : RightModuleHomomorphism M N -> GroupHomomorphism M N
  := lm_homo_map (R:=rng_op R) M N.
Coercion rm_homo_map : RightModuleHomomorphism >-> GroupHomomorphism.

Definition rm_homo_ract {R : Ring} {M N : RightModule R}
  (f : RightModuleHomomorphism M N)
  : forall m r, f (ract m r) = ract (f m) r
  := fun m r => lm_homo_lact (R:=rng_op R) M N f r m.

Definition lm_homo_id {R : Ring} (M : LeftModule R) : LeftModuleHomomorphism M M.
Proof.
  snapply Build_LeftModuleHomomorphism.
  - exact grp_homo_id.
  - reflexivity.
Defined.

Definition rm_homo_id {R : Ring} (M : RightModule R) : RightModuleHomomorphism M M
  := lm_homo_id (R:=rng_op R) M.

Definition lm_homo_compose {R : Ring} {M N L : LeftModule R}
  : LeftModuleHomomorphism N L -> LeftModuleHomomorphism M N
  -> LeftModuleHomomorphism M L.
Proof.
  intros f g.
  snapply Build_LeftModuleHomomorphism.
  - exact (grp_homo_compose f g).
  - intros r m.
    rhs_V napply lm_homo_lact.
    apply (ap f).
    apply lm_homo_lact.
Defined.

Definition rm_homo_compose {R : Ring} {M N L : RightModule R}
  : RightModuleHomomorphism N L -> RightModuleHomomorphism M N
  -> RightModuleHomomorphism M L
  := lm_homo_compose (R:=rng_op R).

(** Smart constructor for building left module homomorphisms from a map. *)
Definition Build_LeftModuleHomomorphism' {R : Ring} {M N : LeftModule R}
  (f : M -> N) (p : forall r x y, f (r *L x + y) = r *L f x + f y)
  : LeftModuleHomomorphism M N.
Proof.
  snapply Build_LeftModuleHomomorphism.
  - snapply Build_GroupHomomorphism.
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
    rhs_V napply grp_unit_r.
    apply grp_cancelL.
    specialize (p 1 0 0).
    rewrite 2 lm_unit in p.
    apply (grp_cancelL1 (z := f 0)).
    lhs_V napply p.
    apply ap.
    apply grp_unit_l.
Defined.

Definition Build_RightModuleHomomorphism' {R  :Ring} {M N : RightModule R}
  (f : M -> N) (p : forall r x y, f (x *R r + y) = f x *R r + f y)
  : RightModuleHomomorphism M N
  := Build_LeftModuleHomomorphism' (R:=rng_op R) f p.

Record LeftModuleIsomorphism {R : Ring} (M N : LeftModule R) := {
  lm_iso_map :> LeftModuleHomomorphism M N;
  isequiv_lm_iso_map :: IsEquiv lm_iso_map;
}.

Definition RightModuleIsomorphism {R : Ring} (M N : RightModule R)
  := LeftModuleIsomorphism (R:=rng_op R) M N.

Definition Build_LeftModuleIsomorphism' {R : Ring} (M N : LeftModule R)
  (f : GroupIsomorphism M N) (p : forall r x, f (r *L x) = r *L f x)
  : LeftModuleIsomorphism M N.
Proof.
  snapply Build_LeftModuleIsomorphism.
  - snapply Build_LeftModuleHomomorphism.
    + exact f.
    + exact p.
  - exact _.
Defined.

Definition Build_RightModuleIsomorphism' {R : Ring} (M N : RightModule R)
  (f : GroupIsomorphism M N) (p : forall r x, f (ract x r) = ract (f x) r)
  : RightModuleIsomorphism M N
  := Build_LeftModuleIsomorphism' (R:=rng_op R) M N f p.

Definition lm_iso_inverse {R : Ring} {M N : LeftModule R}
  : LeftModuleIsomorphism M N -> LeftModuleIsomorphism N M.
Proof.
  intros f.
  snapply Build_LeftModuleIsomorphism.
  - snapply Build_LeftModuleHomomorphism'.
    + exact f^-1.
    + intros r m n.
      apply moveR_equiv_V. 
      rhs napply grp_homo_op.
      symmetry.
      f_ap.
      2: apply eisretr.
      lhs napply lm_homo_lact.
      apply ap.
      apply eisretr.
  - exact _.
Defined.

Definition rm_iso_inverse {R : Ring} {M N : RightModule R}
  : RightModuleIsomorphism M N -> RightModuleIsomorphism N M
  := lm_iso_inverse (R:=rng_op R).

(** ** Category of left and right R-modules *)

(** TODO: define as a displayed category over Ring *)

(** *** Category of left R-modules *)

Instance isgraph_leftmodule {R : Ring} : IsGraph (LeftModule R)
  := Build_IsGraph _ LeftModuleHomomorphism.

Instance is01cat_leftmodule {R : Ring} : Is01Cat (LeftModule R)
  := Build_Is01Cat _ _ lm_homo_id (@lm_homo_compose R).

Instance is2graph_leftmodule {R : Ring} : Is2Graph (LeftModule R)
  := fun M N => isgraph_induced (@lm_homo_map R M N).

Instance is1cat_leftmodule {R : Ring} : Is1Cat (LeftModule R).
Proof.
  snapply Build_Is1Cat'.
  - intros M N; rapply is01cat_induced.
  - intros M N; rapply is0gpd_induced.
  - intros M N L h.
    snapply Build_Is0Functor.
    intros f g p m.
    exact (ap h (p m)).
  - intros M N L f.
    snapply Build_Is0Functor.
    intros g h p m.
    exact (p (f m)).
  - simpl; reflexivity.
  - simpl; reflexivity.
  - simpl; reflexivity.
Defined.

Instance hasequivs_leftmodule {R : Ring} : HasEquivs (LeftModule R).
Proof.
  snapply Build_HasEquivs.
  - exact LeftModuleIsomorphism.
  - intros M N; exact IsEquiv.
  - intros M N f; exact f.
  - simpl; exact _.
  - apply Build_LeftModuleIsomorphism.
  - reflexivity.
  - intros M N; exact lm_iso_inverse.
  - intros M N f; apply eissect.
  - intros M N f; apply eisretr.
  - intros M N f g fg gf.
    exact (isequiv_adjointify f g fg gf).
Defined.

(** *** Category of right R-modules *)

Instance isgraph_rightmodule {R : Ring} : IsGraph (RightModule R)
  := isgraph_leftmodule (R:=rng_op R).

Instance is01cat_rightmodule {R : Ring} : Is01Cat (RightModule R)
  := is01cat_leftmodule (R:=rng_op R).

Instance is2graph_rightmodule {R : Ring} : Is2Graph (RightModule R)
  := is2graph_leftmodule (R:=rng_op R).

Instance is1cat_rightmodule {R : Ring} : Is1Cat (RightModule R)
  := is1cat_leftmodule (R:=rng_op R).

Instance hasequivs_rightmodule {R : Ring} : HasEquivs (RightModule R)
  := hasequivs_leftmodule (R:=rng_op R).

(** ** Kernel of module homomorphism *)

Instance isleftsubmodule_grp_kernel {R : Ring}
  {M N : LeftModule R} (f : M $-> N)
  : IsLeftSubmodule (grp_kernel f).
Proof.
  srapply Build_IsLeftSubmodule.
  intros r m n.
  lhs napply lm_homo_lact.
  rhs_V napply (lm_zero_r r).
  apply ap.
  exact n.
Defined.

Instance isrightsubmodule_grp_kernel {R : Ring}
  {M N : RightModule R} (f : M $-> N)
  : IsRightSubmodule (grp_kernel f)
  := isleftsubmodule_grp_kernel (R:=rng_op R) f.

Definition lm_kernel {R : Ring} {M N : LeftModule R} (f : M $-> N)
  : LeftSubmodule M
  := Build_LeftSubmodule _ _ (grp_kernel f) _.

Definition rm_kernel {R : Ring} {M N : RightModule R} (f : M $-> N)
  : RightSubmodule M
  := lm_kernel (R:=rng_op R) f.

(** ** Image of module homomorphism *)

Instance isleftsubmodule_grp_image {R : Ring}
  {M N : LeftModule R} (f : M $-> N)
  : IsLeftSubmodule (grp_image f).
Proof.
  srapply Build_IsLeftSubmodule.
  intros r m; apply Trunc_functor; intros [n p].
  exists (r *L n).
  lhs napply lm_homo_lact.
  apply ap.
  exact p.
Defined.

Instance isrightsubmodule_grp_image {R : Ring}
  {M N : RightModule R} (f : M $-> N)
  : IsRightSubmodule (grp_image f)
  := isleftsubmodule_grp_image (R:=rng_op R) f.

Definition lm_image {R : Ring} {M N : LeftModule R} (f : M $-> N)
  : LeftSubmodule N
  := Build_LeftSubmodule _ _ (grp_image f) _.

Definition rm_image {R : Ring} {M N : RightModule R} (f : M $-> N)
  : RightSubmodule N
  := lm_image (R:=rng_op R) f.

(** ** Quotient Modules *)

(** The quotient abelian group of a module and a submodule has a natural ring action. *)
Instance isleftmodule_quotientabgroup {R : Ring}
  (M : LeftModule R) (N : LeftSubmodule M)
  : IsLeftModule R (QuotientAbGroup M N).
Proof.
  snapply Build_IsLeftModule.
  - intros r.
    snapply quotient_abgroup_rec.
    + refine (grp_quotient_map $o _). 
      snapply Build_GroupHomomorphism.
      * exact (lact r).
      * intros x y.
        apply lm_dist_l.
    + intros n Nn; simpl.
      apply qglue.
      apply issubgroup_in_inv_op.
      2: exact issubgroup_in_unit.
      by apply is_left_submodule.
  - intros r m n; revert m.
    snapply Quotient_ind_hprop; [exact _ | intros m; revert n].
    snapply Quotient_ind_hprop; [exact _ | intros n; simpl].
    rapply ap.
    apply lm_dist_l.
  - intros r s.
    snapply Quotient_ind_hprop; [exact _| intros m; simpl].
    rapply ap.
    apply lm_dist_r.
  - intros r s.
    snapply Quotient_ind_hprop; [exact _| intros m; simpl].
    rapply ap.
    apply lm_assoc.
  - snapply Quotient_ind_hprop; [exact _| intros m; simpl].
    rapply ap.
    apply lm_unit.
Defined.

Instance isrightmodule_quotientabgroup {R : Ring}
  (M : RightModule R) (N : RightSubmodule M)
  : IsRightModule R (QuotientAbGroup M N)
  := isleftmodule_quotientabgroup (R:=rng_op R) M N.

(** We can therefore form the quotient module of a module by its submodule. *)
Definition QuotientLeftModule {R : Ring} (M : LeftModule R) (N : LeftSubmodule M)
  : LeftModule R
  := Build_LeftModule R (QuotientAbGroup M N) _.

Definition QuotientRightModule {R : Ring} (M : RightModule R) (N : RightSubmodule M)
  : RightModule R
  := QuotientLeftModule (R:=rng_op R) M N.

Infix "/" := QuotientLeftModule : module_scope.

(** TODO: Notation for right module quotient? *)
  
(** ** First Isomorphism Theorem *)

Local Open Scope module_scope.
Local Open Scope wc_iso_scope.

Definition lm_first_iso `{Funext} {R : Ring} {M N : LeftModule R} (f : M $-> N)
  : M / lm_kernel f ≅ lm_image f.
Proof.
  snapply Build_LeftModuleIsomorphism'.
  1: rapply abgroup_first_iso.
  intros r.
  srapply Quotient_ind_hprop; intros m.
  apply path_sigma_hprop; simpl.
  apply lm_homo_lact.
Defined.

Definition rm_first_iso `{Funext} {R : Ring} {M N : RightModule R} (f : M $-> N)
  : QuotientRightModule M (rm_kernel f) ≅ rm_image f
  := lm_first_iso (R:=rng_op R) f.

(** ** Direct products *)

(** TODO: generalise to biproducts *)
(** The direct product of modules *)
Definition lm_prod {R : Ring} : LeftModule R -> LeftModule R -> LeftModule R.
Proof.
  intros M N.
  snapply (Build_LeftModule R (ab_biprod M N)).
  snapply Build_IsLeftModule.
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

Definition rm_prod {R : Ring} : RightModule R -> RightModule R -> RightModule R
  := lm_prod (R:=rng_op R).

Definition lm_prod_fst {R : Ring} {M N : LeftModule R} : lm_prod M N $-> M.
Proof.
  snapply Build_LeftModuleHomomorphism.
  - exact grp_prod_pr1.
  - reflexivity.
Defined.

Definition rm_prod_fst {R : Ring} {M N : RightModule R} : rm_prod M N $-> M
  := lm_prod_fst (R:=rng_op R).

Definition lm_prod_snd {R : Ring} {M N : LeftModule R} : lm_prod M N $-> N.
Proof.
  snapply Build_LeftModuleHomomorphism.
  - exact grp_prod_pr2.
  - reflexivity.
Defined.

Definition rm_prod_snd {R : Ring} {M N : RightModule R} : rm_prod M N $-> N
  := lm_prod_snd (R:=rng_op R).

Definition lm_prod_corec {R : Ring} {M N : LeftModule R} (L : LeftModule R)
  (f : L $-> M) (g : L $-> N)
  : L $-> lm_prod M N.
Proof.
  snapply Build_LeftModuleHomomorphism.
  - exact (grp_prod_corec f g).
  - intros r l.
    apply path_prod; apply lm_homo_lact.
Defined.

Definition rm_prod_corec {R : Ring} {M N : RightModule R} (R' : RightModule R)
  (f : R' $-> M) (g : R' $-> N)
  : R' $-> rm_prod M N
  := lm_prod_corec (R:=rng_op R) R' f g.

Instance hasbinaryproducts_leftmodule {R : Ring}
  : HasBinaryProducts (LeftModule R).
Proof.
  intros M N.
  snapply Build_BinaryProduct.
  - exact (lm_prod M N).
  - exact lm_prod_fst.
  - exact lm_prod_snd.
  - exact lm_prod_corec.
  - cbn; reflexivity.
  - cbn; reflexivity.
  - intros L f g p q a.
    exact (path_prod' (p a) (q a)).
Defined.

Instance hasbinaryproducts_rightmodule {R : Ring}
  : HasBinaryProducts (RightModule R)
  := hasbinaryproducts_leftmodule (R:=rng_op R).

(** ** Finite Sums *)

(** Left scalar multiplication distributes over finite sums of left module elements. *)
Definition lm_sum_dist_l {R : Ring} (M : LeftModule R) (n : nat)
  (f : forall k, (k < n)%nat -> M) (r : R)
  : r *L ab_sum n f = ab_sum n (fun k Hk => r *L f k Hk).
Proof.
  induction n as [|n IHn].
  1: apply lm_zero_r.
  lhs napply lm_dist_l; simpl; f_ap.
Defined.

(** Right scalar multiplication distributes over finite sums of right module elements. *)
Definition rm_sum_dist_r {R : Ring} (M : RightModule R) (n : nat)
  (f : forall k, (k < n)%nat -> M) (r : R)
  : ab_sum n f *R r = ab_sum n (fun k Hk => f k Hk *R r)
  := lm_sum_dist_l (R:=rng_op R) M n f r.

(** Left module elements distribute over finite sums of scalars. *)
Definition lm_sum_dist_r {R : Ring} (M : LeftModule R) (n : nat)
  (f : forall k, (k < n)%nat -> R) (x : M)
  : ab_sum n f *L x = ab_sum n (fun k Hk => f k Hk *L x).
Proof.
  induction n as [|n IHn].
  1: apply lm_zero_l.
  lhs napply lm_dist_r; simpl; f_ap.
Defined.

(** Right module elements distribute over finite sums of scalar. *)
Definition rm_sum_dist_l {R : Ring} (M : RightModule R) (n : nat)
  (f : forall k, (k < n)%nat -> R) (x : M)
  : x *R ab_sum n f = ab_sum n (fun k Hk => x *R f k Hk)
  := lm_sum_dist_r (R:=rng_op R) M n f x.
