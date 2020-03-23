Require Import Basics.
Require Import Types.
Require Import Fibrations.
Require Import AbelianGroup.
Require Import Algebra.Groups.Group.
Require Import Algebra.Groups.Subgroup.
Require Import WildCat.

(** Kernels of groups *)

Local Open Scope mc_scope.

Definition grp_kernel {A B : Group} (f : A $-> B) : Group.
Proof.
  srapply (Build_Group (hfiber f group_unit)); repeat split.
  - (** Operation *)
    intros [a p] [b q].
    exists (sg_op a b).
    rewrite grp_homo_op, p, q.
    apply left_identity.
  - (** Unit *)
    exists mon_unit.
    apply (grp_homo_unit f).
  - (** Inverse *)
    intros [a p].
    exists (-a).
    rewrite grp_homo_inv, p.
    exact negate_mon_unit.
  - (** HSet *)
    exact _.
  - intros [a p] [b q] [c r].
    srapply path_sigma_hprop.
    cbn; apply associativity.
  - intros [a p].
    srapply path_sigma_hprop.
    cbn; apply left_identity.
  - intros [a p].
    srapply path_sigma_hprop.
    cbn; apply right_identity.
  - intros [a p].
    srapply path_sigma_hprop.
    cbn; apply left_inverse.
  - intros [a p].
    srapply path_sigma_hprop.
    cbn; apply right_inverse.
Defined.

Definition grp_homo_kernel_pr1 {A B : Group} (f : A $-> B)
  : (grp_kernel f) $-> A.
Proof.
  srapply Build_GroupHomomorphism.
  - apply pr1.
  - intros a b; reflexivity.
Defined.

Global Instance isinjective_grp_homo_kernel_pr1 {A B : Group}
  (f : A $-> B) : IsInjective (grp_homo_kernel_pr1 f).
Proof.
  intros a b.
  apply path_sigma_hprop.
Defined.

Global Instance issubgroup_grp_kernel {A B : Group}
  (f : A $-> B) : IsSubgroup (grp_kernel f) A.
Proof.
  srapply Build_IsSubgroup.
  + exact (grp_homo_kernel_pr1 f).
  + exact (isinjective_grp_homo_kernel_pr1 _).
Defined.

Definition Kernel {A B : Group} (f : A $-> B)
  : Subgroup A := Build_Subgroup A (grp_kernel f) _.

Global Instance isnormal_abkernel {A : AbGroup} {B : Group} (f : (A : Group) $-> B)
  : IsNormalSubgroup (Kernel f) := _.
