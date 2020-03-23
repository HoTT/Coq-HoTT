Require Import Basics Types.
Require Import Algebra.Groups.Group.
Require Import Algebra.Groups.Subgroup.
Require Import WildCat.

(** Kernels of groups *)

Local Open Scope mc_scope.

Definition grp_kernel {A B : Group} (f : A $-> B) : Subgroup A.
Proof.
  snrapply Build_Subgroup.
  { srapply (Build_Group (hfiber f group_unit)); repeat split.
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
    - (** Associativity *)
      intros [a p] [b q] [c r].
      srapply path_sigma_hprop.
      cbn; apply associativity.
    - (** Left identity *)
      intros [a p].
      srapply path_sigma_hprop.
      cbn; apply left_identity.
    - (** Right identity *)
      intros [a p].
      srapply path_sigma_hprop.
      cbn; apply right_identity.
    - (** Left inverse *)
      intros [a p].
      srapply path_sigma_hprop.
      cbn; apply left_inverse.
    - (** Right inverse *)
      intros [a p].
      srapply path_sigma_hprop.
      cbn; apply right_inverse. }
  (** The kernel is a subgroup of the source of the map *)
  snrapply Build_IsSubgroup.
  { snrapply Build_GroupHomomorphism.
    1: exact pr1.
    intros ??; reflexivity. }
  hnf; cbn; intros x y p.
  by apply path_sigma_hprop.
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

Locate IsNormalSubgroup.

Global Instance isnormal_kernel {A B : Group} (f : A $-> B)
  : IsNormalSubgroup (Kernel f).
Proof.
  apply isnormalsubgroup_of_cong_mem.
  intros g n.
  srefine ((_ ; _ ); _).
  3: reflexivity.
  simpl.
  rewrite grp_homo_op, grp_homo_op, grp_homo_inv.
  rewrite (pr2 n), (right_identity (- f g)).
  rewrite (negate_l _).
  reflexivity.
Defined.
