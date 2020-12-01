Require Import Basics Types.
Require Import Algebra.Groups.Group.
Require Import Algebra.Groups.Subgroup.
Require Import WildCat.

(** * Kernels of group homomorphisms *)

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

Definition grp_kernel {A B : Group} (f : GroupHomomorphism A B) : Subgroup A.
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

Global Instance isnormal_kernel {A B : Group} (f : GroupHomomorphism A B)
  : IsNormalSubgroup (grp_kernel f).
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

(** ** Corecursion principle for group kernels *)

Proposition grp_kernel_corec {A B G : Group} {f : A $-> B} {g : G $-> A}
            (h : f $o g == grp_homo_const) : G $-> grp_kernel f.
Proof.
  snrapply Build_GroupHomomorphism.
  - exact (fun x:G => (g x; h x)).
  - intros x x'.
    apply path_sigma_hprop; cbn.
    apply grp_homo_op.
Defined.

Theorem equiv_grp_kernel_corec `{Funext} {A B G : Group} {f : A $-> B}
  : (G $-> grp_kernel f) <~> (exists g : G $-> A, f $o g == grp_homo_const).
Proof.
  srapply equiv_adjointify.
  - intro k. refine (subgrp_incl _ _ $o k; _).
    intro x; cbn.
    exact (k x).2.
  - intros [g p].
    exact (grp_kernel_corec p).
  - intros [g p].
    apply path_sigma_hprop; unfold pr1.
    apply equiv_path_grouphomomorphism; intro; reflexivity.
  - intro k.
    apply equiv_path_grouphomomorphism; intro x.
    apply path_sigma_hprop; reflexivity.
Defined.

(** ** Characterisation of group embeddings *)

Local Existing Instance ishprop_path_subgroup.

Proposition equiv_kernel_isembedding `{Univalence} {A B : Group} (f : A $-> B)
  : (grp_kernel f = trivial_subgroup) <~> IsEmbedding f.
Proof.
  srapply equiv_iff_hprop.
  - intros phi b.
    apply hprop_inhabited_contr; intro a.
    rapply (contr_equiv' _ (equiv_grp_hfiber _ _ a)^-1%equiv).
    rapply (transport Contr (x:=grp_trivial)).
    exact (ap (group_type o subgroup_group A) phi^).
  - intro isemb_f.
    rapply equiv_path_subgroup.
    srefine (grp_iso_inverse _; _).
    + srapply Build_GroupIsomorphism.
      * exact grp_homo_const.
      * srapply isequiv_adjointify.
        1: exact grp_homo_const.
        all: intro x; apply path_ishprop.
    + apply equiv_path_grouphomomorphism; intro x; cbn.
      refine (ap pr1 (y:=(mon_unit; grp_homo_unit f)) _).
      apply path_ishprop.
Defined.
