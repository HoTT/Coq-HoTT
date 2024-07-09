Require Import Basics.
Require Import Spaces.Pos.Core Spaces.Int.
Require Import Algebra.AbGroups.AbelianGroup.

Local Set Universe Minimization ToSet.

(** * The group of integers *)

(** See also Cyclic.v for a definition of the integers as the free group on one generator. *)

Local Open Scope int_scope.

Definition abgroup_Z@{} : AbGroup@{Set}.
Proof.
  snrapply Build_AbGroup.
  - refine (Build_Group Int int_add 0 int_neg _); repeat split.
    + exact _.
    + exact int_add_assoc.
    + exact int_add_0_r.
    + exact int_add_neg_l.
    + exact int_add_neg_r.
  - exact int_add_comm.
Defined.

(** For every group [G] and element [g : G], the map sending an integer to that power of [g] is a homomorphism. *)
Definition grp_pow_homo {G : Group} (g : G)
  : GroupHomomorphism abgroup_Z G.
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact (grp_pow g).
  intros m n; apply grp_pow_add.
Defined.

Local Open Scope mc_add_scope.

(** For every abelian group [A], [grp_pow] distributes over the group operation. *)
Definition grp_pow_plus {A : AbGroup} (a a' : A) (z : Int)
  : grp_pow (a + a') z = grp_pow a z + grp_pow a' z.
Proof.
  induction z.
  - symmetry; apply grp_unit_l.
  - rewrite 3 grp_pow_succ.
    rewrite <- 2 grp_assoc.
    nrapply (ap (a +)).
    rewrite (ab_comm (grp_pow a n)).
    rewrite <- grp_assoc.
    nrapply (ap (a' +)).
    rhs nrapply ab_comm.
    exact IHz.
  - rewrite 3 grp_pow_pred.
    rewrite grp_inv_op.
    rewrite (ab_comm (negate a')).
    rewrite <- 2 grp_assoc.
    nrapply (ap (_ +)).
    rewrite grp_assoc.
    rewrite (ab_comm (grp_pow _ _)).
    rewrite <- grp_assoc.
    nrapply (ap (_ +)).
    exact IHz.
Defined. 

Definition abgroup_Z_grp_pow_1 (z : Int)
  : grp_pow (G:=abgroup_Z) 1%int z = z.
Proof.
  induction z.
  - reflexivity.
  - rewrite grp_pow_succ.
    f_ap.
  - rewrite grp_pow_pred.
    f_ap.
Defined.
