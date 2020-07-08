Require Import Basics Types.
Require Import Algebra.Groups.Group.
Require Import Algebra.Groups.Subgroup.
Require Import WildCat.
Require Import Truncations.
Require Import Factorization.

(** Image of group homomorphisms *)

Local Open Scope mc_add_scope.

(** The image of a group homomorphisms between groups is a subgroup *)
Definition grp_image {A B : Group} (f : A $-> B) : Subgroup B.
Proof.
  snrapply Build_Subgroup.
  { (** The underlying type is the (propositional) image of the type *)
  srapply (Build_Group (image (Tr (-1)) f)); repeat split.
  + (** Group operation *)
    intros [a p] [b q].
    exists (a + b).
    strip_truncations.
    apply tr.
    exists (p.1 + q.1).
    rewrite grp_homo_op.
    rewrite p.2, q.2. 
    reflexivity.
  + (** Group unit *)
    exists mon_unit.
    apply tr.
    exists mon_unit.
    apply (grp_homo_unit f).
  + (** Group inverse *)
    intros [a p].
    exists (- a).
    strip_truncations.
    apply tr.
    exists (- p.1).
    rewrite grp_homo_inv.
    apply ap, p.2.
  (** The image is a set *)
  + exact _.
  (** Our operation is commutative *)
  + intros [a p] [b q] [c r].
    srapply path_sigma_hprop.
    cbn; apply associativity.
  (** Left identity *)
  + intros [a p].
    srapply path_sigma_hprop.
    cbn; apply left_identity.
  (** Right identity *)
  + intros [a p].
    srapply path_sigma_hprop.
    cbn; apply right_identity.
  (** Left inverse *)
  + intros [a p].
    srapply path_sigma_hprop.
    cbn; apply left_inverse.
  (** Right inverse *)
  + intros [a p].
    srapply path_sigma_hprop.
    cbn; apply right_inverse. }
  (** The image is a subgroup *)
  snrapply Build_IsSubgroup.
  { snrapply Build_GroupHomomorphism.
    (** The inclusion map is just the projection *)
    1: exact pr1.
    (** This is easily a homomorphism *)
    intros ??; reflexivity. }
  hnf; cbn; intros a b.
  (** We know that the first components of this sigma type are equal and since the second component is a proposition we are done. *)
  apply path_sigma_hprop.
Defined.

Global Instance ishset_grp_image {A B : Group} (f : A $-> B)
  : IsHSet (grp_image f) := _.

Definition grp_image_in {A B : Group} (f : A $-> B) : A $-> grp_image f.
Proof.
  snrapply Build_GroupHomomorphism.
  { intro x.
    exists (f x).
    srapply tr.
    exists x.
    reflexivity. }
  { intros x y.
    apply path_sigma_hprop.
    apply grp_homo_op. }  
Defined.
