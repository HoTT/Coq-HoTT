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
  snrapply (Build_Subgroup _ (fun b => hexists (fun a => f a = b))).
  repeat split.
  1: exact _.
  1: apply tr; exists mon_unit; apply grp_homo_unit.
  { intros x y p q; strip_truncations; apply tr.
    destruct p as [a []], q as [b []].
    exists (a + b).
    apply grp_homo_op. }
  intros b p.
  strip_truncations.
  destruct p as [a []].
  apply tr; exists (- a).
  apply grp_homo_inv.
Defined.

Definition grp_image_in {A B : Group} (f : A $-> B) : A $-> grp_image f.
Proof.
  snrapply Build_GroupHomomorphism.
  { intro x.
    exists (f x).
    srapply tr.
    exists x.
    reflexivity. }
  cbn. grp_auto.
Defined.
