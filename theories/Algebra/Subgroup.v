Require Import Basics.
Require Import Types.
Require Import HSet.
Require Import Algebra.Group.

Local Open Scope mc_mult_scope.
Generalizable Variables G H A B C N f g.

(** * Subgroups *)

(** The property of being a subgroup *)
Class IsSubgroup (G H : Group) := {
  issubgroup_incl :> GroupHomomorphism G H;
  isinj_issubgroup_incl :> IsInjective issubgroup_incl;
}.

(* Subgroup inclusion is an embedding. *)
Global Instance isembedding_issubgroup_incl `{!IsSubgroup G H}
  : IsEmbedding (@issubgroup_incl G H _).
Proof.
  apply isembedding_isinj_hset.
  apply isinj_issubgroup_incl.
Defined.

Definition issig_issubgroup G H : _ <~> IsSubgroup G H
  := ltac:(issig).

(** A subgroup of a group H is a group G which is a subgroup of H. *) 
Class Subgroup (H : Group) := {
  subgroup_group :> Group;
  subgroup_issubgroup :> IsSubgroup subgroup_group H;
}.

Coercion subgroup_group : Subgroup >-> Group.

Section Cosets.

  (** Left and right cosets give equivalence relations. *)

  Context {G : Group} `{!IsSubgroup H G}.

  (* The relation of being in a left coset represented by an element. *)
  Definition in_cosetL : Relation G.
  Proof.
    intros x y.
    refine (hfiber issubgroup_incl _).
    exact (-x * y).
  Defined.

  (* The relation of being in a right coset represented by an element. *)
  Definition in_cosetR : Relation G.
  Proof.
    intros x y.
    refine (hfiber issubgroup_incl _).
    exact (x * -y).
  Defined.

  (* These are props *)

  Global Instance ishprop_in_cosetL : is_mere_relation G in_cosetL.
  Proof.
    exact _.
  Defined.

  Global Instance ishprop_in_cosetR : is_mere_relation G in_cosetR.
  Proof.
    exact _.
  Defined.

  (* Infact they are both equivalence relations. *)

  Global Instance reflexive_in_cosetL : Reflexive in_cosetL.
  Proof.
    intro x; hnf.
    exists mon_unit.
    refine (_ @ _).
    2: apply symmetry, left_inverse.
    apply grp_homo_unit.
  Defined.

  Global Instance reflexive_in_cosetR : Reflexive in_cosetR.
  Proof.
    intro x; hnf.
    exists mon_unit.
    refine (_ @ _).
    2: apply symmetry, right_inverse.
    apply grp_homo_unit.
  Defined.

  Global Instance symmetric_in_cosetL : Symmetric in_cosetL.
  Proof.
    intros x y [h p]; hnf.
    exists (-h).
    refine (_ @ _).
    1: apply grp_homo_inv.
    apply moveR_equiv_M.
    refine (p @ _).
    symmetry.
    refine (negate_sg_op _ _ @ _).
    refine (ap (-x *.) _).
    apply negate_involutive.
  Defined.

  Global Instance symmetric_in_cosetR : Symmetric in_cosetR.
  Proof.
    intros x y [h p]; hnf.
    exists (-h).
    refine (_ @ _).
    1: apply grp_homo_inv.
    apply moveR_equiv_M.
    refine (p @ _).
    symmetry.
    refine (negate_sg_op _ _ @ _).
    refine (ap (fun x => x *  -y) _).
    apply negate_involutive.
  Defined.

  Global Instance transitive_in_cosetL : Transitive in_cosetL.
  Proof.
    intros x y z [h p] [h' q].
    exists (h * h').
    refine (grp_homo_op _ _ _ @ _).
    destruct p^, q^.
    rewrite <- simple_associativity.
    apply ap.
    rewrite simple_associativity.
    refine (ap (fun x => x *  -z) _ @ _).
    1: apply right_inverse.
    apply left_identity.
  Defined.

  Global Instance transitive_in_cosetR : Transitive in_cosetR.
  Proof.
    intros x y z [h p] [h' q].
    exists (h * h').
    refine (grp_homo_op _ _ _ @ _).
    destruct p^, q^.
    rewrite <- simple_associativity.
    apply ap.
    rewrite simple_associativity.
    refine (ap (fun x => x *  -z) _ @ _).
    1: apply left_inverse.
    apply left_identity.
  Defined.

End Cosets.

(** Identities related to the left and right cosets. *)

Definition in_cosetL_unit {G : Group} `{!IsSubgroup N G}
  : forall x y, in_cosetL (-x * y) mon_unit <~> in_cosetL x y.
Proof.
  intros x y.
  unfold in_cosetL.
  rewrite negate_sg_op.
  rewrite negate_involutive.
  rewrite (right_identity (-y * x)).
  change (in_cosetL y x <~> in_cosetL x y).
  serapply equiv_iff_hprop;
  by intro; symmetry.
Defined.

Definition in_cosetR_unit {G : Group} `{!IsSubgroup N G}
  : forall x y, in_cosetR (x * -y) mon_unit <~> in_cosetR x y.
Proof.
  intros x y.
  unfold in_cosetR.
  rewrite negate_mon_unit.
  rewrite (right_identity (x * -y)).
  reflexivity.
Defined.

(** Symmetry is an equivalence. *)
Definition equiv_in_cosetL_symm {G : Group} `{!IsSubgroup N G}
  : forall x y, in_cosetL x y <~> in_cosetL y x.
Proof.
  intros x y.
  serapply equiv_iff_hprop.
  all: by intro.
Defined.

Definition equiv_in_cosetR_symm {G : Group} `{!IsSubgroup N G}
  : forall x y, in_cosetR x y <~> in_cosetR y x.
Proof.
  intros x y.
  serapply equiv_iff_hprop.
  all: by intro.
Defined.

(* A subgroup is normal if being in a left coset is equivalent to being in a right coset represented by the same element. *)
Class IsNormalSubgroup {G : Group} (N : Subgroup G) := {
  isnormal {x y} : in_cosetL x y <~> in_cosetR x y;
}.

(* Inverses are then respected *)
Definition in_cosetL_inv {G : Group} `{!IsNormalSubgroup N}
  : forall x y, in_cosetL (-x) (-y) <~> in_cosetL x y.
Proof.
  intros x y.
  refine (_ oE (in_cosetL_unit _ _)^-1).
  refine (_ oE isnormal).
  refine (_ oE in_cosetR_unit _ _).
  refine (_ oE isnormal^-1).
  by rewrite negate_involutive.
Defined.

Definition in_cosetR_inv {G : Group} `{!IsNormalSubgroup N}
  : forall x y, in_cosetR (-x) (-y) <~> in_cosetR x y.
Proof.
  intros x y.
  refine (_ oE (in_cosetR_unit _ _)^-1).
  refine (_ oE isnormal^-1).
  refine (_ oE in_cosetL_unit _ _).
  refine (_ oE isnormal).
  by rewrite negate_involutive.
Defined.

(* There is always another element of the normal subgroup allowing us to commute with an element of the group. *)
Definition normal_subgroup_swap {G : Group}
  `{!IsNormalSubgroup N} (x : G) (h : N)
  : exists h' : N, x * issubgroup_incl h = issubgroup_incl h' * x.
Proof.
  assert (X : in_cosetL x (x * issubgroup_incl h)).
  { exists h.
    rewrite simple_associativity.
    rewrite left_inverse.
    symmetry.
    apply left_identity. }
  apply isnormal in X.
  destruct X as [a p].
  rewrite negate_sg_op in p.
  rewrite simple_associativity in p.
  eexists (-a).
  symmetry.
  rewrite grp_homo_inv.
  apply (moveR_equiv_M (f := (- _ *.))).
  cbn; rewrite negate_involutive.
  rewrite simple_associativity.
  apply (moveL_equiv_M (f := (fun x => x * _))).
  apply (moveL_equiv_M (f := (fun x => x * _))).
  symmetry.
  assumption.
Defined.

(* This let's us prove that left and right coset relations are congruences. *)
Definition in_cosetL_cong {G : Group} `{!IsNormalSubgroup N}
  : forall x x' y y', in_cosetL x y -> in_cosetL x' y' -> in_cosetL (x * x') (y * y').
Proof.
  intros x x' y y' [a p] [b q].
  eexists ?[c].
  rewrite negate_sg_op.
  rewrite <- simple_associativity.
  rewrite (simple_associativity (-x) y).
  rewrite <- p.
  rewrite simple_associativity.
  rewrite (normal_subgroup_swap _ a).2.
  rewrite <- simple_associativity.
  rewrite <- q.
  apply grp_homo_op.
Defined.

Definition in_cosetR_cong {G : Group} `{!IsNormalSubgroup N}
  : forall x x' y y', in_cosetR x y -> in_cosetR x' y' -> in_cosetR (x * x') (y * y').
Proof.
  intros x x' y y' [a p] [b q].
  eexists ?[c].
  rewrite negate_sg_op.
  rewrite <- simple_associativity.
  rewrite (simple_associativity x' (-y')).
  rewrite <- q.
  rewrite simple_associativity.
  rewrite (normal_subgroup_swap _ b).2.
  rewrite <- simple_associativity.
  rewrite <- p.
  apply grp_homo_op.
Defined.

