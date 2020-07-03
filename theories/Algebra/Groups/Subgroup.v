Require Import Basics Types HSet.
Require Import Algebra.Groups.Group.

Local Open Scope mc_mult_scope.
Generalizable Variables G H A B C N f g.

(** * Subgroups *)

(** The property of being a subgroup *)
Class IsSubgroup (G H : Group) := {
  issubgroup_incl : GroupHomomorphism G H;
  isinj_issubgroup_incl : IsInjective issubgroup_incl;
}.

Global Existing Instance isinj_issubgroup_incl.

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
Record Subgroup (H : Group) := {
  subgroup_group : Group;
  subgroup_issubgroup : IsSubgroup subgroup_group H;
}.

Coercion subgroup_group : Subgroup >-> Group.
Global Existing Instance subgroup_issubgroup.
(* Arguments subgroup_group {_}. *)

Section Cosets.

  (** Left and right cosets give equivalence relations. *)

  Context {G : Group} (H : Group) `{!IsSubgroup H G}.

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
  : forall x y, in_cosetL N (-x * y) mon_unit <~> in_cosetL N x y.
Proof.
  intros x y.
  unfold in_cosetL.
  rewrite negate_sg_op.
  rewrite negate_involutive.
  rewrite (right_identity (-y * x)).
  change (in_cosetL N y x <~> in_cosetL N x y).
  srapply equiv_iff_hprop;
  by intro; symmetry.
Defined.

Definition in_cosetR_unit {G : Group} `{!IsSubgroup N G}
  : forall x y, in_cosetR N (x * -y) mon_unit <~> in_cosetR N x y.
Proof.
  intros x y.
  unfold in_cosetR.
  rewrite negate_mon_unit.
  rewrite (right_identity (x * -y)).
  reflexivity.
Defined.

(** Symmetry is an equivalence. *)
Definition equiv_in_cosetL_symm {G : Group} `{!IsSubgroup N G}
  : forall x y, in_cosetL N x y <~> in_cosetL N y x.
Proof.
  intros x y.
  srapply equiv_iff_hprop.
  all: by intro.
Defined.

Definition equiv_in_cosetR_symm {G : Group} `{!IsSubgroup N G}
  : forall x y, in_cosetR N x y <~> in_cosetR N y x.
Proof.
  intros x y.
  srapply equiv_iff_hprop.
  all: by intro.
Defined.

(* A subgroup is normal if being in a left coset is equivalent to being in a right coset represented by the same element. *)
Class IsNormalSubgroup (N : Group) {G : Group} `{IsSubgroup N G}
  := isnormal : forall {x y}, @in_cosetL G N _ x y <~> in_cosetR N x y.

Record NormalSubgroup (G : Group) := {
  normalsubgroup_group : Group;
  normalsubgroup_issubgroup : IsSubgroup normalsubgroup_group G;
  normalsubgroup_isnormal : IsNormalSubgroup normalsubgroup_group;
}.

Coercion normalsubgroup_subgroup (G : Group) : NormalSubgroup G -> Subgroup G.
Proof.
  intros [N H1 H2].
  exact (Build_Subgroup G N H1).
Defined.

(* Inverses are then respected *)
Definition in_cosetL_inv `{IsNormalSubgroup N G}
  : forall x y : G, in_cosetL N (-x) (-y) <~> in_cosetL N x y.
Proof.
  intros x y.
  refine (_ oE (in_cosetL_unit _ _)^-1).
  refine (_ oE isnormal).
  refine (_ oE in_cosetR_unit _ _).
  refine (_ oE isnormal^-1).
  by rewrite negate_involutive.
Defined.

Definition in_cosetR_inv `{IsNormalSubgroup N G}
  : forall x y : G, in_cosetR N (-x) (-y) <~> in_cosetR N x y.
Proof.
  intros x y.
  refine (_ oE (in_cosetR_unit _ _)^-1).
  refine (_ oE isnormal^-1).
  refine (_ oE in_cosetL_unit _ _).
  refine (_ oE isnormal).
  by rewrite negate_involutive.
Defined.

(** There is always another element of the normal subgroup allowing us to commute with an element of the group. *)
Definition normal_subgroup_swap `{IsNormalSubgroup N G} (x : G) (h : N)
  : exists h' : N, x * issubgroup_incl h = issubgroup_incl h' * x.
Proof.
  assert (X : in_cosetL N x (x * issubgroup_incl h)).
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

(* This lets us prove that left and right coset relations are congruences. *)
Definition in_cosetL_cong `{IsNormalSubgroup N G} (x x' y y' : G)
  : in_cosetL N x y -> in_cosetL N x' y' -> in_cosetL N (x * x') (y * y').
Proof.
  intros [a p] [b q].
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

Definition in_cosetR_cong `{IsNormalSubgroup N G} (x x' y y' : G)
  : in_cosetR N x y -> in_cosetR N x' y' -> in_cosetR N (x * x') (y * y').
Proof.
  intros [a p] [b q].
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

Definition isnormalsubgroup_of_cong_mem {G : Group} (N : Subgroup G)
  (h : forall g : G, forall n : N, exists m : N, - g * issubgroup_incl n * g = issubgroup_incl m)
  : IsNormalSubgroup N.
Proof.
  intros x y.
  apply equiv_iff_hprop; intros [m p].
  1: specialize (h (-y) (-m)).
  2: specialize (h y (-m)).
  1-2: destruct h as [m' p'].
  1-2: exists m'.
  1-2: rewrite <- p'.
  1-2: f_ap.
  1-2: rewrite grp_homo_inv, p, negate_sg_op, involutive. 
  1: rewrite associativity, involutive, (negate_r G y).
  2: rewrite (associativity (-y)), (negate_l G y).
  1-2: rewrite (left_identity _); reflexivity.
Defined.
