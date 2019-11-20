Require Import Basics.
Require Import Types.
Require Import PathAny.
Require Export Classes.interfaces.abstract_algebra.
Require Export Classes.theory.groups.

(** ** Groups *)

(** * Definition of Group *)

(** A group consists of a type, and operation on that type, and unit and an inverse, such that they satisfy the group axioms in IsGroup. *)
Class Group := {
  group_type : Type;
  group_sgop :> SgOp group_type;
  group_unit :> MonUnit group_type;
  group_inverse :> Negate group_type;
  group_isgroup :> IsGroup group_type;
}.

(** We coerce groups back to types. *)
Coercion group_type : Group >-> Sortclass.

Definition issig_group : _ <~> Group
  := ltac:(issig).

(** Groups are pointed sets with point the identity. *)
Global Instance ispointed_group (G : Group)
  : IsPointed G := @mon_unit G _.

(** * Some basic properties of groups *)

(** An element acting like the identity is unique. *)
Definition identity_unique {A : Type} {Aop : SgOp A}
  (x y : A) {p : LeftIdentity Aop x} {q : RightIdentity Aop y}
  : x = y := (q x)^ @ p y.

Definition identity_unique' {A : Type} {Aop : SgOp A}
  (x y : A) {p : LeftIdentity Aop x} {q : RightIdentity Aop y}
  : y = x := (identity_unique x y)^.

(** An element acting like an inverse is unique. *)
Definition inverse_unique `{IsMonoid A}
  (a x y : A) {p : x & a = mon_unit} {q : a & y = mon_unit}
  : x = y.
Proof.
  refine ((right_identity x)^ @ ap _ q^ @ _).
  refine (associativity _ _ _ @ _).
  refine (ap (& y) p @ _).
  apply left_identity.
Defined.

(** Inverses are involutive *)
(* Check negate_involutive. *)

(** Inverses distribute over the group operation *)
(* Check negate_sg_op. *)

(** Group elements can be cancelled on the left of an equation *)
(* Check group_cancelL. *)

(** Group elements can be cancelled on the right of an equation *)
(* Check group_cancelR. *)

(** Definition of Group Homomorphism *)

(* A group homomorphism consists of a map between groups and a proof that the map preserves the group operation. *)
Class GroupHomomorphism (G H : Group) := Build_GroupHomomorphism' {
  grp_homo_map : G -> H;
  grp_homo_ishomo :> IsMonoidPreserving grp_homo_map;
}.

(* We coerce a homomorphism to its underlying map. *)
Coercion grp_homo_map : GroupHomomorphism >-> Funclass.
(* Notation "G '->G' H" := (GroupHomomorphism G H) (at level 20). *)

Definition issig_GroupHomomorphism {G H : Group} : _ <~> GroupHomomorphism G H
  := ltac:(issig).

Definition path_GroupHomomorphism `{F : Funext} {G H : Group}
  {g h : GroupHomomorphism G H} : g == h -> g = h.
Proof.
  intro p.
  apply ((ap issig_GroupHomomorphism^-1)^-1).
  serapply path_sigma_hprop.
  by apply path_forall.
Defined.

(** * Some basic properties of group homomorphisms *)

(** Group homomorphisms preserve identities *)
Definition grp_homo_unit {G H} (f : GroupHomomorphism G H)
  : f (mon_unit) = mon_unit.
Proof.
  apply monmor_unitmor.
Defined.

(** Group homomorphisms preserve group operations *)
Definition grp_homo_op {G H} (f : GroupHomomorphism G H)
  : forall x y : G, f (x & y) = f x & f y.
Proof.
  apply monmor_sgmor.
Defined.

(** Group homomorphisms preserve inverses *)
Definition grp_homo_inv {G H} (f : GroupHomomorphism G H)
  : forall x, f (- x) = -(f x).
Proof.
  intro x.
  apply (inverse_unique (f x)).
  + refine (_ @ grp_homo_unit f).
    refine ((grp_homo_op f (-x) x)^ @ _).
    apply ap.
    apply left_inverse.
  + apply right_inverse.
Defined.

(** When building a group homomorphism we only need that it preserves the group operation, since we can prove that the identity is preserved. *)
Definition Build_GroupHomomorphism {G H : Group}
  (f : G -> H) {h : IsSemiGroupPreserving f}
  : GroupHomomorphism G H.
Proof.
  serapply (Build_GroupHomomorphism' _ _ f).
  split.
  1: exact h.
  unfold IsUnitPreserving.
  apply (group_cancelL (f mon_unit)).
  refine (_ @ (right_identity _)^).
  refine (_ @ ap _ (monoid_left_id _ mon_unit)).
  symmetry.
  apply h.
Defined.

Definition grp_homo_compose {G H K : Group}
  : GroupHomomorphism H K -> GroupHomomorphism G H -> GroupHomomorphism G K.
Proof.
  intros f g.
  serapply Build_GroupHomomorphism.
  1: exact (f o g).
  intros x y.
  refine (ap f (grp_homo_op g _ _) @ _).
  apply grp_homo_op.
Defined.

(* An isomorphism of groups is a group homomorphism that is an equivalence. *)
Class GroupIsomorphism (G H : Group) := Build_GroupIsomorphism {
  grp_iso_homo :> GroupHomomorphism G H;
  isequiv_group_iso :> IsEquiv grp_iso_homo;
}.

Coercion grp_iso_homo : GroupIsomorphism >-> GroupHomomorphism.

Definition issig_GroupIsomorphism (G H : Group)
  : _ <~> GroupIsomorphism G H := ltac:(issig).

Definition grp_iso_inverse {G H : Group}
  : GroupIsomorphism G H -> GroupIsomorphism H G.
Proof.
  intros [f e].
  serapply Build_GroupIsomorphism.
  { serapply Build_GroupHomomorphism.
    1: exact f^-1.
    unfold IsSemiGroupPreserving.
    intros x y.
    apply (ap f)^-1.
    rewrite grp_homo_op.
    by rewrite !eisretr. }
  exact _.
Defined.

(* We can build an isomorphism from an operation preserving equivalence. *)
Definition Build_GroupIsomorphism' {G H : Group}
  (f : G <~> H) (h : IsSemiGroupPreserving f)
  : GroupIsomorphism G H.
Proof.
  serapply Build_GroupIsomorphism.
  1: serapply Build_GroupHomomorphism.
  exact _.
Defined.

(** Group Isomorphisms are a reflexive relation *)
Global Instance reflexive_groupisomorphism
  : Reflexive GroupIsomorphism.
Proof.
  intro x.
  by serapply Build_GroupIsomorphism'.
Defined.

(** Group Isomorphisms are a symmetric relation *)
Global Instance symmetric_groupisomorphism
  : Symmetric GroupIsomorphism.
Proof.
  intros G H.
  serapply grp_iso_inverse.
Defined.

Global Instance transitive_groupisomorphism
  : Transitive GroupIsomorphism.
Proof.
  intros G H K f g.
  serapply Build_GroupIsomorphism.
  1: serapply grp_homo_compose.
  exact _.
Defined.

(** TODO: Finish this
Definition equiv_path_group {U : Univalence} {G H : Group}
  : GroupIsomorphism G H <~> G = H.
Proof.
  refine (_ oE (issig_GroupIsomorphism _ _)^-1).
  eqp_issig_contr issig_group.
Admitted.
*)

(** * Simple group equivalences *)

(** Left multiplication is an equivalence *)
Global Instance isequiv_group_left_op `{IsGroup G}
  : forall x, IsEquiv (x &).
Proof.
  intro x.
  serapply isequiv_adjointify.
  1: exact (-x &).
  all: intro y.
  all: refine (associativity _ _ _ @ _ @ left_identity y).
  all: refine (ap (& y) _).
  1: apply right_inverse.
  apply left_inverse.
Defined.

(** Right multiplication is an equivalence *)
Global Instance isequiv_group_right_op `{IsGroup G}
  : forall x, IsEquiv (& x).
Proof.
  intro x.
  serapply isequiv_adjointify.
  1: exact (& - x).
  all: intro y.
  all: refine ((associativity _ _ _)^ @ _ @ right_identity y).
  all: refine (ap (y &) _).
  1: apply left_inverse.
  apply right_inverse.
Defined.

Definition left_mult_equiv `{IsGroup G} : G -> G <~> G
  := fun x => Build_Equiv _ _ (x &) _.

(* Right multiplication is an equivalence. *)
Definition right_mult_equiv `{IsGroup G} : G -> G <~> G
  := fun x => Build_Equiv _ _ (& x) _.

Global Instance isequiv_group_inverse `{IsGroup G}
  : IsEquiv (-).
Proof.
  serapply isequiv_adjointify.
  1: apply (-).
  all: intro; apply negate_involutive.
Defined.

(** * Direct product of group *)

Definition group_prod : Group -> Group -> Group.
Proof.
  intros G H.
  serapply (Build_Group (G * H)).
  (** Operation *)
  { intros [g1 h1] [g2 h2].
    exact (g1 & g2, h1 & h2). }
  (** Unit *)
  1: exact (mon_unit, mon_unit).
  (** Inverse *)
  { intros [g h].
    exact (-g, -h). }
  (** Group laws *)
  serapply Build_IsGroup.
  (** Monoid laws *)
  { serapply Build_IsMonoid.
    (** Semigroup lawss *)
    { serapply Build_IsSemiGroup.
      (** Associativity *)
      intros [g1 h1] [g2 h2] [g3 h3].
      apply path_prod; cbn.
      1,2: apply associativity. }
    (** Left identity *)
    { intros [g h].
      apply path_prod; cbn.
      1,2: apply left_identity. }
    (** Right identity *)
    { intros [g h].
      apply path_prod; cbn.
      1,2: apply right_identity. } }
  (** Left inverse *)
  { intros [g h].
    apply path_prod; cbn.
    1,2: apply left_inverse. }
  (** Right inverse *)
  { intros [g h].
    apply path_prod; cbn.
    1,2: apply right_inverse. }
Defined.

Definition groupiso_prod {A B C D : Group}
  : GroupIsomorphism A B -> GroupIsomorphism C D
    -> GroupIsomorphism (group_prod A C) (group_prod B D).
Proof.
  intros f g.
  serapply Build_GroupIsomorphism'.
  1: serapply (equiv_functor_prod (f:=f) (g:=g)).
  simpl.
  unfold functor_prod.
  intros x y.
  apply path_prod.
  1,2: apply grp_homo_op.
Defined.
