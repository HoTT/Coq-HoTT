Require Import Basics.
Require Import Types.
Require Import Cubical.
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

Definition issig_GroupHomomorphism (G H : Group) : _ <~> GroupHomomorphism G H
  := ltac:(issig).

Definition equiv_path_grouphomomorphism {F : Funext} {G H : Group}
  {g h : GroupHomomorphism G H} : g == h <~> g = h.
Proof.
  refine ((equiv_ap (issig_GroupHomomorphism G H)^-1 _ _)^-1 oE _).
  refine (equiv_path_sigma_hprop _ _ oE _).
  apply equiv_path_forall.
Defined.

Global Instance ishset_grouphomomorphism {F : Funext} {G H : Group}
  : IsHSet (GroupHomomorphism G H).
Proof.
  intros f g; apply (trunc_equiv' _ equiv_path_grouphomomorphism).
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

(** Under univalence, equality of groups is equivalent to isomorphism of groups. This is a long proof that mostly consists of rearranging sigma types. *)
Definition equiv_path_group {U : Univalence} {G H : Group}
  : GroupIsomorphism G H <~> G = H.
Proof.
  refine (equiv_compose' (B := sig (fun f : G <~> H => IsMonoidPreserving f)) _ _).
  { eqp_issig_contr issig_group.
    + intros [G [? [? [? ?]]]].
      exists 1%equiv.
      exact _.
    + intros [G [op [unit [neg ax]]]]; cbn.
      contr_sigsig G (equiv_idmap G).
      srefine (Build_Contr _ ((_;(_;(_;_)));_) _); cbn; try assumption; try exact _.
      intros [[op' [unit' [neg' ax']]] eq].
      apply path_sigma_hprop; cbn.
      (* We really need to fix https://github.com/HoTT/HoTT/issues/976 *)
      srefine (@ap _ _ (fun x : sig (fun oun : sig (fun oo : SgOp G => sig (fun u : MonUnit G => Negate G)) => @IsGroup G oun.1 oun.2.1 oun.2.2) => (x.1.1 ; x.1.2.1 ; x.1.2.2 ; x.2))
                   ((op;unit;neg);ax) ((op';unit';neg');ax') _).
      apply path_sigma_hprop; cbn.
      srefine (path_sigma' _ _ _).
      { apply path_arrow; intros x; apply path_arrow; intros y; apply eq. }
      rewrite transport_const.
      srefine (path_sigma' _ _ _).
      { apply eq. }
      rewrite transport_const.
      apply path_arrow; intros x.
      exact (preserves_negate x). }
  refine (_ oE (issig_GroupIsomorphism G H)^-1).
  refine (_ oE (equiv_functor_sigma' (issig_GroupHomomorphism G H) (fun f => 1%equiv))^-1).
  refine (equiv_functor_sigma' (issig_equiv G H) (fun f => 1%equiv) oE _).
  cbn.
  refine (equiv_adjointify (fun f => (exist (IsMonoidPreserving o pr1) (exist IsEquiv f.1.1 f.2) f.1.2))
                           (fun f => (exist (IsEquiv o pr1) (exist IsMonoidPreserving f.1.1 f.2) f.1.2))
                           _ _); intros [[f f1] f2]; reflexivity.
Defined.  

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

