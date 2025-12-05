From HoTT Require Import Basics Types.
Require Import Spaces.Nat.Core Spaces.Int.
Require Export Classes.interfaces.canonical_names (Zero, zero, Plus, plus, Negate, negate, Involutive, involutive).
Require Export Classes.interfaces.abstract_algebra (IsAbGroup(..), abgroup_group, abgroup_commutative).
Require Export Algebra.Groups.Group.
Require Export Algebra.Groups.Subgroup.
Require Import Algebra.Groups.QuotientGroup.
Require Import WildCat.

Local Set Polymorphic Inductive Cumulativity.

Local Open Scope mc_scope.
Local Open Scope mc_add_scope.

(** * Abelian groups *)

(** Definition of an abelian group *)

Record AbGroup := {
  abgroup_group : Group;
  abgroup_commutative :: @Commutative abgroup_group _ (+);
}.

Coercion abgroup_group : AbGroup >-> Group.

Definition zero_abgroup (A : AbGroup) : Zero A := mon_unit.
Definition negate_abgroup (A : AbGroup) : Negate A := inv.
Definition plus_abgroup (A : AbGroup) : Plus A := sg_op.

(** Sometimes we want an abelian group to act as if it has a [Plus], [Zero] and [Negate] operation. For example, when working with rings. We therefore make this module of hints available for import so that consumers can control the way the abelian group operation is treated.

Files about abelian groups (apart from this one) typically don't have these instances available, whereas files about rings do. *)
Module Import AdditiveInstances.
  #[export] Hint Immediate zero_abgroup : typeclass_instances.
  #[export] Hint Immediate negate_abgroup : typeclass_instances.
  #[export] Hint Immediate plus_abgroup : typeclass_instances.
End AdditiveInstances.

Instance isabgroup_abgroup {A : AbGroup} : IsAbGroup A.
Proof.
  split; exact _.
Defined.

(** Easier way to build abelian groups without redundant information. *)
Definition Build_AbGroup' (G : Type)
  `{MonUnit G, Inverse G, SgOp G, IsHSet G}
  (comm : Commutative (A:=G) (+))
  (assoc : Associative (A:=G) (+))
  (unit_l : LeftIdentity (A:=G) (+) 0)
  (inv_l : LeftInverse (A:=G) (+) (-) 0)
  : AbGroup.
Proof.
  snapply Build_AbGroup.
  - rapply (Build_Group' G).
  - exact comm.
Defined.

Definition issig_abgroup : _ <~> AbGroup := ltac:(issig).

Definition ab_neg_op {A : AbGroup} (x y : A) : - (x + y) = -x - y.
Proof.
  lhs napply grp_inv_op.
  apply commutativity.
Defined.

(** ** Paths between abelian groups *)

Definition equiv_path_abgroup `{Univalence} {A B : AbGroup@{u}}
  : GroupIsomorphism A B <~> (A = B).
Proof.
  refine (equiv_ap_inv issig_abgroup _ _ oE _).
  refine (equiv_path_sigma_hprop _ _ oE _).
  exact equiv_path_group.
Defined.

Definition equiv_path_abgroup_group `{Univalence} {A B : AbGroup}
  : (A = B :> AbGroup) <~> (A = B :> Group)
  := equiv_path_group oE equiv_path_abgroup^-1.

(** ** Subgroups of abelian groups *)

Local Hint Immediate canonical_names.inverse_is_negate : typeclass_instances.

(** Subgroups of abelian groups are abelian *)
Instance isabgroup_subgroup (G : AbGroup) (H : Subgroup G)
  : IsAbGroup H.
Proof.
  napply Build_IsAbGroup.
  1: exact _.
  intros x y.
  apply path_sigma_hprop.
  cbn. apply commutativity.
Defined.

(** Given any subgroup of an abelian group, we can coerce it to an abelian group. Note that Coq complains this coercion doesn't satisfy the uniform-inheritance condition, but in practice it works and doesn't cause any issue, so we ignore it. *)
Definition abgroup_subgroup (G : AbGroup) : Subgroup G -> AbGroup
  := fun H => Build_AbGroup H _.
#[warnings="-uniform-inheritance"]
Coercion abgroup_subgroup : Subgroup >-> AbGroup.

Instance isnormal_ab_subgroup (G : AbGroup) (H : Subgroup G)
  : IsNormalSubgroup H.
Proof.
  intros x y h.
  by rewrite commutativity.
Defined.

(** ** Quotients of abelian groups *)

Instance isabgroup_quotient (G : AbGroup) (H : Subgroup G)
  : IsAbGroup (QuotientGroup' G H (isnormal_ab_subgroup G H)).
Proof.
  napply Build_IsAbGroup.
  1: exact _.
  srapply Quotient_ind2_hprop; intros x y.
  apply (ap (class_of _)).
  apply commutativity.
Defined.

Definition QuotientAbGroup (G : AbGroup) (H : Subgroup G) : AbGroup
  := (Build_AbGroup (QuotientGroup' G H (isnormal_ab_subgroup G H)) _).

Arguments QuotientAbGroup G H : simpl never.

Definition quotient_abgroup_rec {G : AbGroup}
  (N : Subgroup G) (H : AbGroup)
  (f : GroupHomomorphism G H) (h : forall n : G, N n -> f n = mon_unit)
  : GroupHomomorphism (QuotientAbGroup G N) H
  := grp_quotient_rec G (Build_NormalSubgroup G N _) f h.

Theorem equiv_quotient_abgroup_ump {F : Funext} {G : AbGroup}
  (N : Subgroup G) (H : Group)
  : {f : GroupHomomorphism G H & forall (n : G), N n -> f n = mon_unit}
    <~> (GroupHomomorphism (QuotientAbGroup G N) H).
Proof.
  exact (equiv_grp_quotient_ump (Build_NormalSubgroup G N _) _).
Defined.

(** ** The wild category of abelian groups *)

Instance isgraph_abgroup : IsGraph AbGroup
  := isgraph_induced abgroup_group.

Instance is01cat_abgroup : Is01Cat AbGroup
  := is01cat_induced abgroup_group.

Instance is2graph_abgroup : Is2Graph AbGroup
  := is2graph_induced abgroup_group.

Instance isgraph_abgrouphomomorphism {A B : AbGroup} : IsGraph (A $-> B)
  := is2graph_induced abgroup_group A B.

Instance is01cat_abgrouphomomorphism {A B : AbGroup} : Is01Cat (A $-> B)
  := is01cat_induced (@grp_homo_map A B).

Instance is0gpd_abgrouphomomorphism {A B : AbGroup} : Is0Gpd (A $-> B)
  := is0gpd_induced (@grp_homo_map A B).

(** [AbGroup] forms a 1Cat *)
Instance is1cat_abgroup : Is1Cat AbGroup
  := is1cat_induced _.

Instance hasmorext_abgroup `{Funext} : HasMorExt AbGroup
  := hasmorext_induced _.

Instance hasequivs_abgroup : HasEquivs AbGroup
  := hasequivs_induced _.

(** Zero object of [AbGroup] *)

Definition abgroup_trivial : AbGroup.
Proof.
  rapply (Build_AbGroup grp_trivial).
  by intros [].
Defined.

(** [AbGroup] is a pointed category *)
Instance ispointedcat_abgroup : IsPointedCat AbGroup.
Proof.
  apply Build_IsPointedCat with abgroup_trivial.
  all: intro A; apply ispointedcat_group.
Defined.

(** [abgroup_group] is a functor *)
Instance is0functor_abgroup_group : Is0Functor abgroup_group
  := is0functor_induced _.

Instance is1functor_abgroup_group : Is1Functor abgroup_group
  := is1functor_induced _.

(** Image of group homomorphisms between abelian groups *)
Definition abgroup_image {A B : AbGroup} (f : A $-> B) : AbGroup
  := Build_AbGroup (grp_image f) _.

(** First isomorphism theorem of abelian groups *)
Definition abgroup_first_iso `{Funext} {A B : AbGroup} (f : A $-> B)
  : GroupIsomorphism (QuotientAbGroup A (grp_kernel f)) (abgroup_image f).
Proof.
  etransitivity.
  2: rapply grp_first_iso.
  apply grp_iso_quotient_normal.
Defined.

(** ** Kernels of abelian groups *)

Definition ab_kernel {A B : AbGroup} (f : A $-> B) : AbGroup
  := Build_AbGroup (grp_kernel f) _.

(** ** Transporting in families related to abelian groups *)

Lemma transport_abgrouphomomorphism_from_const `{Univalence} {A B B' : AbGroup}
      (p : B = B') (f : GroupHomomorphism A B)
  : transport (Hom A) p f
    = grp_homo_compose (equiv_path_abgroup^-1 p) f.
Proof.
  induction p.
  by apply equiv_path_grouphomomorphism.
Defined.

Lemma transport_iso_abgrouphomomorphism_from_const `{Univalence} {A B B' : AbGroup}
      (phi : GroupIsomorphism B B') (f : GroupHomomorphism A B)
  : transport (Hom A) (equiv_path_abgroup phi) f
    = grp_homo_compose phi f.
Proof.
  refine (transport_abgrouphomomorphism_from_const _ _ @ _).
  by rewrite eissect.
Defined.

Lemma transport_abgrouphomomorphism_to_const `{Univalence} {A A' B : AbGroup}
      (p : A = A') (f : GroupHomomorphism A B)
  : transport (fun G => Hom G B) p f
    = grp_homo_compose f (grp_iso_inverse (equiv_path_abgroup^-1 p)).
Proof.
  induction p; cbn.
  by apply equiv_path_grouphomomorphism.
Defined.

Lemma transport_iso_abgrouphomomorphism_to_const `{Univalence} {A A' B : AbGroup}
      (phi : GroupIsomorphism A A') (f : GroupHomomorphism A B)
  : transport (fun G => Hom G B) (equiv_path_abgroup phi) f
    = grp_homo_compose f (grp_iso_inverse phi).
Proof.
  refine (transport_abgrouphomomorphism_to_const _ _ @ _).
  by rewrite eissect.
Defined.

(** ** Operations on abelian groups *)

(** The negation automorphism of an abelian group *)
Definition ab_homo_negation {A : AbGroup} : GroupIsomorphism A A.
Proof.
  snapply Build_GroupIsomorphism.
  - snapply Build_GroupHomomorphism.
    + exact (fun a => -a).
    + intros x y.
      refine (grp_inv_op x y @ _).
      apply commutativity.
  - srapply isequiv_adjointify.
    1: exact (fun a => -a).
    1-2: exact inverse_involutive.
Defined.

(** Multiplication by [n : Int] defines an endomorphism of any abelian group [A]. *)
Definition ab_mul {A : AbGroup} (n : Int) : GroupHomomorphism A A.
Proof.
  snapply Build_GroupHomomorphism.
  1: exact (fun a => grp_pow a n).
  intros a b.
  apply grp_pow_mul, commutativity.
Defined.

(** [ab_mul n] is natural. *)
Definition ab_mul_natural {A B : AbGroup}
  (f : GroupHomomorphism A B) (n : Int)
  : f o ab_mul n == ab_mul n o f
  := grp_pow_natural f n.

(** The image of an inclusion is a normal subgroup. *)
Definition ab_image_embedding {A B : AbGroup} (f : A $-> B) `{IsEmbedding f} : NormalSubgroup B
  := {| normalsubgroup_subgroup := grp_image_embedding f; normalsubgroup_isnormal := _ |}.

Definition ab_image_in_embedding {A B : AbGroup} (f : A $-> B) `{IsEmbedding f}
  : GroupIsomorphism A (ab_image_embedding f)
  := grp_image_in_embedding f.

(** The cokernel of a homomorphism into an abelian group. *)
Definition ab_cokernel {G : Group@{u}} {A : AbGroup@{u}} (f : GroupHomomorphism G A)
  : AbGroup := QuotientAbGroup _ (grp_image f).

Definition ab_cokernel_embedding {G : Group} {A : AbGroup} (f : G $-> A) `{IsEmbedding f}
  : AbGroup := QuotientAbGroup _ (grp_image_embedding f).

Definition ab_cokernel_embedding_rec {G: Group} {A B : AbGroup} (f : G $-> A) `{IsEmbedding f}
  (h : A $-> B) (p : grp_homo_compose h f $== grp_homo_const)
  : ab_cokernel_embedding f $-> B.
Proof.
  snapply (grp_quotient_rec _ _ h).
  intros a [g q].
  induction q.
  exact (p g).
Defined.
