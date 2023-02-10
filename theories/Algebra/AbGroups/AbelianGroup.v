Require Export Algebra.Groups.Group.
Require Export Algebra.Groups.Subgroup.
Require Import Algebra.Groups.QuotientGroup.
Require Import WildCat.

Local Set Polymorphic Inductive Cumulativity.

Local Open Scope mc_add_scope.

(** * Abelian groups *)

(** Definition of an abelian group *)

Record AbGroup := {
  abgroup_group : Group;
  abgroup_commutative : Commutative (@group_sgop abgroup_group);
}.

Coercion abgroup_group : AbGroup >-> Group.
Global Existing Instance abgroup_commutative.

Global Instance isabgroup_abgroup {A : AbGroup} : IsAbGroup A.
Proof.
  split; exact _.
Defined.

Definition issig_abgroup : _ <~> AbGroup := ltac:(issig).

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

(** Subgroups of abelian groups are abelian *)
Global Instance isabgroup_subgroup (G : AbGroup) (H : Subgroup G)
  : IsAbGroup H.
Proof.
  nrapply Build_IsAbGroup.
  1: exact _.
  intros x y.
  apply path_sigma_hprop.
  cbn. apply commutativity.
Defined.

Global Instance isnormal_ab_subgroup (G : AbGroup) (H : Subgroup G)
  : IsNormalSubgroup H.
Proof.
  intros x y; unfold in_cosetL, in_cosetR.
  refine (_ oE equiv_subgroup_inverse _ _).
  rewrite negate_sg_op.
  rewrite negate_involutive.
  by rewrite (commutativity (-y) x).
Defined.

(** ** Quotients of abelian groups *)

Global Instance isabgroup_quotient (G : AbGroup) (H : Subgroup G)
  : IsAbGroup (QuotientGroup' G H (isnormal_ab_subgroup G H)).
Proof.
  nrapply Build_IsAbGroup.
  1: exact _.
  intro x.
  srapply Quotient_ind_hprop.
  intro y; revert x.
  srapply Quotient_ind_hprop.
  intro x.
  apply (ap (class_of _)).
  apply commutativity.
Defined.

Definition QuotientAbGroup (G : AbGroup) (H : Subgroup G) : AbGroup
  := (Build_AbGroup (QuotientGroup' G H (isnormal_ab_subgroup G H)) _).

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

Global Instance isgraph_abgroup : IsGraph AbGroup
  := isgraph_induced abgroup_group.

Global Instance is01cat_abgroup : Is01Cat AbGroup
  := is01cat_induced abgroup_group.

Global Instance is01cat_grouphomomorphism {A B : AbGroup} : Is01Cat (A $-> B)
  := is01cat_induced (@grp_homo_map A B).

Global Instance is0gpd_grouphomomorphism {A B : AbGroup} : Is0Gpd (A $-> B)
  := is0gpd_induced (@grp_homo_map A B).

Global Instance is2graph_abgroup : Is2Graph AbGroup
  := is2graph_induced abgroup_group.

(** AbGroup forms a 1Cat *)
Global Instance is1cat_abgroup : Is1Cat AbGroup
  := is1cat_induced _.

Global Instance hasmorext_abgroup `{Funext} : HasMorExt AbGroup
  := hasmorext_induced _.

Global Instance hasequivs_abgroup@{u v} : HasEquivs@{v u u u u} AbGroup@{u}
  := hasequivs_induced _.

(** Zero object of AbGroup *)

Definition abgroup_trivial : AbGroup.
Proof.
  rapply (Build_AbGroup grp_trivial).
  by intros [].
Defined.

(** AbGroup is a pointed category *)
Global Instance ispointedcat_abgroup : IsPointedCat AbGroup.
Proof.
  snrapply Build_IsPointedCat.
  1: exact abgroup_trivial.
  { intro A.
    snrefine (Build_GroupHomomorphism (fun _ => mon_unit); _).
    1: exact _.
    { intros [] [].
      symmetry.
      apply left_identity. }
    intros g []; cbn.
    exact (grp_homo_unit g)^. }
  intro A.
  snrefine (Build_GroupHomomorphism (fun _ => mon_unit); _).
  1: exact _.
  { intros x y; symmetry.
    apply left_identity. }
  intros g x; cbn.
  apply path_unit.
Defined.

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
  snrapply Build_GroupIsomorphism.
  - snrapply Build_GroupHomomorphism.
    + exact (fun a => -a).
    + intros x y.
      refine (grp_inv_op x y @ _).
      apply commutativity.
  - srapply isequiv_adjointify.
    1: exact (fun a => -a).
    1-2: exact negate_involutive.
Defined.

(** Multiplication by [n : nat] defines an endomorphism of any abelian group [A]. *)
Definition ab_mul_nat {A : AbGroup} (n : nat) : GroupHomomorphism A A.
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact (fun a => grp_pow a n).
  intros a b.
  induction n; cbn.
  1: exact (grp_unit_l _)^.
  refine (_ @ associativity _ _ _).
  refine (_ @ ap _ (associativity _ _ _)^).
  rewrite (commutativity (grp_pow a n) b).
  refine (_ @ ap _ (associativity _ _ _)).
  refine (_ @ (associativity _ _ _)^).
  apply grp_cancelL.
  assumption.
Defined.

Definition ab_mul_nat_homo {A B : AbGroup}
  (f : GroupHomomorphism A B) (n : nat)
  : f o ab_mul_nat n == ab_mul_nat n o f
  := grp_pow_homo f n.

(** The image of an inclusion is a normal subgroup. *)
Definition ab_image_embedding {A B : AbGroup} (f : A $-> B) `{IsEmbedding f} : NormalSubgroup B
  := {| normalsubgroup_subgroup := grp_image_embedding f; normalsubgroup_isnormal := _ |}.

Definition ab_image_in_embedding {A B : AbGroup} (f : A $-> B) `{IsEmbedding f}
  : GroupIsomorphism A (ab_image_embedding f)
  := grp_image_in_embedding f.

(** The cokernel of a homomorphism into an abelian group. *)
Definition ab_cokernel {G : Group} {A : AbGroup} (f : GroupHomomorphism G A)
  : AbGroup := QuotientAbGroup _ (grp_image f).

Definition ab_cokernel_embedding {G : Group} {A : AbGroup} (f : G $-> A)
  `{IsEmbedding f} : AbGroup := QuotientAbGroup _ (grp_image_embedding f).
