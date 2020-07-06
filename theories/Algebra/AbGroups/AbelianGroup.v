Require Import HoTT.Basics HoTT.Types.
Require Import Truncations.
Require Import HIT.Coeq.
Require Export Algebra.Groups.
Require Import Cubical.
Require Import WildCat.

Local Open Scope mc_mult_scope.

(** * Abelian groups *)

(** Definition of an abelian group *)

Record AbGroup := {
  abgroup_type : Type;
  abgroup_sgop : SgOp abgroup_type;
  abgroup_unit : MonUnit abgroup_type;
  abgroup_inverse : Negate abgroup_type;
  abgroup_isabgroup : IsAbGroup abgroup_type;
}.

Existing Instances abgroup_sgop abgroup_unit abgroup_inverse abgroup_isabgroup.

(** We want abelian groups to be coerced to the underlying type. *)
Coercion abgroup_type : AbGroup >-> Sortclass.

Definition Build_AbGroup' (G : Group) {H : Commutative (@group_sgop G)} : AbGroup.
Proof.
  srapply (Build_AbGroup G).
  4: split.
  1-5: exact _.
Defined.

(** The underlying group of an abelian group. *)
Definition group_abgroup : AbGroup -> Group.
Proof.
  intros [G ? ? ? [l ?]].
  nrapply (Build_Group G _ _ _ l).
Defined.

(** We also want abelian groups to be coerced to the underlying group. *)
Coercion group_abgroup : AbGroup >-> Group.

(** ** Subgroups of abelian groups *)

(** Subgroups of abelian groups are abelian *)
Global Instance isabgroup_subgroup (G : AbGroup) (H : Subgroup G)
  : IsAbGroup H.
Proof.
  nrapply Build_IsAbGroup.
  1: exact _.
  intros x y.
  apply (injective issubgroup_incl).
  refine (_ @ _ @ _^).
  1,3: apply grp_homo_op.
  apply commutativity.
Defined.

Global Instance isnormal_ab_subgroup (G : AbGroup) (H : Subgroup G)
  : IsNormalSubgroup H.
Proof.
  intros x y.
  unfold in_cosetL, in_cosetR.
  refine (equiv_functor_sigma' (Build_Equiv _ _ group_inverse _) _).
  intros h; simpl.
  srapply equiv_iff_hprop.
  + intros p.
    rewrite grp_homo_inv.
    rewrite p.
    rewrite negate_sg_op.
    rewrite (involutive x).
    apply commutativity.
  + intros p.
    rewrite grp_homo_inv in p.
    apply moveL_equiv_V in p.
    rewrite p; cbn.
    change (- (x * -y) = - x * y).
    rewrite negate_sg_op.
    rewrite (involutive y).
    apply commutativity.
Defined.

(** Quotients of abelian groups *)

Global Instance isabgroup_quotient (G : AbGroup) (H : Subgroup G)
  : IsAbGroup (QuotientGroup G H).
Proof.
  nrapply Build_IsAbGroup.
  1: exact _.
  intro x.
  srapply Quotient_ind_hprop.
  intro y; revert x.
  srapply Quotient_ind_hprop.
  intro x.
  apply (ap (tr o coeq)).
  apply commutativity.
Defined.

Definition QuotientAbGroup (G : AbGroup) (H : Subgroup G)
  : AbGroup := Build_AbGroup (QuotientGroup G H) _ _ _ _.

(** The wild category of abelian groups *)

Global Instance isgraph_abgroup : IsGraph AbGroup
  := induced_graph group_abgroup.

Global Instance is01cat_AbGroup : Is01Cat AbGroup
  := induced_01cat group_abgroup.

Global Instance is01cat_GroupHomomorphism {A B : AbGroup} : Is01Cat (A $-> B)
  := induced_01cat (@grp_homo_map A B).

Global Instance is0gpd_GroupHomomorphism {A B : AbGroup}: Is0Gpd (A $-> B)
  := induced_0gpd (@grp_homo_map A B).

(** AbGroup forms a 1Cat *)
Global Instance is1cat_abgroup : Is1Cat AbGroup
  := induced_1cat _.

Instance hasmorext_abgroup `{Funext} : HasMorExt AbGroup
  := induced_hasmorext _.

Global Instance hasequivs_abgroup : HasEquivs AbGroup
  := induced_hasequivs _.

(** Zero object of AbGroup *)

Definition abgroup_trivial : AbGroup.
Proof.
  rapply (Build_AbGroup' grp_trivial).
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
    exact (grp_homo_unit g). }
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
  := Build_AbGroup (grp_image f) _ _ _ _.

(** First isomorphism theorem of abelian groups *)
Definition abgroup_first_iso `{Funext} {A B : AbGroup} (f : A $-> B)
  : GroupIsomorphism (QuotientAbGroup A (grp_kernel f)) (abgroup_image f).
Proof.
  etransitivity.
  2: rapply grp_first_iso.
  apply grp_iso_quotient_normal.
Defined.

