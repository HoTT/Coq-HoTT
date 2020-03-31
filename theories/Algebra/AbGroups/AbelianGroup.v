Require Import HoTT.Basics HoTT.Types.
Require Import Truncations.
Require Import HIT.Coeq.
Require Export Algebra.Groups.
Require Import Cubical.
Require Import WildCat.

Local Open Scope mc_mult_scope.

(** * Abelian groups *)

(** Definition of an abelian group *)

Class AbGroup := {
  abgroup_type : Type;
  abgroup_sgop :> SgOp abgroup_type;
  abgroup_unit :> MonUnit abgroup_type;
  abgroup_inverse :> Negate abgroup_type;
  abgroup_isabgroup :> IsAbGroup abgroup_type;
}.

Definition Build_AbGroup' (G : Group) `{IsAbGroup G} : AbGroup
  := Build_AbGroup G _ _ _ _.

Existing Instance abgroup_sgop.
Existing Instance abgroup_unit.
Existing Instance abgroup_inverse.
Existing Instance abgroup_isabgroup.

(** We want abelian groups to be coerced to the underlying type. *)
Coercion abgroup_type : AbGroup >-> Sortclass.

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

(** Now we finally check that our definition of abelianization satisfies the universal property of being an abelianization. *)

(** We define abel to be the abelianization of a group. This is a map from Group to AbGroup. *)
Definition abel : Group -> AbGroup.
Proof.
  intro G.
  srapply (Build_AbGroup (Abel G)).
Defined.

(** The unit of this map is the map ab which typeclasses can pick up to be a homomorphism. We write it out explicitly here. *)
Definition abel_unit (X : Group)
  : GroupHomomorphism X (abel X).
Proof.
  snrapply @Build_GroupHomomorphism.
  + exact ab.
  + exact _.
Defined.

(** Finally we can prove that our construction abel is an abelianization. *)
Global Instance isabelianization_abel {G : Group}
  : IsAbelianization (abel G) (abel_unit G).
Proof.
  intros A. constructor.
  { intros h. srefine (_;_).
    { snrapply @Build_GroupHomomorphism.
      { srapply (Abel_rec _ _ h).
        intros x y z.
        refine (grp_homo_op _ _ _ @ _ @ (grp_homo_op _ _ _)^).
        apply (ap (_ *.)).
        refine (grp_homo_op _ _ _ @ _ @ (grp_homo_op _ _ _)^).
        apply commutativity. }
      intros y.
      Abel_ind_hprop x; revert y.
      Abel_ind_hprop y.
      apply grp_homo_op. }
    cbn. reflexivity. }
  intros g h p.
  Abel_ind_hprop x.
  exact (p x).
Defined.

Theorem groupiso_isabelianization {G : Group}
  (A B : AbGroup)
  (eta1 : GroupHomomorphism G A)
  (eta2 : GroupHomomorphism G B)
  {isab1 : IsAbelianization A eta1}
  {isab2 : IsAbelianization B eta2}
  : GroupIsomorphism A B.
Proof.
  destruct (esssurj (group_precomp B eta1) eta2) as [a ac].
  destruct (esssurj (group_precomp A eta2) eta1) as [b bc].
  srapply (Build_GroupIsomorphism _ _ a).
  srapply (isequiv_adjointify _ b).
  { refine (essinj0 (group_precomp B eta2)
                    (x := a $o b) (y := Id (A := Group) B) _).
    intros x; cbn in *.
    refine (_ @ ac x).
    apply ap, bc. }
  { refine (essinj0 (group_precomp A eta1)
                    (x := b $o a) (y := Id (A := Group) A) _).
    intros x; cbn in *.
    refine (_ @ bc x).
    apply ap, ac. }
Defined.

Theorem homotopic_isabelianization {G : Group} (A B : AbGroup)
  (eta1 : GroupHomomorphism G A) (eta2 : GroupHomomorphism G B)
  {isab1 : IsAbelianization A eta1} {isab2 : IsAbelianization B eta2}
  : eta2 == grp_homo_compose (groupiso_isabelianization A B eta1 eta2) eta1.
Proof.
  intros x.
  exact (((esssurj (group_precomp B eta1) eta2).2 x)^).
Defined.

(** Hence any abelianization is surjective. *)
Global Instance issurj_isabelianization {G : Group}
  (A : AbGroup) (eta : GroupHomomorphism G A)
  : IsAbelianization A eta -> IsSurjection eta.
Proof.
  intros k.
  pose (homotopic_isabelianization A (abel G) eta (abel_unit G)) as p.
  refine (@cancelR_isequiv_conn_map _ _ _ _ _ _ _
    (conn_map_homotopic _ _ _ p _)).
Defined.

Global Instance isabelianization_identity (A : AbGroup) : IsAbelianization A grp_homo_id.
Proof.
  intros B. constructor.
  - intros h; exact (h ; fun _ => idpath).
  - intros g h p; exact p.
Defined.

Global Instance isequiv_abgroup_abelianization
  (A B : AbGroup) (eta : GroupHomomorphism A B) {isab : IsAbelianization B eta}
  : IsEquiv eta.
Proof.
  srapply isequiv_homotopic.
  - srapply (groupiso_isabelianization A B grp_homo_id eta).
  - exact _.
  - symmetry; apply homotopic_isabelianization.
Defined.

(** The wild category of abelian groups *)

Global Instance isgraph_abgroup : IsGraph AbGroup
  := induced_graph group_abgroup.

Global Instance is01cat_AbGroup : Is01Cat AbGroup
  := induced_01cat group_abgroup.
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

Global Instance is01cat_GroupHomomorphism {A B : AbGroup} : Is01Cat (A $-> B)
  := induced_01cat (@grp_homo_map A B).

Global Instance is0gpd_GroupHomomorphism {A B : AbGroup}: Is0Gpd (A $-> B)
  := induced_0gpd (@grp_homo_map A B).
(** Quotients of abelian groups *)

(** AbGroup forms a 1Cat *)
Global Instance is1cat_abgroup : Is1Cat AbGroup
  := induced_1cat _.

Instance hasmorext_abgroup `{Funext} : HasMorExt AbGroup
  := induced_hasmorext _.

Global Instance hasequivs_abgroup : HasEquivs AbGroup
  := induced_hasequivs _.

(** Zero object of AbGroup *)
Definition TrivialAbGroup : AbGroup.
Proof.
  refine (Build_AbGroup Unit (fun _ _ => tt) tt (fun _ => tt) _).
  repeat split; try exact _; by intros [].
Defined.

(** AbGroup is a pointed category *)
Global Instance ispointedcat_abgroup : IsPointedCat AbGroup.
Proof.
  snrapply Build_IsPointedCat.
  1: exact TrivialAbGroup.
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

Definition TrivialAbGroup : AbGroup.
Proof.
  refine (Build_AbGroup Unit (fun _ _ => tt) tt (fun _ => tt) _).
  repeat split; try exact _; by intros [].
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

