From HoTT Require Import Basics Types.
Require Import Truncations.Core.
Require Import Algebra.Congruence.
Require Import Algebra.Groups.Group.
Require Import Algebra.Groups.Subgroup.
Require Export Colimits.Quotient.
Require Import HSet.
Require Import Spaces.Finite.Finite.
From HoTT.WildCat Require Import Core Equiv.
Require Import Modalities.Modality.

(** * Quotient groups *)

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.
Local Open Scope wc_iso_scope.

(** ** Congruence quotients *)

Section GroupCongruenceQuotient.

  (** A congruence on a group is a relation satisfying [R x x' -> R y y' -> R (x * y) (x' * y')].  Because we also require that [R] is reflexive, we also know that [R y y' -> R (x * y) (x * y')] for any [x], and similarly for multiplication on the right by [x].  We don't need to assume that [R] is symmetric or transitive. *)
  Context {G : Group} {R : Relation G} `{!IsCongruence R, !Reflexive R}.

  (** The type underlying the quotient group is [Quotient R]. *)
  Definition CongruenceQuotient := G / R.

  #[export] Instance congquot_sgop : SgOp CongruenceQuotient.
  Proof.
    srapply Quotient_rec2.
    - intros x y.
      exact (class_of _ (x * y)).
    - intros x x' y p. apply qglue. by apply iscong.
    - intros x y y' q. apply qglue. by apply iscong.
  Defined.

  #[export] Instance congquot_mon_unit : MonUnit CongruenceQuotient.
  Proof.
    apply class_of, mon_unit.
  Defined.

  #[export] Instance congquot_inverse : Inverse CongruenceQuotient.
  Proof.
    srapply Quotient_rec.
    1: exact (class_of R o (^)).
    intros x y p; cbn beta.
    transitivity (class_of R (y^ * (y * x^))).
    - rewrite grp_assoc.
      rewrite grp_inv_l.
      rewrite grp_unit_l.
      reflexivity.
    - transitivity (class_of R (y^ * (x * x^))).
      + symmetry; apply qglue; repeat apply iscong.
        1,3: reflexivity.
        exact p.
      + rewrite grp_inv_r.
        rewrite grp_unit_r.
        reflexivity.
  Defined.

  #[export] Instance congquot_sgop_associative : Associative congquot_sgop.
  Proof.
    srapply Quotient_ind3_hprop; intros x y z.
    snapply (ap (class_of R)).
    rapply associativity.
  Defined.
  Global Opaque congquot_sgop_associative.

  #[export] Instance issemigroup_congquot : IsSemiGroup CongruenceQuotient := {}.

  #[export] Instance congquot_leftidentity : LeftIdentity (.*.) mon_unit.
  Proof.
    srapply Quotient_ind_hprop; intro x.
    snapply (ap (class_of R)).
    rapply left_identity.
  Defined.
  Global Opaque congquot_leftidentity.

  #[export] Instance congquot_rightidentity : RightIdentity (.*.) mon_unit.
  Proof.
    srapply Quotient_ind_hprop; intro x.
    snapply (ap (class_of R)).
    rapply right_identity.
  Defined.
  Global Opaque congquot_rightidentity.

  #[export] Instance ismonoid_quotientgroup : IsMonoid CongruenceQuotient := {}.

  #[export] Instance quotientgroup_leftinverse : LeftInverse (.*.) (^) mon_unit.
  Proof.
    srapply Quotient_ind_hprop; intro x; cbn beta.
    snapply (ap (class_of R)).
    rapply left_inverse.
  Defined.
  Global Opaque quotientgroup_leftinverse.

  #[export] Instance quotientgroup_rightinverse : RightInverse (.*.) (^) mon_unit.
  Proof.
    srapply Quotient_ind_hprop; intro x; cbn beta.
    snapply (ap (class_of R)).
    rapply right_inverse.
  Defined.
  Global Opaque quotientgroup_rightinverse.

  #[export] Instance isgroup_quotientgroup : IsGroup CongruenceQuotient := {}.

End GroupCongruenceQuotient.

(** ** Sets of cosets *)

Section Cosets.

  Context (G : Group) (H : Subgroup G).

  Definition LeftCoset := G / in_cosetL H.

  (** TODO: Way too many universes, needs fixing *)
  (** The set of left cosets of a finite subgroup of a finite group is finite. *)
  #[export] Instance finite_leftcoset `{Univalence, Finite G, Finite H}
    : Finite LeftCoset.
  Proof.
    napply finite_quotient.
    1-5: exact _.
    intros x y.
    apply (detachable_finite_subset H).
  Defined.

  (** The index of a subgroup is the number of cosets of the subgroup. *)
  Definition subgroup_index `{Univalence, Finite G, Finite H} : nat
    := fcard LeftCoset.

  Definition RightCoset := G / in_cosetR H.

  (** The set of left cosets is equivalent to the set of right coset. *)
  Definition equiv_leftcoset_rightcoset
    : LeftCoset <~> RightCoset.
  Proof.
    snapply equiv_quotient_functor.
    - exact inv.
    - exact _.
    - intros x y; simpl.
      by rewrite grp_inv_inv.
  Defined.

  (** The set of right cosets of a finite subgroup of a finite group is finite since it is equivalent to the set of left cosets. *)
  #[export] Instance finite_rightcoset `{Univalence, Finite G, Finite H}
    : Finite RightCoset.
  Proof.
    napply finite_equiv'.
    1: exact equiv_leftcoset_rightcoset.
    exact _.
  Defined.

End Cosets.

(** ** Quotient groups *)

(** Now we can define the quotient group by a normal subgroup. *)

Section QuotientGroup.

  Context (G : Group) (N : NormalSubgroup G).

  #[export] Instance iscongruence_in_cosetL : IsCongruence (in_cosetL N).
  Proof.
    srapply Build_IsCongruence.
    intros; by apply in_cosetL_cong.
  Defined.

  #[export] Instance iscongruence_in_cosetR: IsCongruence (in_cosetR N).
  Proof.
    srapply Build_IsCongruence.
    intros; by apply in_cosetR_cong.
  Defined.

  (** Now we have to make a choice whether to pick the left or right cosets. Due to existing convention we shall pick left cosets but we note that we could equally have picked right. *)
  Definition QuotientGroup : Group
    := Build_Group (LeftCoset G N) _ _ _ _.

  Definition grp_quotient_map : G $-> QuotientGroup.
  Proof.
    snapply Build_GroupHomomorphism.
    1: exact (class_of _).
    intros ??; reflexivity.
  Defined.

  Definition grp_quotient_rec {A : Group} (f : G $-> A)
             (h : forall n : G, N n -> f n = mon_unit)
    : QuotientGroup $-> A.
  Proof.
    snapply Build_GroupHomomorphism.
    - srapply Quotient_rec.
      + exact f.
      + cbn; intros x y n.
        apply grp_moveR_M1.
        rhs_V napply (ap (.* f y) (grp_homo_inv _ _)).
        rhs_V napply grp_homo_op.
        symmetry; apply h; assumption.
    - intro x.
      refine (Quotient_ind_hprop _ _ _).
      intro y. revert x.
      refine (Quotient_ind_hprop _ _ _).
      intro x; simpl.
      apply grp_homo_op.
  Defined.

  Definition grp_quotient_ind_hprop (P : QuotientGroup -> Type)
    `{forall x, IsHProp (P x)}
    (H1 : forall x, P (grp_quotient_map x))
    : forall x, P x.
  Proof.
    srapply Quotient_ind_hprop.
    exact H1.
  Defined.

End QuotientGroup.

Arguments QuotientGroup G N : simpl never.
Arguments grp_quotient_map {_ _}.

Notation "G / N" := (QuotientGroup G N) : group_scope.

(** Rephrasing that lets you specify the normality proof *)
Definition QuotientGroup' (G : Group) (N : Subgroup G) (H : IsNormalSubgroup N)
  := QuotientGroup G (Build_NormalSubgroup G N H).

Local Open Scope group_scope.

(** Computation rule for [grp_quotient_rec]. *)
Corollary grp_quotient_rec_beta `{F : Funext} {G : Group}
          (N : NormalSubgroup G) (H : Group)
          {A : Group} (f : G $-> A)
          (h : forall n:G, N n -> f n = mon_unit)
  : (grp_quotient_rec G N f h) $o grp_quotient_map = f.
Proof.
  apply equiv_path_grouphomomorphism; reflexivity.
Defined.

(** Computation rule for [grp_quotient_rec]. *)
Definition grp_quotient_rec_beta' {G : Group}
          (N : NormalSubgroup G) (H : Group)
          {A : Group} (f : G $-> A)
          (h : forall n:G, N n -> f n = mon_unit)
  : (grp_quotient_rec G N f h) $o grp_quotient_map == f
    := fun _ => idpath.

(** The proof of normality is irrelevant up to equivalence. It is unfortunate that it doesn't hold definitionally. *)
Definition grp_iso_quotient_normal (G : Group) (H : Subgroup G)
  {k k' : IsNormalSubgroup H}
  : QuotientGroup' G H k ≅ QuotientGroup' G H k'.
Proof.
  snapply Build_GroupIsomorphism'.
  1: reflexivity.
  intro x.
  srapply Quotient_ind_hprop; intro y; revert x.
  srapply Quotient_ind_hprop; intro x.
  reflexivity.
Defined.

(** The universal mapping property for groups *)
Theorem equiv_grp_quotient_ump {F : Funext} {G : Group} (N : NormalSubgroup G) (H : Group)
  : {f : G $-> H & forall (n : G), N n -> f n = mon_unit}
    <~> (G / N $-> H).
Proof.
  srapply equiv_adjointify.
  - intros [f p].
    exact (grp_quotient_rec _ _ f p).
  - intro f.
    exists (f $o grp_quotient_map).
    intros n h; cbn.
    refine (_ @ grp_homo_unit f).
    apply ap.
    apply qglue; cbn.
    rewrite right_identity;
      by apply issubgroup_in_inv.
  - intros f.
    rapply equiv_path_grouphomomorphism.
      by srapply Quotient_ind_hprop.
  - intros [f p].
    srapply path_sigma_hprop; simpl.
    exact (grp_quotient_rec_beta N H f p).
Defined.

Section FirstIso.

  Context `{Funext} {A B : Group} (phi : A $-> B).

  (** First we define a map from the quotient by the kernel of phi into the image of phi *)
  Definition grp_image_quotient
    : A / grp_kernel phi $-> grp_image phi.
  Proof.
    srapply grp_quotient_rec.
    + srapply grp_homo_image_in.
    + intros n x.
      by apply path_sigma_hprop.
  Defined.

  (** The underlying map of this homomorphism is an equivalence *)
  #[export] Instance isequiv_grp_image_quotient
    : IsEquiv grp_image_quotient.
  Proof.
    snapply isequiv_surj_emb.
    1: srapply cancelR_conn_map.
    srapply isembedding_isinj_hset.
    srapply Quotient_ind2_hprop.
    intros x y h; simpl in h.
    apply qglue; cbn.
    apply (equiv_path_sigma_hprop _ _)^-1%equiv in h; cbn in h.
    cbn. rewrite grp_homo_op, grp_homo_inv, h.
    apply grp_inv_l.
  Defined.

  (** First isomorphism theorem for groups *)
  Theorem grp_first_iso : A / grp_kernel phi ≅ grp_image phi.
  Proof.
    exact (Build_GroupIsomorphism _ _ grp_image_quotient _).
  Defined.

End FirstIso.

(** Quotient groups are finite. *)
(** Note that we cannot constructively conclude that the normal subgroup [H] must be finite since [G] is, therefore we keep it as an assumption. *)
Instance finite_quotientgroup {U : Univalence} (G : Group) (H : NormalSubgroup G)
  (fin_G : Finite G) (fin_H : Finite H)
  : Finite (QuotientGroup G H).
Proof.
  napply finite_quotient.
  1-5: exact _.
  intros x y.
  pose (dec_H := detachable_finite_subset H).
  apply dec_H.
Defined.

Definition grp_kernel_quotient_iso `{Univalence} {G : Group} (N : NormalSubgroup G)
  : GroupIsomorphism N (grp_kernel (@grp_quotient_map G N)).
Proof.
  srapply Build_GroupIsomorphism.
  - srapply (grp_kernel_corec (subgroup_incl N)).
    intro x; cbn.
    apply qglue.
    apply issubgroup_in_op.
    + exact (issubgroup_in_inv _ x.2).
    + exact issubgroup_in_unit.
  - apply isequiv_surj_emb.
    2: exact (cancelL_isembedding (g:=pr1)).
    intros [g p].
    rapply contr_inhabited_hprop.
    srefine (tr ((g; _); _)).
    + rewrite <- grp_unit_l, <- inverse_mon_unit.
      apply (related_quotient_paths (fun x y => N (x^ * y))).
      exact p^%path.
    + srapply path_sigma_hprop.
      reflexivity.
Defined.

(** When the normal subgroup [N] is trivial, the inclusion map [G $-> G / N] is an isomorphism. *)
Instance catie_grp_quotient_map_trivial {G : Group} (N : NormalSubgroup G)
  (triv : IsTrivialGroup N)
  : CatIsEquiv (@grp_quotient_map G N).
Proof.
  snapply catie_adjointify.
  - srapply (grp_quotient_rec _ _ (Id _)).
    exact triv.
  - by srapply grp_quotient_ind_hprop.
  - reflexivity.
Defined.

(** The group quotient by a trivial group is isomorphic to the original group. *)
Definition grp_quotient_trivial (G : Group) (N : NormalSubgroup G)
  (triv : IsTrivialGroup N)
  : G $<~> G / N
  := Build_CatEquiv grp_quotient_map.

(** A quotient by a maximal subgroup is trivial. *)
Instance istrivial_grp_quotient_maximal
  (G : Group) (N : NormalSubgroup G)
  : IsMaximalSubgroup N -> IsTrivialGroup (G / N).
Proof.
  intros max x _; revert x.
  rapply grp_quotient_ind_hprop.
  intros x.
  apply qglue, max.
Defined.

(** Conversely, a trivial quotient means the subgroup is maximal. *)
Definition ismaximalsubgroup_istrivial_grp_quotient `{Univalence}
  (G : Group) (N : NormalSubgroup G)
  : IsTrivialGroup (G / N) -> IsMaximalSubgroup N.
Proof.
  intros triv x.
  specialize (triv (grp_quotient_map x) tt).
  simpl in triv.
  apply related_quotient_paths in triv.
  2-5: exact _.
  apply equiv_subgroup_inv.
  napply (subgroup_in_op_l _ _ 1 triv) .
  apply subgroup_in_unit.
Defined.
