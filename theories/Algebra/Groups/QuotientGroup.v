Require Import HoTT.Basics HoTT.Types.
Require Import HSet.
Require Import Algebra.Groups.Group.
Require Import Algebra.Groups.Subgroup.
Require Import Algebra.Congruence.
Require Export Colimits.Quotient.
Require Export Algebra.Groups.Image.
Require Export Algebra.Groups.Kernel.
Require Import HSet.
Require Import WildCat.

(** * Quotient groups *)

Local Open Scope mc_mult_scope.

Section GroupCongruenceQuotient.

  Context {G : Group} {R : Relation G}
    `{is_mere_relation _ R} `{!IsCongruence R} (* Congruence just means respects op *)
    `{!Reflexive R} `{!Symmetric R} `{!Transitive R}.

  Definition CongruenceQuotient := G / R.

  Global Instance congquot_sgop : SgOp CongruenceQuotient.
  Proof.
    intros x.
    srapply Quotient_rec.
    { intro y; revert x.
      srapply Quotient_rec.
      { intros x.
        apply class_of.
        exact (x * y). }
      intros a b r.
      cbn.
      apply qglue.
      by apply iscong. }
    intros a b r.
    revert x.
    srapply Quotient_ind_hprop.
    intro x.
    apply qglue.
    by apply iscong.
  Defined.

  Global Instance congquot_mon_unit : MonUnit CongruenceQuotient.
  Proof.
    apply class_of, mon_unit.
  Defined.

  Global Instance congquot_negate : Negate CongruenceQuotient.
  Proof.
    srapply Quotient_functor.
    1: apply negate.
    intros x y p.
    rewrite <- (left_identity (-x)).
    destruct (left_inverse y).
    set (-y * y * -x).
    rewrite <- (right_identity (-y)).
    destruct (right_inverse x).
    unfold g; clear g.
    rewrite <- simple_associativity.
    apply iscong; try reflexivity.
    apply iscong; try reflexivity.
    by symmetry.
  Defined.

  Global Instance congquot_sgop_associative : Associative congquot_sgop.
  Proof.
    intros x y.
    srapply Quotient_ind_hprop; intro a; revert y.
    srapply Quotient_ind_hprop; intro b; revert x.
    srapply Quotient_ind_hprop; intro c.
    simpl; by rewrite associativity.
  Qed.

  Global Instance issemigroup_congquot : IsSemiGroup CongruenceQuotient := {}.

  Global Instance congquot_leftidentity
    : LeftIdentity congquot_sgop congquot_mon_unit.
  Proof.
    srapply Quotient_ind_hprop; intro x.
    by simpl; rewrite left_identity.
  Qed.

  Global Instance congquot_rightidentity
    : RightIdentity congquot_sgop congquot_mon_unit.
  Proof.
    srapply Quotient_ind_hprop; intro x.
    by simpl; rewrite right_identity.
  Qed.

  Global Instance ismonoid_quotientgroup : IsMonoid CongruenceQuotient := {}.

  Global Instance quotientgroup_leftinverse
    : LeftInverse congquot_sgop congquot_negate congquot_mon_unit.
  Proof.
    srapply Quotient_ind_hprop; intro x.
    by simpl; rewrite left_inverse.
  Qed.

  Global Instance quotientgroup_rightinverse
    : RightInverse congquot_sgop congquot_negate congquot_mon_unit.
  Proof.
    srapply Quotient_ind_hprop; intro x.
    by simpl; rewrite right_inverse.
  Qed.

  Global Instance isgroup_quotientgroup : IsGroup CongruenceQuotient := {}.

End GroupCongruenceQuotient.

(** Now we can define the quotient group by a normal subgroup. *)

Section QuotientGroup.

  Context (G : Group) (N : NormalSubgroup G).

  Global Instance iscongruence_in_cosetL : IsCongruence (in_cosetL N).
  Proof.
    srapply Build_IsCongruence.
    intros; by apply in_cosetL_cong.
  Defined.

  Global Instance iscongruence_in_cosetR: IsCongruence (in_cosetR N).
  Proof.
    srapply Build_IsCongruence.
    intros; by apply in_cosetR_cong.
  Defined.

  (** Now we have to make a choice whether to pick the left or right cosets. Due to existing convention we shall pick left cosets but we note that we could equally have picked right. *)
  Definition QuotientGroup : Group
    := Build_Group (G / (in_cosetL N)) _ _ _ _.

  Definition grp_quotient_map : G $-> QuotientGroup.
  Proof.
    snrapply Build_GroupHomomorphism.
    1: exact (class_of _).
    intros ??; reflexivity.
  Defined.

  Definition grp_quotient_rec {A : Group} (f : G $-> A)
             (h : forall n : G, N n -> f n = mon_unit)
    : QuotientGroup $-> A.
  Proof.
    snrapply Build_GroupHomomorphism.
    - srapply Quotient_rec.
      + exact f.
      + cbn; intros x y n.
        symmetry.
        apply (group_moveL_M1 _ _).
        rewrite <- grp_homo_inv.
        rewrite <- grp_homo_op.
        apply h; assumption.
    - intro x.
      refine (Quotient_ind_hprop _ _ _).
      intro y. revert x.
      refine (Quotient_ind_hprop _ _ _).
      intro x; simpl.
      apply grp_homo_op.
  Defined.

End QuotientGroup.

Arguments grp_quotient_map {_ _}.

Notation "G / N" := (QuotientGroup G N) : group_scope.

(** Rephrasing that lets you specify the normality proof *)
Definition QuotientGroup' (G : Group) (N : Subgroup G) (H : IsNormalSubgroup N)
  := QuotientGroup G (Build_NormalSubgroup G N H).

Local Open Scope group_scope.

(** Computation rule for grp_quotient_rec. *)
Corollary grp_quotient_rec_beta `{F : Funext} {G : Group}
          (N : NormalSubgroup G) (H : Group)
          {A : Group} (f : G $-> A)
          (h : forall n:G, N n -> f n = mon_unit)
  : (grp_quotient_rec G N f h) $o grp_quotient_map = f.
Proof.
  apply equiv_path_grouphomomorphism; reflexivity.
Defined.

(** The proof of normality is irrelevent up to equivalence. This is unfortunate that it doesn't hold definitionally. *)
Definition grp_iso_quotient_normal (G : Group) (H : Subgroup G)
  {k k' : IsNormalSubgroup H}
  : GroupIsomorphism (QuotientGroup' G H k) (QuotientGroup' G H k').
Proof.
  snrapply Build_GroupIsomorphism'.
  1: reflexivity.
  intro x.
  srapply Quotient_ind_hprop; intro y; revert x.
  srapply Quotient_ind_hprop; intro x.
  reflexivity.
Defined.

(** The universal mapping property for groups *)
Theorem equiv_grp_quotient_ump {F : Funext} {G : Group} (N : NormalSubgroup G) (H : Group)
  : {f : G $-> H & forall (n : G), N n -> f n = mon_unit} <~> (G / N $-> H).
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
      by apply issubgroup_inverse.
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
  Definition grp_image_quotient : GroupHomomorphism (A / grp_kernel phi) (grp_image phi).
  Proof.
    srapply grp_quotient_rec.
    + srapply grp_image_in.
    + intros n x.
      by apply path_sigma_hprop.
  Defined.

  (** The underlying map of this homomorphism is an equivalence *)
  Global Instance isequiv_grp_image_quotient : IsEquiv grp_image_quotient.
  Proof.
    snrapply isequiv_surj_emb.
    1: srapply cancelR_conn_map.
    srapply isembedding_isinj_hset.
    refine (Quotient_ind_hprop _ _ _); intro x.
    refine (Quotient_ind_hprop _ _ _); intro y.
    intros h; simpl in h.
    apply qglue; cbn.
    apply (equiv_path_sigma_hprop _ _)^-1%equiv in h; cbn in h.
    cbn. rewrite grp_homo_op, grp_homo_inv, h.
    srapply negate_l.
  Defined.

  (** First isomorphism theorem for groups *)
  Theorem grp_first_iso : GroupIsomorphism (A / grp_kernel phi) (grp_image phi) .
  Proof.
    exact (Build_GroupIsomorphism _ _ grp_image_quotient _).
  Defined.

End FirstIso.
