Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids Basics.Trunc.
Require Import Types.Sigma.
Require Import Groups.Group AbGroups.Abelianization AbGroups.AbelianGroup
  Groups.QuotientGroup.
Require Import WildCat.Core WildCat.EquivGpd.
Require Import Truncations.Core.

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

Set Universe Minimization ToSet.

(** Commutators in groups *)

(** ** Commutators of group elements *)

(** Note that this convention is chosen due to the convention we chose for group conjugation elsewhere. *)
Definition grp_commutator {G : Group} (x y : G) : G := x * y * x^ * y^.

Notation "[ x , y ]" := (grp_commutator x y) : mc_mult_scope.

(** ** Easy properties of commutators *)

(** Commuting elements of a group have trivial commutator. *)
Definition grp_commutator_commutes {G : Group} (x y : G) (p : x * y = y * x)
  : [x, y] = 1.
Proof.
  unfold grp_commutator.
  rewrite p, grp_inv_gg_V.
  apply grp_inv_r.
Defined.

(** A commutator of an element with itself is the unit. *)
Definition grp_commutator_cancel {G : Group} (x y : G)
  : [x, x] = 1.
Proof.
  by apply grp_commutator_commutes.
Defined.

(** A commutator of a group element with unit on the left is the unit. *)
Definition grp_commutator_unit_l {G : Group} (x : G)
  : [1, x] = 1.
Proof.
  by apply grp_commutator_commutes, grp_1g_g1.
Defined.

(** A commutator of a group element with unit on the right is the unit. *)
Definition grp_commutator_unit_r {G : Group} (x : G)
  : [x, 1] = 1.
Proof.
  by apply grp_commutator_commutes, grp_g1_1g.
Defined.

(** Commutators in abelian groups are trivial. *)
Definition ab_commutator (A : AbGroup) (x y : A)
  : [x, y] = 1.
Proof.
  apply grp_commutator_commutes, commutativity.
Defined.

(** The commutator can be thought of as the "error" in the commutativity of two elements of a group. *)
Definition grp_commutator_swap_op {G : Group} (x y : G)
  : x * y = [x, y] * y * x.
Proof.
  unfold grp_commutator.
  by rewrite !grp_inv_gV_g.
Defined.

(** Inverting a commutator reverses the order. *)
Definition grp_commutator_inv {G : Group} (x y : G)
  : [x, y]^ = [y, x].
Proof.
  unfold grp_commutator.
  by rewrite 3 grp_inv_op, 2 grp_inv_inv, 2 grp_assoc.
Defined.

(** Group homomorphisms commute with commutators. *)
Definition grp_homo_commutator {G H : Group} (f : G $-> H) (x y : G)
  : f [x, y] = [f x, f y].
Proof.
  unfold grp_commutator.
  by rewrite !grp_homo_op, !grp_homo_inv.
Defined.

(** A commutator with a product on the left side can be expanded as the product of a conjugated commutator and another commutator. *)
Definition grp_commutator_op_l {G : Group} (x y z : G)
  : [x * y, z] = grp_conj x [y, z] * [x, z].
Proof.
  unfold grp_commutator, grp_conj, grp_homo_map.
  by rewrite grp_inv_op, !grp_assoc, !grp_inv_gV_g.
Defined.

(** A commutator with a product on the right side can be expanded as the product of a conjugated commutator and another commutator. *)
Definition grp_commutator_op_r {G : Group} (x y z : G)
  : [x, y * z] = [x, y] * grp_conj y [x, z].
Proof.
  unfold grp_commutator, grp_conj, grp_homo_map.
  by rewrite grp_inv_op, !grp_assoc, !grp_inv_gV_g.
Defined.

(** A commutator with the element on the right being multiplied on the right gives a conjugation. *)
Definition grp_op_l_commutator {G : Group} (x y : G)
  : [x, y] * y = grp_conj x y.
Proof.
  unfold grp_commutator, grp_conj, grp_homo_map.
  by rewrite grp_inv_gV_g.
Defined.

(** A commutator with the inverse element on the left being multiplied on the left gives a conjugation. *)
Definition grp_op_r_commutator {G : Group} (x y : G)
  : x^ * [x, y] = grp_conj y x^.
Proof.
  unfold grp_commutator, grp_conj, grp_homo_map.
  by rewrite <- !grp_assoc, grp_inv_V_gg.
Defined.

(** Commutators with inverted left sides are conjugated commutators. *)
Definition grp_commutator_inv_l {G : Group} (x y : G)
  : [x^, y] = grp_conj x^ [y, x].
Proof.
  unfold grp_commutator, grp_conj, grp_homo_map.
  by rewrite !grp_assoc, grp_inv_inv, grp_inv_gV_g.
Defined.

(** Commutators with inverted right sides are conjugated commutators. *)
Definition grp_commutator_inv_r {G : Group} (x y : G)
  : [x, y^] = grp_conj y^ [y, x].
Proof.
  unfold grp_commutator, grp_conj, grp_homo_map.
  by rewrite <- !grp_assoc, grp_inv_inv, grp_inv_V_gg.
Defined.

Definition grp_conj_commutator_inv_l {G : Group} (x y : G)
  : grp_conj x [x^, y] = [y, x].
Proof.
  unfold grp_commutator, grp_conj, grp_homo_map.
  by rewrite !grp_inv_inv, <- !grp_assoc, grp_inv_g_Vg.
Defined.

Definition grp_conj_commutator_inv_r {G : Group} (x y : G)
  : grp_conj y [x, y^] = [y, x].
Proof.
  unfold grp_commutator, grp_conj, grp_homo_map.
  by rewrite grp_inv_inv, !grp_assoc, grp_inv_gg_V.
Defined.

(** ** Hall-Witt identity *)

(** The Hall-Witt identity is a Jacobi-like identity for groups. It states that the different commutators of 3 elements (with one conjugated) assemble into an identity. The proof is purely mechanical and simply cancels all the terms. This is a rare instance where a mechanized proof is much shorter than an on-paper proof. *)
Definition grp_hall_witt {G : Group} (x y z : G)
  : [[x, y], grp_conj y z] * [[y, z], grp_conj z x] * [[z, x], grp_conj x y] = 1.
Proof.
  unfold grp_commutator, grp_conj, grp_homo_map.
  rewrite !grp_inv_op, !grp_inv_inv, !grp_assoc.
  do 3 rewrite !grp_inv_gV_g, !grp_inv_gg_V.
  apply grp_inv_r.
Defined.

(** This variant of the Hall-Witt identity is useful later for proving the three subgroups lemma. *)  
Definition grp_hall_witt' {G : Group} (x y z : G)
  : grp_conj x [[x^, y], z] * grp_conj z [[z^, x], y] * grp_conj y [[y^, z], x] = 1.
Proof.
  rewrite 3 (grp_homo_commutator _ [_^, _]).
  rewrite 3 grp_conj_commutator_inv_l.
  apply grp_hall_witt.
Defined.

(** ** Precomposing normal subgroups with commutators *)

Global Instance issubgroup_precomp_commutator {G : Group} (H : Subgroup G)
  `{!IsNormalSubgroup H} (y : G)
  : IsSubgroup (fun x => H [x, y]).
Proof.
  snrapply Build_IsSubgroup; cbn beta.
  - exact _.
  - rewrite grp_commutator_unit_l.
    apply subgroup_in_unit.
  - intros x z Hxy Hzy.
    rewrite grp_commutator_op_l.
    apply subgroup_in_op.
    + by rapply isnormal_conj.
    + assumption.
  - intros x Hxy.
    rewrite grp_commutator_inv_l.
    rapply isnormal_conj.
    rewrite <- grp_commutator_inv.
    by apply subgroup_in_inv.
Defined.

Definition subgroup_precomp_commutator {G : Group} (H : Subgroup G) (y : G)
  `{!IsNormalSubgroup H}
  : Subgroup G
  := Build_Subgroup _ (fun x => H [x, y]) _.

(** ** Commutator subgroups *)

Definition subgroup_commutator {G : Group@{i}} (H K : Subgroup@{i i} G)
  : Subgroup@{i i} G
  := subgroup_generated (fun g => exists (x : H) (y : K), [x.1, y.1] = g).

Notation "[ H , K ]" := (subgroup_commutator H K) : group_scope.

Local Open Scope group_scope.

(** [subgroup_commutator H K] is the smallest subgroup containing the commutators of elements of [H] with elements of [K]. *)
Definition subgroup_commutator_rec {G : Group} {H K : Subgroup G} (J : Subgroup G)
  (i : forall x y, H x -> K y -> J (grp_commutator x y))
  : forall x, [H, K] x -> J x.
Proof.
  rapply subgroup_generated_rec; intros x [[y Hy] [[z Kz] p]];
    destruct p; simpl.
  by apply i.
Defined.

(** Doubly iterated [subgroup_commutator]s of [H], [J] and [K] are the smallest of the normal subgroups containing the doubly iterated commutators of elements of [H], [J] and [K]. *)
Definition subgroup_commutator_2_rec {G : Group} {H J K : Subgroup G}
  (N : Subgroup G) `{!IsNormalSubgroup N}
  (i : forall x y z, H x -> J y -> K z -> N (grp_commutator (grp_commutator x y) z))
  : forall x, [[H, J], K] x -> N x.
Proof.
  snrapply subgroup_commutator_rec.
  intros x z HJx Kz; revert x HJx.
  change (N (grp_commutator ?x z)) with (subgroup_precomp_commutator N z x).
  rapply subgroup_commutator_rec.
  by intros; apply i.
Defined.

(** A commutator subgroup of an abelian group is always trivial. *)
Definition istrivial_commutator_subgroup_ab {A : AbGroup} (H K : Subgroup A)
  : IsTrivialGroup [H, K].
Proof.
  rapply subgroup_commutator_rec; intros.
  rapply ab_commutator.
Defined.

(** ** Derived subgroup *)

(** The commutator subgroup of the maximal subgroup with itself is called the derived subgroup. It is the subgroup generated by all commutators. *)

(** The derived subgroup is a normal subgroup. *)
Global Instance isnormal_subgroup_derived {G : Group}
  : IsNormalSubgroup [G, G].
Proof.
  snrapply Build_IsNormalSubgroup'.
  intros x y; revert x.
  apply (functor_subgroup_generated _ _ (grp_conj y)).
  intros g.
  snrapply (functor_sigma (functor_sigma (grp_conj y) (fun _ => idmap)));
    cbn beta; intros [x []].
  snrapply (functor_sigma (functor_sigma (grp_conj y) (fun _ => idmap)));
    cbn beta; intros [z []].
  intros p; simpl.
  lhs_V nrapply (grp_homo_commutator (grp_conj y)).
  snrapply (ap (grp_conj y)).
  exact p.
Defined.

Definition normalsubgroup_derived G : NormalSubgroup G
  := Build_NormalSubgroup G [G, G] _.

(** We can quotient a group by its derived subgroup. *)
Definition grp_derived_quotient (G : Group) : Group
  := QuotientGroup G (normalsubgroup_derived G).

(** We can show that the multiplication then becomes commutative. *)
Global Instance commutative_grp_derived_quotient (G : Group)
  : Commutative (A:=grp_derived_quotient G) (.*.).
Proof.
  intros x.
  srapply grp_quotient_ind_hprop; intros y; revert x.
  srapply grp_quotient_ind_hprop; intros x; cbn beta.
  apply qglue, tr, sgt_in; exists (y^; tt), (x^; tt).
  unfold grp_commutator; simpl.
  by rewrite !grp_inv_op, !grp_inv_inv, !grp_assoc.
Defined.

(** Hence we have a way of producing abelian groups from groups. *)
Definition abgroup_derived_quotient (G : Group) : AbGroup
  := Build_AbGroup (grp_derived_quotient G) _.

(** We get a recursion principle into abelian groups. *)
Definition abgroup_derived_quotient_rec {G : Group} {A : AbGroup} (f : G $-> A) 
  : abgroup_derived_quotient G $-> A.
Proof.
  snrapply (grp_quotient_rec _ _ f).
  change (f ?n = 1) with (subgroup_preimage f (trivial_subgroup A) n).
  snrapply subgroup_commutator_rec.
  intros x y _ _.
  lhs nrapply grp_homo_commutator.
  apply ab_commutator.
Defined.

(** Furthermore, this construction is an abelianization. *)
Definition isabelianization_derived_quotient (G : Group)
  : IsAbelianization (abgroup_derived_quotient G) grp_quotient_map.
Proof.
  intros A.
  snrapply Build_IsSurjInj.
  - intros f.
    nrefine (abgroup_derived_quotient_rec f; _).
    hnf; reflexivity.
  - intros f g p.
    srapply grp_quotient_ind_hprop; intros x; cbn beta.
    exact (p x).
Defined.

(** *** Three subgroups lemma *)

Definition three_subgroups_lemma (G : Group) (H J K N : Subgroup G)
  `{!IsNormalSubgroup N}
  (T1 : forall x, [[H, J], K] x -> N x)
  (T2 : forall x, [[J, K], H] x -> N x)
  : forall x, [[K, H], J] x -> N x.
Proof.
  rapply subgroup_commutator_2_rec.
  Local Close Scope group_scope.
  intros z x y Kz Hx Jy.
  pose proof (grp_hall_witt' x y z^) as p.
  rewrite grp_inv_inv in p.
  apply grp_moveL_1V in p.
  apply grp_moveL_Vg in p.
  apply (isnormal_conj _ (y:=z^))^-1.
  change (N (grp_conj z^ [[z, x], y])).
  rewrite p.
  apply subgroup_in_op.
  - apply subgroup_in_inv.
    rapply isnormal_conj.
    apply T1.
    apply tr, sgt_in.
    unshelve eexists.
    + exists [x^, y].
      apply tr, sgt_in.
      by exists (x^; subgroup_in_inv _ _ Hx), (y; Jy). 
    + by exists (z^; subgroup_in_inv _ _ Kz).
  - apply subgroup_in_inv.
    rapply isnormal_conj.
    apply T2.
    apply tr, sgt_in.
    unshelve eexists.
    + exists [y^, z^].
      apply tr, sgt_in.
      by exists (y^; subgroup_in_inv _ _ Jy), (z^; subgroup_in_inv _ _ Kz). 
    + by exists (x; Hx).
  Local Open Scope group_scope.
Defined.

Definition three_trivial_commutators (G : Group) (H J K : Subgroup G)
  : IsTrivialGroup [[H, J], K]
    -> IsTrivialGroup [[J, K], H]
    -> IsTrivialGroup [[K, H], J].
Proof.
  rapply three_subgroups_lemma.
Defined.
