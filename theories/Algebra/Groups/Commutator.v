Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids Basics.Trunc
  Basics.Iff Basics.Equivalences Basics.Predicate.
Require Import Types.Sigma Types.Paths.
Require Import Groups.Group AbGroups.Abelianization AbGroups.AbelianGroup
  Groups.QuotientGroup.
Require Import WildCat.Core WildCat.Equiv WildCat.EquivGpd.
Require Import Truncations.Core.

Local Open Scope predicate_scope.
Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

Set Universe Minimization ToSet.

(** Commutators in groups *)

(** ** Commutators of group elements *)

(** Note that this convention is chosen due to the convention we chose for group conjugation elsewhere. *)
Definition grp_commutator {G : Group} (x y : G) : G := x * y * x^ * y^.

Notation "[ x , y ]" := (grp_commutator x y) : mc_mult_scope.

Arguments grp_commutator {G} x y : simpl never.

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

Instance issubgroup_precomp_commutator_l {G : Group} (H : Subgroup G)
  `{!IsNormalSubgroup H} (y : G)
  : IsSubgroup (fun x => H [x, y]).
Proof.
  snapply Build_IsSubgroup; cbn beta.
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

(** The condition [H [x, y]] is equivalent to the condition [H [y, x]]. *)
Definition issubgroup_precomp_commutator_agree {G : Group} (H : Subgroup G)
  (x y : G)
  : H [x, y] <~> H [y, x].
Proof.
  refine (_ oE equiv_subgroup_inv _ _).
  by rewrite grp_commutator_inv.
Defined.

(** So we get this symmetrical version as well. *)
Instance issubgroup_precomp_commutator_r {G : Group} (H : Subgroup G)
  `{!IsNormalSubgroup H} (x : G)
  : IsSubgroup (fun y => H [x, y])
  := issubgroup_equiv (fun y => issubgroup_precomp_commutator_agree H y x) _.

Definition subgroup_precomp_commutator_l {G : Group} (H : Subgroup G) (y : G)
  `{!IsNormalSubgroup H}
  : Subgroup G
  := Build_Subgroup _ (fun x => H [x, y]) _.

Definition subgroup_precomp_commutator_r {G : Group} (H : Subgroup G) (x : G)
  `{!IsNormalSubgroup H}
  : Subgroup G
  := Build_Subgroup _ (fun y => H [x, y]) _.

(** ** Commutator subgroups *)

Definition subgroup_commutator {G : Group@{i}} (H K : Subgroup@{i i} G)
  : Subgroup@{i i} G
  := subgroup_generated (fun g => exists (x : H) (y : K), [x.1, y.1] = g).

Notation "[ H , K ]" := (subgroup_commutator H K) : group_scope.

Local Open Scope group_scope.

(** [subgroup_commutator H K] is the smallest subgroup containing the commutators of elements of [H] with elements of [K]. *)
Definition subgroup_commutator_rec {G : Group} {H K : Subgroup G} (J : Subgroup G)
  (i : forall x y, H x -> K y -> J (grp_commutator x y))
  : [H, K] ⊆ J.
Proof.
  rapply subgroup_generated_rec; intros x [[y Hy] [[z Kz] p]];
    destruct p; simpl.
  by apply i.
Defined.

(** Doubly iterated [subgroup_commutator]s of [H], [J] and [K] are the smallest of the normal subgroups containing the doubly iterated commutators of elements of [H], [J] and [K]. *)
Definition subgroup_commutator_2_rec {G : Group} {H J K : Subgroup G}
  (N : Subgroup G) `{!IsNormalSubgroup N}
  (i : forall x y z, H x -> J y -> K z -> N (grp_commutator (grp_commutator x y) z))
  : [[H, J], K] ⊆ N.
Proof.
  snapply subgroup_commutator_rec.
  intros x z HJx Kz; revert x HJx.
  change (N (grp_commutator ?x z)) with (subgroup_precomp_commutator_l N z x).
  rapply subgroup_commutator_rec.
  by intros; apply i.
Defined.

(** A commutator of elements from each respective subgroup is in the commutator subgroup. *)
Definition subgroup_commutator_in {G : Group} {H J : Subgroup G} {x y : G}
  (Hx : H x) (Jy : J y)
  : subgroup_commutator H J (grp_commutator x y).
Proof.
  apply tr, sgt_in.
  by exists (x; Hx), (y; Jy).
Defined.

(** Commutator subgroups are functorial. *)
Definition functor_subgroup_commutator {G : Group} {H J K L : Subgroup G}
  (f : H ⊆ K) (g : J ⊆ L)
  : [H, J] ⊆ [K, L].
Proof.
  snapply subgroup_commutator_rec.
  intros x y Hx Jx.
  exact (subgroup_commutator_in (f _ Hx) (g _ Jx)).
Defined.

Definition subgroup_eq_commutator {G : Group} {H J K L : Subgroup G}
  (f : H ↔ K) (g : J ↔ L)
  : [H, J] ↔ [K, L].
Proof.
  snapply pred_subset_antisymm; apply functor_subgroup_commutator.
  3,4: apply pred_subset_pred_eq'.
  1,3: exact f.
  1,2: exact g.
Defined.

Definition subgroup_incl_commutator_symm {G : Group} (H J : Subgroup G)
  : [H, J] ⊆ [J, H].
Proof.
  snapply subgroup_commutator_rec.
  intros x y Hx Jy.
  napply subgroup_in_inv'.
  rewrite grp_commutator_inv.
  by apply subgroup_commutator_in.
Defined.

(** Commutator subgroups are symmetric in their arguments. *)
Definition subgroup_commutator_symm {G : Group} (H J : Subgroup G)
  : [H, J] ↔ [J, H].
Proof.
  snapply pred_subset_antisymm; apply subgroup_incl_commutator_symm.
Defined.

(** The opposite subgroup of a commutator subgroup is the commutator subgroup of the opposite subgroups. *)
Definition subgroup_eq_commutator_grp_op {G : Group} (H J : Subgroup G)
  : subgroup_grp_op [H, J] ↔ [subgroup_grp_op J, subgroup_grp_op H].
Proof.
  napply (subgroup_eq_subgroup_generated_op (G:=G)).
  intro x.
  refine (iff_compose _ (equiv_sigma_symm _)).
  do 2 (snapply (equiv_functor_sigma'
    (grp_iso_subgroup_group (grp_op_iso_inv G)
      (equiv_subgroup_inv (G:=grp_op G) (subgroup_grp_op _)))); intro).
  simpl.
  apply equiv_concat_l; symmetry.
  lhs_V napply grp_commutator_inv.
  exact (grp_homo_commutator (grp_op_iso_inv _) a0.1 a.1).
Defined.

(** A commutator subgroup of an abelian group is always trivial. *)
Definition istrivial_commutator_subgroup_ab {A : AbGroup} (H K : Subgroup A)
  : IsTrivialGroup [H, K].
Proof.
  rapply subgroup_commutator_rec; intros.
  rapply ab_commutator.
Defined.

(** A commutator of normal subgroups is normal. *)
Instance isnormal_subgroup_commutator {G : Group} (H J : Subgroup G)
  `{!IsNormalSubgroup H, !IsNormalSubgroup J}
  : IsNormalSubgroup [H, J].
Proof.
  snapply Build_IsNormalSubgroup'.
  intros x y; revert x.
  apply (functor_subgroup_generated _ _ (grp_conj y)).
  intros x.
  do 2 (rapply (functor_sigma (grp_iso_normal_conj _ y)); intro).
  intros p.
  lhs_V napply (grp_homo_commutator (grp_conj y)).
  exact (ap (grp_conj y) p).
Defined.

(** Commutator subgroups distribute over products of normal subgroups on the left. *)
Definition subgroup_commutator_normal_prod_l {G : Group}
  (H K L : NormalSubgroup G)
  : [subgroup_product H K, L] ↔ subgroup_product [H, L] [K, L].
Proof.
  intros x; split.
  - revert x; snapply subgroup_commutator_rec.
    intros x y HKx Ly; revert x HKx.
    change (subgroup_product ?H ?J (grp_commutator ?x y))
      with (subgroup_precomp_commutator_l (subgroup_product H J) y x).
    snapply subgroup_generated_rec.
    intros x [Hx | Kx].
    + apply subgroup_product_incl_l.
      by apply subgroup_commutator_in.
    + apply subgroup_product_incl_r.
      by apply subgroup_commutator_in.
  - revert x; snapply subgroup_generated_rec.
    intros x [HLx | KLx].
    + revert x HLx.
      apply functor_subgroup_commutator.
      2: reflexivity.
      apply subgroup_product_incl_l.
    + revert x KLx.
      apply functor_subgroup_commutator.
      2: reflexivity.
      apply subgroup_product_incl_r.
Defined.

(** Commutator subgroups distribute over products of normal subgroups on the right. *)
Definition subgroup_commutator_normal_prod_r {G : Group}
  (H K L : NormalSubgroup G)
  : [H, subgroup_product K L] ↔ subgroup_product [H, K] [H, L].
Proof.
  intros x.
  etransitivity.
  1: symmetry; apply subgroup_commutator_symm.
  etransitivity.
  2: napply (subgroup_eq_functor_subgroup_product grp_iso_id
    (subgroup_commutator_symm _ _) (subgroup_commutator_symm _ _)).
  exact (subgroup_commutator_normal_prod_l K L H x).
Defined.

(** The subgroup image of a commutator is included in the commutator of the subgroup images. The converse only generally holds for a normal [J] and [K] and a surjective [f]. *)
Definition subgroup_image_commutator_incl {G H : Group}
  (f : G $-> H) (J K : Subgroup G)
  : subgroup_image f [J, K] ⊆ [subgroup_image f J, subgroup_image f K].
Proof.
  snapply subgroup_image_rec.
  snapply subgroup_commutator_rec.
  intros x y Jx Ky.
  change (subgroup_preimage f [?G, ?H] ?x) with ([G, H] (f x)).
  rewrite grp_homo_commutator.
  apply subgroup_commutator_in;
    by apply subgroup_image_in.
Defined.

(** ** Derived subgroup *)

(** The commutator subgroup of the maximal subgroup with itself is called the derived subgroup. It is the subgroup generated by all commutators. *)
Definition normalsubgroup_derived G : NormalSubgroup G
  := Build_NormalSubgroup G [G, G] _.

(** We can quotient a group by its derived subgroup. *)
Definition grp_derived_quotient (G : Group) : Group
  := QuotientGroup G (normalsubgroup_derived G).

(** We can show that the multiplication then becomes commutative. *)
Instance commutative_grp_derived_quotient (G : Group)
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
  snapply (grp_quotient_rec _ _ f).
  change (f ?n = 1) with (subgroup_preimage f (trivial_subgroup A) n).
  snapply subgroup_commutator_rec.
  intros x y _ _.
  lhs napply grp_homo_commutator.
  apply ab_commutator.
Defined.

(** Furthermore, this construction is an abelianization. *)
Definition isabelianization_derived_quotient (G : Group)
  : IsAbelianization (abgroup_derived_quotient G) grp_quotient_map.
Proof.
  intros A.
  snapply Build_IsSurjInj.
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
  (T1 : [[H, J], K] ⊆ N) (T2 : [[J, K], H] ⊆ N)
  : [[K, H], J] ⊆ N.
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
      apply subgroup_commutator_in; trivial.
      by apply subgroup_in_inv.
    + by exists (z^; subgroup_in_inv _ _ Kz).
  - apply subgroup_in_inv.
    rapply isnormal_conj.
    apply T2.
    apply tr, sgt_in.
    unshelve eexists.
    + exists [y^, z^].
      apply subgroup_commutator_in;
        by apply subgroup_in_inv.
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
