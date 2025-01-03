Require Import Basics Types HFiber WildCat.Core WildCat.Equiv.
Require Import Truncations.Core.
Require Import Algebra.Groups.Group TruncType.

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

Generalizable Variables G H A B C N f g.

(** * Subgroups *)

(** A subgroup H of a group G is a predicate (i.e. an hProp-valued type family) on G which is closed under the group operations. The group underlying H is given by the total space { g : G & H g }, defined in [subgroup_group] below. *)
Class IsSubgroup {G : Group} (H : G -> Type) := {
  issubgroup_predicate : forall x, IsHProp (H x) ;
  issubgroup_in_unit : H mon_unit ;
  issubgroup_in_op : forall x y, H x -> H y -> H (x * y) ;
  issubgroup_in_inv : forall x, H x -> H x^ ;
}.

Global Existing Instance issubgroup_predicate.

(** Smart constructor for subgroups.  *)
Definition Build_IsSubgroup' {G : Group}
  (H : G -> Type) `{forall x, IsHProp (H x)}
  (unit : H mon_unit)
  (c : forall x y, H x -> H y -> H (x * y^))
  : IsSubgroup H.
Proof.
  refine (Build_IsSubgroup G H _ unit _ _).
  - intros x y.
    intros hx hy.
    pose (c' := c mon_unit y).
    specialize (c' unit).
    specialize (c x y^).
    rewrite (grp_inv_inv y) in c.
    rewrite left_identity in c'.
    apply c.
    1: assumption.
    exact (c' hy).
  - intro g.
    specialize (c _ g unit).
    rewrite left_identity in c.
    assumption.
Defined.

(** Additional lemmas about being elements in a subgroup *)
Section IsSubgroupElements.
  Context  {G : Group} {H : G -> Type} `{IsSubgroup G H}.

  Definition issubgroup_in_op_inv (x y : G) : H x -> H y -> H (x * y^).
  Proof.
    intros p q.
    apply issubgroup_in_op.
    1: assumption.
    by apply issubgroup_in_inv.
  Defined.

  Definition issubgroup_in_inv' (x : G) : H x^ -> H x.
  Proof.
    intros p; rewrite <- (inverse_involutive x); revert p.
    apply issubgroup_in_inv.
  Defined.

  Definition issubgroup_in_inv_op (x y : G) : H x -> H y -> H (x^ * y).
  Proof.
    intros p q.
    rewrite <- (inverse_involutive y).
    apply issubgroup_in_op_inv.
    1,2: by apply issubgroup_in_inv.
  Defined.

  Definition issubgroup_in_op_l (x y : G) : H (x * y) -> H y -> H x.
  Proof.
    intros p q.
    rewrite <- (grp_unit_r x).
    revert p q.
    rewrite <- (grp_inv_r y).
    rewrite grp_assoc.
    apply issubgroup_in_op_inv.
  Defined.

  Definition issubgroup_in_op_r (x y : G) : H (x * y) -> H x -> H y.
  Proof.
    intros p q.
    rewrite <- (grp_unit_l y).
    revert q p.
    rewrite <- (grp_inv_l x).
    rewrite <- grp_assoc.
    apply issubgroup_in_inv_op.
  Defined.

End IsSubgroupElements.

Definition issig_issubgroup {G : Group} (H : G -> Type) : _ <~> IsSubgroup H
  := ltac:(issig).

(** Given a predicate H on a group G, being a subgroup is a property. *)
Global Instance ishprop_issubgroup `{F : Funext} {G : Group} {H : G -> Type}
  : IsHProp (IsSubgroup H).
Proof.
  exact (istrunc_equiv_istrunc _ (issig_issubgroup H)).
Defined.

(** The type (set) of subgroups of a group G. *)
Record Subgroup (G : Group) := {
  subgroup_pred : G -> Type ;
  subgroup_issubgroup : IsSubgroup subgroup_pred ;
}.

Coercion subgroup_pred : Subgroup >-> Funclass.
Global Existing Instance subgroup_issubgroup.

Definition Build_Subgroup' {G : Group}
  (H : G -> Type) `{forall x, IsHProp (H x)}
  (unit : H mon_unit)
  (c : forall x y, H x -> H y -> H (x * y^))
  : Subgroup G.
Proof.
  refine (Build_Subgroup G H _).
  rapply Build_IsSubgroup'; assumption.
Defined.

Section SubgroupElements.
  Context {G : Group} (H : Subgroup G) (x y : G).
  Definition subgroup_in_unit : H 1 := issubgroup_in_unit.
  Definition subgroup_in_inv : H x -> H x^ := issubgroup_in_inv x.
  Definition subgroup_in_inv' : H x^ -> H x := issubgroup_in_inv' x.
  Definition subgroup_in_op : H x -> H y -> H (x * y) := issubgroup_in_op x y.
  Definition subgroup_in_op_inv : H x -> H y -> H (x * y^) := issubgroup_in_op_inv x y.
  Definition subgroup_in_inv_op : H x -> H y -> H (x^ * y) := issubgroup_in_inv_op x y.
  Definition subgroup_in_op_l : H (x * y) -> H y -> H x := issubgroup_in_op_l x y.
  Definition subgroup_in_op_r : H (x * y) -> H x -> H y := issubgroup_in_op_r x y.
End SubgroupElements.

Global Instance isequiv_subgroup_in_inv `(H : Subgroup G) (x : G)
  : IsEquiv (subgroup_in_inv H x).
Proof.
  srapply isequiv_iff_hprop.
  apply subgroup_in_inv'.
Defined.

Definition equiv_subgroup_inverse {G : Group} (H : Subgroup G) (x : G)
  : H x <~> H x^ := Build_Equiv _ _ (subgroup_in_inv H x) _.

(** The group given by a subgroup *)
Definition subgroup_group {G : Group} (H : Subgroup G) : Group.
Proof.
  apply (Build_Group
      (** The underlying type is the sigma type of the predicate. *)
      (sig H)
      (** The operation is the group operation on the first projection with the proof  of being in the subgroup given by the subgroup data. *)
      (fun '(x ; p) '(y ; q) => (x * y ; issubgroup_in_op x y p q))
      (** The unit *)
      (mon_unit ; issubgroup_in_unit)
      (** Inverse *)
      (fun '(x ; p) => (- x ; issubgroup_in_inv _ p))).
  (** Finally we need to prove our group laws. *)
  repeat split.
  1: exact _.
  all: grp_auto.
Defined.

Coercion subgroup_group : Subgroup >-> Group.

Definition subgroup_incl {G : Group} (H : Subgroup G)
  : subgroup_group H $-> G.
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact pr1.
  hnf; reflexivity.
Defined.

Global Instance isembedding_subgroup_incl {G : Group} (H : Subgroup G)
  : IsEmbedding (subgroup_incl H)
  := fun _ => istrunc_equiv_istrunc _ (hfiber_fibration _ _).

Definition issig_subgroup {G : Group} : _ <~> Subgroup G
  := ltac:(issig).

(** Trivial subgroup *)
Definition trivial_subgroup G : Subgroup G.
Proof.
  rapply (Build_Subgroup' (fun x => x = mon_unit)).
  1: reflexivity.
  intros x y p q.
  rewrite p, q.
  rewrite left_identity.
  apply inverse_mon_unit.
Defined.

Definition trivial_subgroup_rec {G : Group} (H : Subgroup G)
  : forall x, trivial_subgroup G x -> H x.
Proof.
  snrapply paths_ind_r; cbn beta.
  apply issubgroup_in_unit.
Defined.

(** The preimage of a subgroup under a group homomorphism is a subgroup. *)
Definition subgroup_preimage {G H : Group} (f : G $-> H) (S : Subgroup H)
  : Subgroup G.
Proof.
  snrapply Build_Subgroup'.
  - exact (S o f).
  - hnf; exact _.
  - nrefine (transport S (grp_homo_unit f)^ _).
    apply subgroup_in_unit.
  - hnf; intros x y Sfx Sfy.
    nrefine (transport S (grp_homo_op f _ _)^ _).
    nrapply subgroup_in_op; only 1: assumption.
    nrefine (transport S (grp_homo_inv f _)^ _).
    by apply subgroup_in_inv.
Defined.

(** Every group is a (maximal) subgroup of itself *)
Definition maximal_subgroup G : Subgroup G.
Proof.
  rapply (Build_Subgroup G (fun x => Unit)).
  split; auto; exact _.
Defined.

(** We wish to coerce a group to its maximal subgroup. However, if we don't explicitly print [maximal_subgroup] things can get confusing, so we mark it as a coercion to be printed. *)
Coercion maximal_subgroup : Group >-> Subgroup.
Add Printing Coercion maximal_subgroup.

(** The group inferred from the maximal subgroup is the original group. *)
Definition grp_iso_subgroup_group_maximal (G : Group)
  : subgroup_group (maximal_subgroup G) $<~> G.
Proof.
  snrapply Build_GroupIsomorphism'.
  - rapply equiv_sigma_contr.
  - hnf; reflexivity.
Defined.

(** Paths between subgroups correspond to homotopies between the underlying predicates. *) 
Proposition equiv_path_subgroup `{F : Funext} {G : Group} (H K : Subgroup G)
  : (H == K) <~> (H = K).
Proof.
  refine ((equiv_ap' issig_subgroup^-1%equiv _ _)^-1%equiv oE _); cbn.
  refine (equiv_path_sigma_hprop _ _ oE _); cbn.
  apply equiv_path_arrow.
Defined.

Proposition equiv_path_subgroup' `{U : Univalence} {G : Group} (H K : Subgroup G)
  : (forall g:G, H g <-> K g) <~> (H = K).
Proof.
  refine (equiv_path_subgroup _ _ oE _).
  apply equiv_functor_forall_id; intro g.
  exact equiv_path_iff_ishprop.
Defined.

Global Instance ishset_subgroup `{Univalence} {G : Group} : IsHSet (Subgroup G).
Proof.
  nrefine (istrunc_equiv_istrunc _ issig_subgroup).
  nrefine (istrunc_equiv_istrunc _ (equiv_functor_sigma_id _)).
  - intro P; apply issig_issubgroup.
  - nrefine (istrunc_equiv_istrunc _ (equiv_sigma_assoc' _ _)^-1%equiv).
    nrapply istrunc_sigma.
    2: intros []; apply istrunc_hprop.
    nrefine (istrunc_equiv_istrunc
               _ (equiv_sig_coind (fun g:G => Type) (fun g x => IsHProp x))^-1%equiv).
    apply istrunc_forall.
Defined.

Section Cosets.

  (** Left and right cosets give equivalence relations. *)

  Context {G : Group} (H : Subgroup G).

  (** The relation of being in a left coset represented by an element. *)
  Definition in_cosetL : Relation G := fun x y => H (x^ * y).
  (** The relation of being in a right coset represented by an element. *)
  Definition in_cosetR : Relation G := fun x y => H (x * y^).

  Hint Extern 4 => progress unfold in_cosetL : typeclass_instances.
  Hint Extern 4 => progress unfold in_cosetR : typeclass_instances.

  Global Arguments in_cosetL /.
  Global Arguments in_cosetR /.

  (** These are props *)
  Global Instance ishprop_in_cosetL : is_mere_relation G in_cosetL := _.
  Global Instance ishprop_in_cosetR : is_mere_relation G in_cosetR := _.

  (** In fact, they are both equivalence relations. *)
  Global Instance reflexive_in_cosetL : Reflexive in_cosetL.
  Proof.
    intro x; hnf.
    rewrite left_inverse.
    apply issubgroup_in_unit.
  Defined.

  Global Instance reflexive_in_cosetR : Reflexive in_cosetR.
  Proof.
    intro x; hnf.
    rewrite right_inverse.
    apply issubgroup_in_unit.
  Defined.

  Global Instance symmetric_in_cosetL : Symmetric in_cosetL.
  Proof.
    intros x y h; cbn; cbn in h.
    rewrite <- (grp_inv_inv x).
    rewrite <- grp_inv_op.
    apply issubgroup_in_inv; assumption.
  Defined.

  Global Instance symmetric_in_cosetR : Symmetric in_cosetR.
  Proof.
    intros x y h; cbn; cbn in h.
    rewrite <- (grp_inv_inv y).
    rewrite <- grp_inv_op.
    apply issubgroup_in_inv; assumption.
  Defined.

  Global Instance transitive_in_cosetL : Transitive in_cosetL.
  Proof.
    intros x y z h k; cbn; cbn in h; cbn in k.
    rewrite <- (right_identity x^).
    rewrite <- (right_inverse y : y * y^ = mon_unit).
    rewrite (associativity x^ _ _).
    rewrite <- simple_associativity.
    apply issubgroup_in_op; assumption.
  Defined.

  Global Instance transitive_in_cosetR : Transitive in_cosetR.
  Proof.
    intros x y z h k; cbn; cbn in h; cbn in k.
    rewrite <- (right_identity x).
    rewrite <- (left_inverse y : y^ * y = mon_unit).
    rewrite (simple_associativity x).
    rewrite <- (associativity _ _ z^).
    apply issubgroup_in_op; assumption.
  Defined.

End Cosets.

(** Identities related to the left and right cosets. *)

Definition in_cosetL_unit {G : Group} {N : Subgroup G}
  : forall x y, in_cosetL N (x^ * y) mon_unit <~> in_cosetL N x y.
Proof.
  intros x y; cbn.
  rewrite (right_identity _^).
  rewrite (inverse_sg_op _).
  rewrite (inverse_involutive _).
  apply equiv_iff_hprop; apply symmetric_in_cosetL.
Defined.

Definition in_cosetR_unit {G : Group} {N : Subgroup G}
  : forall x y, in_cosetR N (x * y^) mon_unit <~> in_cosetR N x y.
Proof.
  intros x y; cbn.
  rewrite inverse_mon_unit.
  rewrite (right_identity (x * y^)).
  reflexivity.
Defined.

(** Symmetry is an equivalence. *)
Definition equiv_in_cosetL_symm {G : Group} {N : Subgroup G}
  : forall x y, in_cosetL N x y <~> in_cosetL N y x.
Proof.
  intros x y.
  srapply equiv_iff_hprop.
  all: by intro.
Defined.

Definition equiv_in_cosetR_symm {G : Group} {N : Subgroup G}
  : forall x y, in_cosetR N x y <~> in_cosetR N y x.
Proof.
  intros x y.
  srapply equiv_iff_hprop.
  all: by intro.
Defined.

(** A normal subgroup is a subgroup closed under conjugation. *)
Class IsNormalSubgroup {G : Group} (N : Subgroup G)
  := isnormal : forall {x y}, N (x * y) -> N (y * x).

Record NormalSubgroup (G : Group) := {
  normalsubgroup_subgroup : Subgroup G ;
  normalsubgroup_isnormal : IsNormalSubgroup normalsubgroup_subgroup ;
}.

Arguments Build_NormalSubgroup G N _ : rename.

Coercion normalsubgroup_subgroup : NormalSubgroup >-> Subgroup.
Global Existing Instance normalsubgroup_isnormal.

Definition equiv_symmetric_in_normalsubgroup {G : Group}
  (N : Subgroup G) `{!IsNormalSubgroup N}
  : forall x y, N (x * y) <~> N (y * x).
Proof.
  intros x y.
  rapply equiv_iff_hprop.
  all: apply isnormal.
Defined.

(** Our definiiton of normal subgroup implies the usual definition of invariance under conjugation. *)
Definition isnormal_conj {G : Group} (N : Subgroup G)
  `{!IsNormalSubgroup N} {x y : G}
  : N x <~> N (y * x * y^).
Proof.
  srefine (equiv_symmetric_in_normalsubgroup N _ _ oE _).
  by rewrite grp_inv_V_gg.
Defined.

(** We can show a subgroup is normal if it is invariant under conjugation. *)
Definition Build_IsNormalSubgroup' (G : Group) (N : Subgroup G)
  (isnormal : forall x y, N x -> N (y * x * y^))
  : IsNormalSubgroup N.
Proof.
  intros x y n.
  nrefine (transport N (grp_unit_r _) _).
  nrefine (transport (fun z => N (_ * z)) (grp_inv_r y) _).
  nrefine (transport N (grp_assoc _ _ _)^ _).
  nrefine (transport (fun z => N (z * _)) (grp_assoc _ _ _) _).
  by apply isnormal.
Defined.

(** Under funext, being a normal subgroup is a hprop. *)
Global Instance ishprop_isnormalsubgroup `{Funext} {G : Group} (N : Subgroup G)
  : IsHProp (IsNormalSubgroup N).
Proof. 
  unfold IsNormalSubgroup; exact _.
Defined.

(** Our definition of normal subgroup and the usual definition are therefore equivalent. *)
Definition equiv_isnormal_conjugate `{Funext} {G : Group} (N : Subgroup G)
  : IsNormalSubgroup N <~> (forall x y, N x -> N (y * x * y^)).
Proof.
  rapply equiv_iff_hprop.
  - intros is_normal x y.
    rapply isnormal_conj.
  - intros is_normal'.
    by snrapply Build_IsNormalSubgroup'.
Defined.

(** The trivial subgroup is a normal subgroup. *)
Global Instance isnormal_trivial_subgroup {G : Group}
  : IsNormalSubgroup (trivial_subgroup G).
Proof.
  intros x y p; cbn in p |- *.
  apply grp_moveL_1V in p.
  by apply grp_moveL_V1.
Defined.

(** The maximal subgroup (the group itself) is a normal subgroup. *)
Global Instance isnormal_maximal_subgroup {G : Group}
  : IsNormalSubgroup (maximal_subgroup G).
Proof.
  intros x y p; exact tt.
Defined.

(** Left and right cosets are equivalent in normal subgroups. *)
Definition equiv_in_cosetL_in_cosetR_normalsubgroup {G : Group}
  (N : NormalSubgroup G) (x y : G)
  : in_cosetL N x y <~> in_cosetR N x y
  := equiv_in_cosetR_symm _ _ oE equiv_symmetric_in_normalsubgroup _ _ _.

(** Inverses are then respected *)
Definition in_cosetL_inverse {G : Group} {N : NormalSubgroup G} (x y : G)
  : in_cosetL N x^ y^ <~> in_cosetL N x y.
Proof.
  refine (_ oE equiv_in_cosetL_in_cosetR_normalsubgroup _ _ _); cbn.
  by rewrite inverse_involutive.
Defined.

Definition in_cosetR_inverse {G : Group} {N : NormalSubgroup G} (x y : G)
  : in_cosetR N x^ y^ <~> in_cosetR N x y.
Proof.
  refine (_ oE equiv_in_cosetL_in_cosetR_normalsubgroup _ _ _); cbn.
  by rewrite grp_inv_inv.
Defined.

(** This lets us prove that left and right coset relations are congruences. *)
Definition in_cosetL_cong {G : Group} {N : NormalSubgroup G}
  (x x' y y' : G)
  : in_cosetL N x y -> in_cosetL N x' y' -> in_cosetL N (x * x') (y * y').
Proof.
  cbn; intros p q.
  (** rewrite goal before applying subgroup_op *)
  rewrite inverse_sg_op, <- simple_associativity.
  apply isnormal.
  rewrite simple_associativity, <- simple_associativity.
  apply subgroup_in_op.
  1: exact p.
  apply isnormal.
  exact q.
Defined.

Definition in_cosetR_cong  {G : Group} {N : NormalSubgroup G}
  (x x' y y' : G)
  : in_cosetR N x y -> in_cosetR N x' y' -> in_cosetR N (x * x') (y * y').
Proof.
  cbn; intros p q.
  (** rewrite goal before applying subgroup_op *)
  rewrite inverse_sg_op, simple_associativity.
  apply isnormal.
  rewrite <- simple_associativity, simple_associativity.
  apply subgroup_in_op.
  2: exact q.
  apply isnormal.
  exact p.
Defined.

(** The property of being the trivial group is useful. Note that any group can be automatically coerced to its maximal subgroup, so it makes sense for this predicate to be applied to groups in general. *)
Class IsTrivialGroup@{i} {G : Group@{i}} (H : Subgroup@{i i} G) :=
  istrivialgroup : forall x, H x -> trivial_subgroup G x.

Global Instance istrivial_trivial_subgroup {G : Group}
  : IsTrivialGroup (trivial_subgroup G)
  := fun x => idmap.

(** Trivial groups are isomorphic to the trivial group. *)
Definition istrivial_iff_grp_iso_trivial_subgroup {G : Group} (H : Subgroup G)
  : IsTrivialGroup H
    <-> (subgroup_group H $<~> subgroup_group (trivial_subgroup G)).
Proof.
  split.
  - intros T.
    snrapply Build_GroupIsomorphism'.
    + snrapply equiv_functor_sigma_id.
      intros x.
      rapply equiv_iff_hprop_uncurried.
      split; only 1: apply T.
      apply trivial_subgroup_rec.
    + intros [x Hx] [y Hy].
      by rapply path_sigma_hprop.
  - unfold IsTrivialGroup.
    intros e x h.
    change ((x; h).1 = (1; idpath).1).
    snrapply (pr1_path (u:=(_;_)) (v:=(_;_))).
    1: apply subgroup_in_unit.
    rhs_V nrapply (grp_homo_unit e^-1$).
    apply moveL_equiv_V.
    apply path_contr.
Defined.

(** Intersection of two subgroups *)
Definition subgroup_intersection {G : Group} (H K : Subgroup G) : Subgroup G.
Proof.
  snrapply Build_Subgroup'.
  1: exact (fun g => H g /\ K g).
  1: exact _.
  1: split; apply subgroup_in_unit.
  intros x y [] [].
  split; by apply subgroup_in_op_inv.
Defined.

(** *** The subgroup generated by a subset *)

(** Underlying type family of a subgroup generated by subset *)
Inductive subgroup_generated_type {G : Group} (X : G -> Type) : G -> Type :=
(** The subgroup should contain all elements of the original family. *)
| sgt_in (g : G) : X g -> subgroup_generated_type X g
(** It should contain the unit. *)
| sgt_unit : subgroup_generated_type X mon_unit
(** Finally, it should be closed under inverses and operation. *)
| sgt_op (g h : G)
  : subgroup_generated_type X g
  -> subgroup_generated_type X h
  -> subgroup_generated_type X (g * h^)
.

Arguments sgt_in {G X g}.
Arguments sgt_unit {G X}.
Arguments sgt_op {G X g h}.

(** Note that [subgroup_generated_type] will not automatically land in [HProp]. For example, if [X] already "contains" the unit of the group, then there are at least two different inhabitants of this family at the unit (given by [sgt_unit] and [sgt_in group_unit _]). Therefore, we propositionally truncate in [subgroup_generated] below. *)

(** Subgroups are closed under inverses. *)
Definition sgt_inv {G : Group} {X} {g : G}
  : subgroup_generated_type X g -> subgroup_generated_type X g^.
Proof.
  intros p.
  rewrite <- left_identity.
  exact (sgt_op sgt_unit p).
Defined.

Definition sgt_inv' {G : Group} {X} {g : G}
  : subgroup_generated_type X g^ -> subgroup_generated_type X g.
Proof.
  intros p.
  rewrite <- grp_inv_inv.
  by apply sgt_inv.
Defined.

Definition sgt_op' {G : Group} {X} {g h : G}
  : subgroup_generated_type X g
    -> subgroup_generated_type X h
    -> subgroup_generated_type X (g * h).
Proof.
  intros p q.
  rewrite <- (inverse_involutive h).
  exact (sgt_op p (sgt_inv q)).
Defined.

(** The subgroup generated by a subset *)
Definition subgroup_generated {G : Group} (X : G -> Type) : Subgroup G.
Proof.
  refine (Build_Subgroup' (merely o subgroup_generated_type X)
            (tr sgt_unit) _).
  intros x y p q; strip_truncations.
  exact (tr (sgt_op p q)).
Defined.

(** The inclusion of generators into the generated subgroup. *)
Definition subgroup_generated_gen_incl {G : Group} {X : G -> Type} (g : G) (H : X g)
  : subgroup_generated X
  := (g; tr (sgt_in H)).

(** The generated subgroup is the smallest subgroup containing the generating set. *)
Definition subgroup_generated_rec {G : Group} (X : G -> Type) (S : Subgroup G)
  (i : forall g, X g -> S g)
  : forall g, subgroup_generated X g -> S g.
Proof.
  intros g; rapply Trunc_rec; intros p.
  induction p as [g Xg | | g h p1 IHp1 p2 IHp2].
  - by apply i.
  - apply subgroup_in_unit.
  - by apply subgroup_in_op_inv.
Defined.

(** If [f : G $-> H] is a group homomorphism and [X] and [Y] are subsets of [G] and [H] such that [f] maps [X] into [Y], then [f] sends the subgroup generated by [X] into the subgroup generated by [Y]. *)
Definition functor_subgroup_generated {G H : Group} (X : G -> Type) (Y : H -> Type)
  (f : G $-> H) (preserves : forall g, X g -> Y (f g))
  : forall g, subgroup_generated X g -> subgroup_generated Y (f g).
Proof.
  change (subgroup_generated Y (f ?g))
    with (subgroup_preimage f (subgroup_generated Y) g).
  apply subgroup_generated_rec.
  intros g p.
  apply tr, sgt_in.
  by apply preserves.
Defined.

(** The product of two subgroups. *)
Definition subgroup_product {G : Group} (H K : Subgroup G) : Subgroup G
  := subgroup_generated (fun x => ((H x) + (K x))%type).

(** The induction principle for the product. *)
Definition subgroup_product_ind {G : Group} (H K : Subgroup G)
  (P : forall x, subgroup_product H K x -> Type)
  (P_H_in : forall x y, P x (tr (sgt_in (inl y))))
  (P_K_in : forall x y, P x (tr (sgt_in (inr y))))
  (P_unit : P mon_unit (tr sgt_unit))
  (P_op : forall x y h k, P x (tr h) -> P y (tr k) -> P (x * - y) (tr (sgt_op h k)))
  `{forall x y, IsHProp (P x y)}
  : forall x (p : subgroup_product H K x), P x p.
Proof.
  intros x p.
  strip_truncations.
  induction p as [x s | | x y h IHh k IHk].
  + destruct s.
    - apply P_H_in.
    - apply P_K_in.
  + exact P_unit.
  + by apply P_op.
Defined.

(* **** Paths between generated subgroups *)

(* This gets used twice in [path_subgroup_generated], so we factor it out here. *)
Local Lemma path_subgroup_generated_helper {G : Group}
  (X Y : G -> Type) (K : forall g, merely (X g) -> merely (Y g))
  : forall g, Trunc (-1) (subgroup_generated_type X g)
         -> Trunc (-1) (subgroup_generated_type Y g).
Proof.
  intro g; apply Trunc_rec; intro ing.
  induction ing as [g x| |g h Xg IHYg Xh IHYh].
  - exact (Trunc_functor (-1) sgt_in (K g (tr x))).
  - exact (tr sgt_unit).
  - strip_truncations.
    by apply tr, sgt_op.
Defined.

(* If the predicates selecting the generators are merely equivalent, then the generated subgroups are equal. (One could probably prove that the generated subgroup are isomorphic without using univalence.) *)
Definition path_subgroup_generated `{Univalence} {G : Group}
  (X Y : G -> Type) (K : forall g, Trunc (-1) (X g) <-> Trunc (-1) (Y g))
  : subgroup_generated X = subgroup_generated Y.
Proof.
  rapply equiv_path_subgroup'. (* Uses Univalence. *)
  intro g; split.
  - apply path_subgroup_generated_helper, (fun x => fst (K x)).
  - apply path_subgroup_generated_helper, (fun x => snd (K x)).
Defined.

(* Equal subgroups have isomorphic underlying groups. *)
Definition equiv_subgroup_group {G : Group} (H1 H2 : Subgroup G)
  : H1 = H2 -> GroupIsomorphism H1 H2
  := ltac:(intros []; exact grp_iso_id).
