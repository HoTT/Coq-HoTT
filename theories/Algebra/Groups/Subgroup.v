Require Import Basics Types HFiber WildCat.Core WildCat.Equiv.
Require Import Truncations.Core Modalities.Modality.
Require Export Modalities.Modality (conn_map_factor1_image).
Require Import Algebra.Groups.Group Universes.TruncType Universes.HSet.

Local Open Scope predicate_scope.
Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

Generalizable Variables G H A B C N f g.

(** * Subgroups *)

(** ** Definition of being a subgroup *)

(** A subgroup H of a group G is a predicate (i.e. an hProp-valued type family) on G which is closed under the group operations. The group underlying H is given by the total space { g : G & H g }, defined in [subgroup_group] below. *)
Class IsSubgroup {G : Group} (H : G -> Type) := {
  issubgroup_predicate :: forall x, IsHProp (H x) ;
  issubgroup_in_unit : H mon_unit ;
  issubgroup_in_op : forall x y, H x -> H y -> H (x * y) ;
  issubgroup_in_inv : forall x, H x -> H x^ ;
}.

Definition issig_issubgroup {G : Group} (H : G -> Type) : _ <~> IsSubgroup H
  := ltac:(issig).

(** Basic properties of subgroups *)

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

(** Given a predicate H on a group G, being a subgroup is a property. *)
Instance ishprop_issubgroup `{F : Funext} {G : Group} {H : G -> Type}
  : IsHProp (IsSubgroup H).
Proof.
  exact (istrunc_equiv_istrunc _ (issig_issubgroup H)).
Defined.

(** Transporting being a subgroup across a pointwise equivalence. *)
Definition issubgroup_equiv {G : Group} {H K : G -> Type}
  (p : forall g, H g <~> K g)
  : IsSubgroup H -> IsSubgroup K.
Proof.
  intros H1.
  snapply Build_IsSubgroup.
  - intros x.
    rapply (istrunc_equiv_istrunc (H x)).
    apply p.
  - apply p, issubgroup_in_unit.
  - intros x y inx iny.
    apply (p _)^-1 in inx, iny.
    exact (p _ (issubgroup_in_op x y inx iny)).
  - intros x inx.
    apply (p _)^-1 in inx.
    exact (p _ (issubgroup_in_inv x inx)).
Defined.

(** ** Definition of subgroup *) 

(** The type (set) of subgroups of a group G. *)
Record Subgroup (G : Group) := {
  subgroup_pred : G -> Type ;
  subgroup_issubgroup :: IsSubgroup subgroup_pred ;
}.

Coercion subgroup_pred : Subgroup >-> Funclass.

Definition issig_subgroup {G : Group} : _ <~> Subgroup G
  := ltac:(issig).

(** ** Basics properties of subgroups *)

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

Instance isequiv_subgroup_in_inv `(H : Subgroup G) (x : G)
  : IsEquiv (subgroup_in_inv H x).
Proof.
  srapply isequiv_iff_hprop.
  apply subgroup_in_inv'.
Defined.

Definition equiv_subgroup_inv {G : Group} (H : Subgroup G) (x : G)
  : H x <~> H x^ := Build_Equiv _ _ (subgroup_in_inv H x) _.

Definition equiv_subgroup_op_inv {G : Group} (H : Subgroup G) (x y : G)
  : H (x * y^) <~> H (y * x^).
Proof.
  nrefine (_ oE equiv_subgroup_inv _ _).
  by rewrite grp_inv_op, grp_inv_inv.
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
  : (pred_eq H K) <~> (H = K).
Proof.
  refine (equiv_path_subgroup _ _ oE _).
  apply equiv_functor_forall_id; intro g.
  exact equiv_path_iff_ishprop.
Defined.

Instance ishset_subgroup `{Univalence} {G : Group} : IsHSet (Subgroup G).
Proof.
  nrefine (istrunc_equiv_istrunc _ issig_subgroup).
  nrefine (istrunc_equiv_istrunc _ (equiv_functor_sigma_id _)).
  - intro P; apply issig_issubgroup.
  - nrefine (istrunc_equiv_istrunc _ (equiv_sigma_assoc' _ _)^-1%equiv).
    napply istrunc_sigma.
    2: intros []; apply istrunc_hprop.
    nrefine (istrunc_equiv_istrunc
               _ (equiv_sig_coind (fun g:G => Type) (fun g x => IsHProp x))^-1%equiv).
    apply istrunc_forall.
Defined.

(** ** Underlying group of a subgroup *)

(** The group given by a subgroup *)
Definition subgroup_group {G : Group} (H : Subgroup G) : Group.
Proof.
  apply (Build_Group (sig H)
      (fun x y => (x.1 * y.1 ; issubgroup_in_op x.1 y.1 x.2 y.2))
      (1; issubgroup_in_unit)
      (fun x => (- x.1 ; issubgroup_in_inv _ x.2))).
  1: repeat split.
  1: exact _.
  1-5: grp_auto.
Defined.

Coercion subgroup_group : Subgroup >-> Group.

(** Equal subgroups have isomorphic underlying groups. *)
Definition equiv_subgroup_group {G : Group} (H1 H2 : Subgroup G)
  : H1 = H2 -> GroupIsomorphism H1 H2
  := ltac:(intros []; exact grp_iso_id).

(** The underlying group of a subgroup of [G] has an inclusion map into [G]. *) 
Definition subgroup_incl {G : Group} (H : Subgroup G)
  : subgroup_group H $-> G.
Proof.
  snapply Build_GroupHomomorphism.
  1: exact pr1.
  hnf; reflexivity.
Defined.

(** The inclusion map is an embedding. *)
Instance isembedding_subgroup_incl {G : Group} (H : Subgroup G)
  : IsEmbedding (subgroup_incl H)
  := fun _ => istrunc_equiv_istrunc _ (hfiber_fibration _ _).

(** Restriction of a group homomorphism to a subgroup. *)
Definition grp_homo_restr {G H : Group} (f : G $-> H) (K : Subgroup G)
  : subgroup_group K $-> H
  := f $o subgroup_incl _.

(** Corestriction of a group homomorphism to a subgroup. *)
Definition subgroup_corec {G H : Group} {K : Subgroup H}
  (f : G $-> H) (g : forall x, K (f x))
  : G $-> subgroup_group K.
Proof.
  snapply Build_GroupHomomorphism.
  - exact (fun x => (f x; g x)).
  - intros x y.
    rapply path_sigma_hprop.
    snapply grp_homo_op.
Defined.

(** Corestriction is an equivalence on group homomorphisms. *)
Definition equiv_subgroup_corec {F : Funext}
  (G : Group) {H : Group} (K : Subgroup H)
  : {f : G $-> H & forall x, K (f x)} <~> (G $-> subgroup_group K).
Proof.
  snapply equiv_adjointify.
  - exact (sig_rec subgroup_corec).
  - intros g.
    exists (subgroup_incl _ $o g).
    intros x.
    exact (g x).2.
  - intros g.
    by snapply equiv_path_grouphomomorphism.
  - intros [f p].
    rapply path_sigma_hprop.
    by snapply equiv_path_grouphomomorphism.
Defined.

(** Functoriality on subgroups. *)
Definition functor_subgroup_group {G H : Group} {J : Subgroup G} {K : Subgroup H}
  (f : G $-> H) (g : forall x, J x -> K (f x))
  : subgroup_group J $-> subgroup_group K
  := subgroup_corec (grp_homo_restr f J) (sig_ind _ g).

Definition grp_iso_subgroup_group {G H : Group@{i}}
  {J : Subgroup@{i i} G} {K : Subgroup@{i i} H}
  (e : G $<~> H) (f : forall x, J x <-> K (e x))
  : subgroup_group J $<~> subgroup_group K.
Proof.
  snapply cate_adjointify.
  - exact (functor_subgroup_group e (fun x => fst (f x))).
  - nrefine (functor_subgroup_group e^-1$ _).
    equiv_intro e x. 
    intros k.
    nrefine ((eissect e _)^ # _).
    exact (snd (f x) k).
  - intros x.
    rapply path_sigma_hprop.
    napply eisretr.
  - intros x.
    rapply path_sigma_hprop.
    napply eissect.
Defined.

(** ** Cosets of subgroups *)

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
  #[export] Instance ishprop_in_cosetL : is_mere_relation G in_cosetL := _.
  #[export] Instance ishprop_in_cosetR : is_mere_relation G in_cosetR := _.

  (** In fact, they are both equivalence relations. *)
  #[export] Instance reflexive_in_cosetL : Reflexive in_cosetL.
  Proof.
    intro x; hnf.
    rewrite left_inverse.
    exact issubgroup_in_unit.
  Defined.

  #[export] Instance reflexive_in_cosetR : Reflexive in_cosetR.
  Proof.
    intro x; hnf.
    rewrite right_inverse.
    exact issubgroup_in_unit.
  Defined.

  #[export] Instance symmetric_in_cosetL : Symmetric in_cosetL.
  Proof.
    intros x y h; cbn; cbn in h.
    rewrite <- (grp_inv_inv x).
    rewrite <- grp_inv_op.
    apply issubgroup_in_inv; assumption.
  Defined.

  #[export] Instance symmetric_in_cosetR : Symmetric in_cosetR.
  Proof.
    intros x y h; cbn; cbn in h.
    rewrite <- (grp_inv_inv y).
    rewrite <- grp_inv_op.
    apply issubgroup_in_inv; assumption.
  Defined.

  #[export] Instance transitive_in_cosetL : Transitive in_cosetL.
  Proof.
    intros x y z h k; cbn; cbn in h; cbn in k.
    rewrite <- (right_identity x^).
    rewrite <- (right_inverse y : y * y^ = mon_unit).
    rewrite (associativity x^ _ _).
    rewrite <- simple_associativity.
    apply issubgroup_in_op; assumption.
  Defined.

  #[export] Instance transitive_in_cosetR : Transitive in_cosetR.
  Proof.
    intros x y z h k; cbn; cbn in h; cbn in k.
    rewrite <- (right_identity x).
    rewrite <- (left_inverse y : y^ * y = mon_unit).
    rewrite (simple_associativity x).
    rewrite <- (associativity _ _ z^).
    apply issubgroup_in_op; assumption.
  Defined.

End Cosets.

(** ** Properties of left and right cosets *)

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

(** The sigma type of a left coset is equivalent to the sigma type of the subgroup. *)
Definition equiv_sigma_in_cosetL_subgroup (G : Group) (H : Subgroup G) (x : G)
  : sig (in_cosetL H x) <~> sig H.
Proof.
  snapply equiv_functor_sigma'.
  - rapply (Build_Equiv _ _ (x^ *.)).
  - reflexivity.
Defined.

(** The sigma type of a right coset is equivalent to the sigma type of the subgroup. *)
Definition equiv_sigma_in_cosetR_subgroup (G : Group) (H : Subgroup G) (x : G)
  : sig (in_cosetR H x) <~> sig H.
Proof.
  snapply equiv_functor_sigma'.
  - rapply (Build_Equiv _ _ (.* x ^)).
  - simpl; intros y.
    apply equiv_subgroup_op_inv.
Defined.

(** ** Normal subgroups *)

(** A normal subgroup is a subgroup closed under conjugation. *)
Class IsNormalSubgroup {G : Group} (N : Subgroup G)
  := isnormal : forall {x y}, N (x * y) -> N (y * x).

Record NormalSubgroup (G : Group) := {
  normalsubgroup_subgroup : Subgroup G ;
  normalsubgroup_isnormal :: IsNormalSubgroup normalsubgroup_subgroup ;
}.

Arguments Build_NormalSubgroup G N _ : rename.

Coercion normalsubgroup_subgroup : NormalSubgroup >-> Subgroup.

Definition equiv_symmetric_in_normalsubgroup {G : Group}
  (N : Subgroup G) `{!IsNormalSubgroup N}
  : forall x y, N (x * y) <~> N (y * x).
Proof.
  intros x y.
  rapply equiv_iff_hprop.
  all: exact isnormal.
Defined.

(** Our definition of normal subgroup implies the usual definition of invariance under conjugation. *)
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
Instance ishprop_isnormalsubgroup `{Funext} {G : Group} (N : Subgroup G)
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
    by snapply Build_IsNormalSubgroup'.
Defined.

(** Inner automorphisms of a group [G] restrict to automorphisms of normal subgroups. *)
Definition grp_iso_normal_conj {G : Group} (N : Subgroup G)
  `{!IsNormalSubgroup N} (x : G)
  : subgroup_group N $<~> subgroup_group N.
Proof.
  snapply grp_iso_subgroup_group.
  - exact (grp_iso_conj x).
  - intros y.
    rapply isnormal_conj.
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

(** ** Trivial subgroup *)

(** The trivial subgroup of a group [G]. *)
Definition trivial_subgroup G : Subgroup G.
Proof.
  rapply (Build_Subgroup' (fun x => x = 1)).
  1: reflexivity.
  intros x y p q.
  destruct p^%path, q^%path.
  lhs apply left_identity.
  apply grp_inv_unit.
Defined.

(** The trivial subgroup is always included in any subgroup. *)
Definition trivial_subgroup_rec {G : Group} (H : Subgroup G)
  : forall x, trivial_subgroup G x -> H x.
Proof.
  napply paths_ind_r; cbn beta.
  exact issubgroup_in_unit.
Defined.

(** The trivial subgroup is a normal subgroup. *)
Instance isnormal_trivial_subgroup {G : Group}
  : IsNormalSubgroup (trivial_subgroup G).
Proof.
  intros x y p; cbn in p |- *.
  apply grp_moveL_1V in p.
  by apply grp_moveL_V1.
Defined.

(** The property of being the trivial subgroup. Note that any group can be automatically coerced to its maximal subgroup, so it makes sense for this predicate to be applied to groups in general. *)
Class IsTrivialGroup@{i} {G : Group@{i}} (H : Subgroup@{i i} G) :=
  istrivialgroup : forall x, H x -> trivial_subgroup G x.

Instance ishprop_istrivialgroup `{F : Funext} {G : Group} (H : Subgroup G)
  : IsHProp (IsTrivialGroup H)
  := istrunc_forall.

Instance istrivial_trivial_subgroup {G : Group}
  : IsTrivialGroup (trivial_subgroup G)
  := fun x => idmap.

(** Trivial groups are isomorphic to the trivial group. *)
Definition istrivial_iff_grp_iso_trivial {G : Group} (H : Subgroup G)
  : IsTrivialGroup H <-> (subgroup_group H $<~> grp_trivial).
Proof.
  split.
  - intros triv.
    snapply cate_adjointify.
    1,2: exact grp_homo_const.
    + by intros [].
    + intros [x Hx]; simpl.
      apply path_sigma_hprop.
      symmetry.
      by apply triv.
  - intros e x Hx.
    change ((x; Hx).1 = (1; idpath).1).
    snapply (pr1_path (u:=(_;_)) (v:=(_;_))).
    1: apply subgroup_in_unit.
    rhs_V exact (grp_homo_unit e^-1$).
    apply moveL_equiv_V.
    apply path_contr.
Defined.

(** All trivial subgroups are isomorphic as groups. *)
Definition grp_iso_trivial_subgroup (G H : Group)
  : subgroup_group (trivial_subgroup G)
    $<~> subgroup_group (trivial_subgroup H).
Proof.
  snrefine (_^-1$ $oE _).
  1: exact grp_trivial.
  1,2: apply istrivial_iff_grp_iso_trivial; exact _.
Defined.

Definition istrivial_grp_iso {G H : Group} (J : Subgroup G) (K : Subgroup H)
  (e : subgroup_group J $<~> subgroup_group K)
  : IsTrivialGroup J -> IsTrivialGroup K.
Proof.
  intros triv.
  apply istrivial_iff_grp_iso_trivial in triv.
  apply istrivial_iff_grp_iso_trivial.
  exact (triv $oE e^-1$).
Defined.

(** ** Maximal Subgroups *)

(** Every group is a (maximal) subgroup of itself. *)
Definition maximal_subgroup G : Subgroup G.
Proof.
  rapply (Build_Subgroup G (fun x => Unit)).
  split; auto; exact _.
Defined.

(** We wish to coerce a group to its maximal subgroup. However, if we don't explicitly print [maximal_subgroup] things can get confusing, so we mark it as a coercion to be printed. *)
Coercion maximal_subgroup : Group >-> Subgroup.
Add Printing Coercion maximal_subgroup.

(** The group associated to the maximal subgroup is the original group. Note that this equivalence does not characterize the maximal subgroup, as a proper subgroup can be isomorphic to the whole group. For example, the even integers are isomorphic to the integers. *)
Definition grp_iso_subgroup_group_maximal (G : Group)
  : subgroup_group (maximal_subgroup G) $<~> G.
Proof.
  snapply Build_GroupIsomorphism'.
  - rapply equiv_sigma_contr.
  - hnf; reflexivity.
Defined.

(** The maximal subgroup (the group itself) is a normal subgroup. *)
Instance isnormal_maximal_subgroup {G : Group}
  : IsNormalSubgroup (maximal_subgroup G).
Proof.
  intros x y p; exact tt.
Defined.

(** The property of being a maximal subgroup of a group [G]. *)
Class IsMaximalSubgroup {G : Group} (H : Subgroup G) :=
  ismaximalsubgroup : forall (x : G), H x.

Instance ishprop_ismaximalsubgroup `{Funext}
  {G : Group} (H : Subgroup G)
  : IsHProp (IsMaximalSubgroup H)
  := istrunc_forall.

Instance ismaximalsubgroup_maximalsubgroup {G : Group}
  : IsMaximalSubgroup (maximal_subgroup G)
  := fun g => tt.

(** ** Subgroups in opposite group *)

Instance issubgroup_grp_op {G : Group} (H : G -> Type)
  : IsSubgroup H -> IsSubgroup (G:=grp_op G) H.
Proof.
  intros H1.
  snapply Build_IsSubgroup'.
  - exact _.
  - cbn; exact issubgroup_in_unit.
  - intros x y Hx Hy; cbn.
    by apply issubgroup_in_inv_op.
Defined.

(** Note that [grp_op] is definitionally involutive, so the next result also gives us a map [Subgroup (grp_op G) -> Subgroup G]. *)
Definition subgroup_grp_op {G : Group} (H : Subgroup G)
  : Subgroup (grp_op G)
  := Build_Subgroup (grp_op G) H _.

Instance isnormal_subgroup_grp_op {G : Group} (H : Subgroup G)
  : IsNormalSubgroup H -> IsNormalSubgroup (subgroup_grp_op H).
Proof.
  intros n x y; cbn.
  exact isnormal.
Defined.

Definition normalsubgroup_grp_op {G : Group}
  : NormalSubgroup G -> NormalSubgroup (grp_op G)
  := fun N => Build_NormalSubgroup (grp_op G) (subgroup_grp_op N) _.

(** ** Subgroup intersection *)

(** Intersection of two subgroups *)
Definition subgroup_intersection {G : Group} (H K : Subgroup G) : Subgroup G.
Proof.
  snapply (Build_Subgroup' (pred_and H K)).
  1: exact _.
  1: split; apply subgroup_in_unit.
  intros x y [] [].
  split; by apply subgroup_in_op_inv.
Defined.

(** Intersection of a family of subgroups *)
Definition subgroup_intersection_family {G : Group} (I : Type) (H : I -> Subgroup G)
  : Subgroup G.
Proof.
  (* We insert [merely] to avoid needing [Funext]. *)
  snapply (Build_Subgroup' (fun g => merely (forall i, H i g))).
  - exact _.
  - apply tr.
    intro i; apply subgroup_in_unit.
  - cbn.
    intros x y Hx Hy.
    strip_truncations; apply tr.
    intro i; by apply subgroup_in_op_inv.
Defined.

(** ** Preimage subgroup *)

(** The preimage of a subgroup under a group homomorphism is a subgroup. *)
Instance issubgroup_preimage {G H : Group} (f : G $-> H) (S : H -> Type)
  : IsSubgroup S -> IsSubgroup (S o f).
Proof.
  intros H1.
  snapply Build_IsSubgroup'.
  - hnf; exact _.
  - nrefine (transport S (grp_homo_unit f)^ _).
    exact issubgroup_in_unit.
  - hnf; intros x y Sfx Sfy.
    nrefine (transport S (grp_homo_op f _ _)^ _).
    rapply issubgroup_in_op; only 1: assumption.
    nrefine (transport S (grp_homo_inv f _)^ _).
    by apply issubgroup_in_inv.
Defined.

Definition subgroup_preimage {G H : Group} (f : G $-> H) (S : Subgroup H)
  : Subgroup G
  := Build_Subgroup G (S o f) _.

(** The preimage of a normal subgroup is again normal. *)
Instance isnormal_subgroup_preimage {G H : Group} (f : G $-> H)
  (N : Subgroup H) `{!IsNormalSubgroup N}
  : IsNormalSubgroup (subgroup_preimage f N).
Proof.
  intros x y Nfxy; simpl.
  nrefine (transport N (grp_homo_op _ _ _)^ _).
  apply isnormal.
  exact (transport N (grp_homo_op _ _ _) Nfxy).
Defined.

Definition functor_subgroup_preimage {G H : Group} (f : G $-> H)
  {S T : Subgroup H} (p : S ⊆ T)
  : subgroup_preimage f S ⊆ subgroup_preimage f T
  := p o f.

(** The preimage of an intersection is the intersection of preimages. *)
Definition subgroup_preimage_intersection {G H : Group} (f : G $-> H)
  (S T : Subgroup H)
  : subgroup_preimage f (subgroup_intersection S T)
    ↔ subgroup_intersection (subgroup_preimage f S) (subgroup_preimage f T)
  := reflexivity _.

(** ** Simple groups *)

Class IsSimpleGroup (G : Group)
  := is_simple_group : forall (N : Subgroup G) `{IsNormalSubgroup G N},
    IsTrivialGroup N + IsMaximalSubgroup N.

(** ** The subgroup generated by a subset *)

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

Definition subgroup_generated_in {G : Group} {X : G -> Type}
  : X ⊆ subgroup_generated X
  := fun _ => (tr o sgt_in).

(** The inclusion of generators into the generated subgroup. *)
Definition subgroup_generated_gen_incl {G : Group} {X : G -> Type} (g : G) (H : X g)
  : subgroup_generated X
  := (g; tr (sgt_in H)).

(** The generated subgroup is the smallest subgroup containing the generating set. *)
Definition subgroup_generated_rec {G : Group} (X : G -> Type) (S : Subgroup G)
  (i : X ⊆ S)
  : subgroup_generated X ⊆ S.
Proof.
  intros g; rapply Trunc_rec; intros p.
  induction p as [g Xg | | g h p1 IHp1 p2 IHp2].
  - by apply i.
  - apply subgroup_in_unit.
  - by apply subgroup_in_op_inv.
Defined.

(** If [f : G $-> H] is a group homomorphism and [X] and [Y] are subsets of [G] and [H] such that [f] maps [X] into [Y], then [f] sends the subgroup generated by [X] into the subgroup generated by [Y]. *)
Definition functor_subgroup_generated {G H : Group}
  (X : G -> Type) (Y : H -> Type) (f : G $-> H) (preserves : X ⊆ (Y o f))
  : subgroup_generated X ⊆ (subgroup_generated Y o f).
Proof.
  apply (subgroup_generated_rec _ (subgroup_preimage f (subgroup_generated Y))).
  transitivity (Y o f).
  1: apply preserves.
  apply (pred_subset_precomp f).
  apply subgroup_generated_in.
Defined.

Definition functor_subgroup_generated' {G : Group}
  (X : G -> Type) (Y : G -> Type) (preserves : pred_subset X Y)
  : subgroup_generated X ⊆ subgroup_generated Y
  := functor_subgroup_generated X Y (Id _) preserves.

Definition subgroup_eq_functor_subgroup_generated {G H : Group}
  (X : G -> Type) (Y : H -> Type) (f : G $<~> H) (preserves : X ↔ (Y o f))
  : subgroup_generated X ↔ (subgroup_generated Y o f).
Proof.
  apply pred_subset_antisymm.
  - apply functor_subgroup_generated.
    exact preserves.
  - apply (pred_subset_moveR_equiv f).
    apply (functor_subgroup_generated _ _ f^-1$).
    apply (pred_subset_moveL_equiv f^-1$); cbn.
    apply pred_subset_pred_eq.
    by symmetry.
Defined.

(** A similar result is true if we replace one group by its opposite, i.e. if [f] is an anti-homomorphism.  For simplicity, we state this only for the case in which [f] is the identity isomorphism.  It's also useful in the special case where [X] and [Y] are the same. *)
Definition subgroup_eq_subgroup_generated_op {G : Group}
  (X : G -> Type) (Y : G -> Type) (preserves : X ↔ Y)
  : subgroup_generated X ↔ subgroup_generated (G:=grp_op G) Y.
Proof.
  intro g; split.
  1: change (subgroup_generated X g -> subgroup_grp_op (subgroup_generated (G:=grp_op G) Y) g).
  2: change (subgroup_generated (G:=grp_op G) Y g -> subgroup_grp_op (subgroup_generated X) g).
  all: apply subgroup_generated_rec.
  all: intros x Xx.
  all: apply (tr o sgt_in).
  all: by apply (preserves x).
Defined.

(** ** Subgroups generated by propositionally truncated predicates *)

(** Propositionally truncating the predicate determining a generating subset does not change the subgroup it generates. *)
Definition subgroup_generated_merely {G : Group} (X : G -> Type)
  : subgroup_generated X ↔ subgroup_generated (merely o X).
Proof.
  apply pred_subset_antisymm.
  - apply functor_subgroup_generated'.
    exact (fun g => tr).
  - intro g.
    intro ing.
    strip_truncations.
    induction ing as [g x| |g h Xg IHYg Xh IHYh].
    + exact (Trunc_functor (-1) sgt_in x).
    + exact (tr sgt_unit).
    + strip_truncations.
      by apply tr, sgt_op.
Defined.

(** If the truncated predicates are related by [pred_subset], then so are the generated subgroups. *)
Definition functor_subgroup_generated_merely {G : Group} (X Y : G -> Type)
  (K : (merely o X) ⊆ (merely o Y))
  : subgroup_generated X ⊆ subgroup_generated Y.
Proof.
  transitivity (subgroup_generated (merely o X)).
  1: apply pred_subset_pred_eq, subgroup_generated_merely.
  transitivity (subgroup_generated (merely o Y)).
  1: by apply functor_subgroup_generated'.
  apply pred_subset_pred_eq', subgroup_generated_merely.
Defined.

Definition subgroup_eq_functor_subgroup_generated_merely {G : Group}
  (X Y : G -> Type) (K : (merely o X) ↔ (merely o Y))
  : subgroup_generated X ↔ subgroup_generated Y.
Proof.
  apply pred_subset_antisymm; apply functor_subgroup_generated_merely.
  - apply pred_subset_pred_eq, K.
  - apply pred_subset_pred_eq', K.
Defined.

(** If the predicates selecting the generators are merely equivalent, then the generated subgroups are isomorphic. *)
Definition grp_iso_subgroup_generated_merely  {G : Group} (X Y : G -> Type)
  (K : (merely o X) ↔ (merely o Y))
  : subgroup_group (subgroup_generated X) $<~> subgroup_group (subgroup_generated Y).
Proof.
  apply (grp_iso_subgroup_group grp_iso_id).
  by apply subgroup_eq_functor_subgroup_generated_merely.
Defined.

(** If the predicates selecting the generators are merely equivalent, then the generated subgroups are equal. *)
Definition path_subgroup_generated `{Univalence} {G : Group}
  (X Y : G -> Type) (K : (merely o X) ↔ (merely o Y))
  : subgroup_generated X = subgroup_generated Y.
Proof.
  rapply equiv_path_subgroup'. (* Uses Univalence. *)
  by apply subgroup_eq_functor_subgroup_generated_merely.
Defined.

(** ** Product of subgroups *)

(** The product of two subgroups. *)
Definition subgroup_product {G : Group} (H K : Subgroup G) : Subgroup G
  := subgroup_generated (pred_or H K).

Definition subgroup_product_incl_l {G : Group} {H K : Subgroup G}
  : H ⊆ subgroup_product H K
  := fun x => subgroup_generated_in _ o inl.

Definition subgroup_product_incl_r {G : Group} {H K : Subgroup G}
  : K ⊆ subgroup_product H K
  := fun x => subgroup_generated_in _ o inr.

(** The induction principle for the product. *)
Definition subgroup_product_ind {G : Group} (H K : Subgroup G)
  (P : forall x, subgroup_product H K x -> Type)
  (P_H_in : forall x y, P x (subgroup_product_incl_l _ y))
  (P_K_in : forall x y, P x (subgroup_product_incl_r _ y))
  (P_unit : P mon_unit (tr sgt_unit))
  (P_op : forall x y h k, P x (tr h) -> P y (tr k)
    -> P (x * y^) (tr (sgt_op h k)))
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

(** The product subgroup is the smallest subgroup containing the factors. *)
Definition subgroup_product_smallest {G : Group} (H K L : Subgroup G)
  : H ⊆ L -> K ⊆ L -> subgroup_product H K ⊆ L.
Proof.
  intros p q.
  napply subgroup_generated_rec.
  intros x [h | k].
  - by apply p.
  - by apply q.
Defined.

(** Subgroup products are commutative *)
Definition subgroup_product_comm {G : Group} (H K : Subgroup G)
  : subgroup_product H K ↔ subgroup_product K H.
Proof.
  apply pred_subset_antisymm; apply subgroup_product_smallest.
  1,3: apply subgroup_product_incl_r.
  1,2: apply subgroup_product_incl_l.
Defined.

(** The trivial subgroup is a left identity. *)
Definition subgroup_product_trivial_l {G : Group} (H : Subgroup G)
  : subgroup_product (trivial_subgroup G) H ↔ H.
Proof.
  apply pred_subset_antisymm.
  { apply subgroup_product_smallest.
    - napply trivial_subgroup_rec.
    - reflexivity. }
  apply subgroup_product_incl_r.
Defined.

(** The trivial subgroup is a right identity. *)
Definition subgroup_product_trivial_r {G : Group} (H : Subgroup G)
  : subgroup_product H (trivial_subgroup G) ↔ H.
Proof.
  apply pred_subset_antisymm.
  { apply subgroup_product_smallest.
    - reflexivity.
    - napply trivial_subgroup_rec. }
  apply subgroup_product_incl_l.
Defined.

(** Subgroups absorb themselves under products. *)
Definition subgroup_product_self {G : Group} (H : Subgroup G)
  : subgroup_product H H ↔ H.
Proof.
  apply pred_subset_antisymm.
  1: by rapply subgroup_product_smallest.
  apply subgroup_product_incl_l.
Defined.

(** Products preserve inclusions in the left summand. *)
Definition subgroup_product_subset_pres_l {G : Group} (H K L : Subgroup G)
  : H ⊆ K -> subgroup_product H L ⊆ subgroup_product K L.
Proof.
  intros p.
  apply subgroup_product_smallest.
  1: exact (transitivity p subgroup_product_incl_l).
  apply subgroup_product_incl_r.
Defined.

(** Products preserve inclusions in the right summand. *)
Definition subgroup_product_subset_pres_r {G : Group} (H K L : Subgroup G)
  : H ⊆ K -> subgroup_product L H ⊆ subgroup_product L K.
Proof.
  intros p.
  apply subgroup_product_smallest.
  1: apply subgroup_product_incl_l.
  1: exact (transitivity p subgroup_product_incl_r).
Defined.

(** Products preserve inclusions in both summands. *)
Definition subgroup_product_subset_pres {G : Group} (H K L M : Subgroup G)
  (p : H ⊆ K) (q : L ⊆ M)
  : subgroup_product H L ⊆ subgroup_product K M.
Proof.
  transitivity (subgroup_product K L).
  1: by apply subgroup_product_subset_pres_l.
  by apply subgroup_product_subset_pres_r.
Defined.

(** Products preserve subgroup equality in both summands. *)
Definition subgroup_product_eq {G : Group} (H K L M : Subgroup G)
  (p : H ↔ K) (q : L ↔ M)
  : subgroup_product H L ↔ subgroup_product K M.
Proof.
  by apply pred_subset_antisymm; apply subgroup_product_subset_pres;
    apply pred_subset_pred_eq.
Defined.

(** A product of normal subgroups is normal. *)
Instance isnormal_subgroup_product {G : Group} (H K : Subgroup G)
  `{!IsNormalSubgroup H, !IsNormalSubgroup K}
  : IsNormalSubgroup (subgroup_product H K).
Proof.
  snapply Build_IsNormalSubgroup'.
  intros x y; revert x.
  napply (functor_subgroup_generated _ _ (grp_conj y)).
  intros x.
  apply functor_sum; rapply isnormal_conj.
Defined.

Definition normalsubgroup_product {G : Group} (H K : NormalSubgroup G)
  : NormalSubgroup G
  := Build_NormalSubgroup G (subgroup_product H K) _.

Definition functor_subgroup_product {G H : Group}
  {J K : Subgroup G} {L M : Subgroup H}
  (f : G $-> H) (l : J ⊆ (L o f)) (r : K ⊆ (M o f))
  : subgroup_product J K ⊆ (subgroup_product L M o f).
Proof.
  snapply functor_subgroup_generated.
  exact (fun x => functor_sum (l x) (r x)).
Defined.

Definition subgroup_eq_functor_subgroup_product {G H : Group}
  {J K : Subgroup G} {L M : Subgroup H}
  (f : G $<~> H) (l : J ↔ (L o f)) (r : K ↔ (M o f))
  : subgroup_product J K ↔ (subgroup_product L M o f).
Proof.
  snapply subgroup_eq_functor_subgroup_generated.
  exact (fun x => iff_functor_sum (l x) (r x)).
Defined.

Definition subgroup_eq_product_grp_op {G : Group} (H K : Subgroup G)
  : subgroup_grp_op (subgroup_product H K)
    ↔ subgroup_product (subgroup_grp_op H) (subgroup_grp_op K).
Proof.
  intro x.
  apply subgroup_eq_subgroup_generated_op.
  reflexivity.
Defined.

(** ** Image of a group homomorphism *)

(** The image of a group homomorphism between groups is a subgroup. *)
Definition grp_image {G H : Group} (f : G $-> H) : Subgroup H.
Proof.
  srapply (Build_Subgroup' (fun y => hexists (fun x => f x = y))); cbn beta.
  - apply tr.
    exists 1.
    apply grp_homo_unit.
  - intros x y p q; strip_truncations; apply tr.
    destruct p as [a p], q as [b q].
    exists (a * b^).
    lhs napply grp_homo_op; f_ap.
    lhs napply grp_homo_inv; f_ap.
Defined.

Definition grp_image_in {G H : Group} (f : G $-> H)
  : forall x, grp_image f (f x)
  := fun x => tr (x; idpath).

Definition grp_homo_image_in {G H : Group} (f : G $-> H)
  : G $-> grp_image f
  := subgroup_corec f (grp_image_in f).

(** ** Image of a group embedding *)

(** When the homomorphism is an embedding, we don't need to truncate. *)
Definition grp_image_embedding {G H : Group} (f : G $-> H) `{IsEmbedding f}
  : Subgroup H.
Proof.
  snapply (Build_Subgroup _ (hfiber f)).
  repeat split.
  - exact _.
  - exact (mon_unit; grp_homo_unit f).
  - intros x y [a []] [b []].
    exists (a * b).
    apply grp_homo_op.
  - intros b [a []].
    exists a^.
    apply grp_homo_inv.
Defined.

Definition grp_image_in_embedding {G H : Group} (f : G $-> H) `{IsEmbedding f}
  : GroupIsomorphism G (grp_image_embedding f).
Proof.
  snapply Build_GroupIsomorphism.
  - snapply (subgroup_corec f).
    exact (fun x => (x; idpath)).
  - apply isequiv_surj_emb.
    2: exact (cancelL_isembedding (g:=pr1)).
    intros [b [a p]]; cbn.
    rapply contr_inhabited_hprop.
    refine (tr (a; _)).
    srapply path_sigma'.
    1: exact p.
    refine (transport_sigma' _ _ @ _).
    by apply path_sigma_hprop.
Defined.

(** The image of a surjective group homomorphism is the maximal subgroup. *)
Instance ismaximal_image_issurj {G H : Group}
  (f : G $-> H) `{IsSurjection f}
  : IsMaximalSubgroup (grp_image f).
Proof.
  rapply conn_map_elim.
  apply grp_image_in.
Defined.

(** ** Image of a subgroup under a group homomorphism *)

(** The image of a subgroup under group homomorphism. *) 
Definition subgroup_image {G H : Group} (f : G $-> H)
  : Subgroup G -> Subgroup H
  := fun K => grp_image (grp_homo_restr f K).

(** By definition, values of [f x] where [x] is in a subgroup [J] are in the image of [J] under [f]. *)
Definition subgroup_image_in {G H : Group} (f : G $-> H) (J : Subgroup G)
  : J ⊆ (subgroup_image f J o f)
  := fun x Jx => tr ((x; Jx); idpath).

(** Converting the subgroups to groups, we get the expected surjective (epi) restriction homomorphism. *)
Definition grp_homo_subgroup_image_in {G H : Group}
  (f : G $-> H) (J : Subgroup G)
  : subgroup_group J $-> subgroup_group (subgroup_image f J)
  := functor_subgroup_group f (subgroup_image_in _ _).

(** The restriction map from the subgroup to the image is surjective as expected, by [conn_map_factor1_image]. *)
Definition issurj_grp_homo_subgroup_image_in {G H : Group}
  (f : G $-> H) (J : Subgroup G)
  : IsSurjection (grp_homo_subgroup_image_in f J)
  := _.

(** An image of a subgroup [J] is included in a subgroup [K] if (and only if) [J] is included in the preimage of the subgroup [K]. *)
Definition subgroup_image_rec {G H : Group}
  (f : G $-> H) {J : Subgroup G} {K : Subgroup H}
  (g : J ⊆ subgroup_preimage f K)
  : subgroup_image f J ⊆ K.
Proof.
  intros x; apply Trunc_rec; intros [[j Jj] p].
  destruct p.
  exact (g j Jj).
Defined.

(** The image functor is adjoint to the preimage functor. *) 
Definition iff_subgroup_image_rec {G H : Group}
  (f : G $-> H) {J : Subgroup G} {K : Subgroup H}
  : (subgroup_image f J ⊆ K) <-> (J ⊆ subgroup_preimage f K). 
Proof.
  split.
  - intros rec x Jx.
    apply rec, tr.
    by exists (x; Jx).
  - snapply subgroup_image_rec.
Defined.

(** [subgroup_image] preserves normal subgroups when the group homomorphism is surjective. *)
Instance isnormal_subgroup_image {G H : Group} (f : G $-> H)
  (J : Subgroup G) `{!IsNormalSubgroup J} `{!IsSurjection f}
  : IsNormalSubgroup (subgroup_image f J).
Proof.
  snapply Build_IsNormalSubgroup'.
  intros x y; revert x.
  change (subgroup_image f J (y * ?x * y^))
    with (subgroup_preimage (grp_conj y) (subgroup_image f J) x).
  snapply subgroup_image_rec.
  intros x Jx.
  change (subgroup_image f J ((grp_conj y $o f) x)).
  revert y; rapply (conn_map_elim (Tr (-1)) f); intros y.
  rewrite <- grp_homo_conj.
  napply subgroup_image_in.
  by rapply isnormal_conj.
Defined.

(** ** Kernels of group homomorphisms *)

Definition grp_kernel {G H : Group} (f : G $-> H)
  : NormalSubgroup G
  := Build_NormalSubgroup G (subgroup_preimage f (trivial_subgroup _)) _.

(** Corecursion principle for group kernels *)
Definition grp_kernel_corec {A B G : Group} {f : A $-> B}
  (g : G $-> A) (h : f $o g == grp_homo_const)
  : G $-> grp_kernel f
  := subgroup_corec (K:=grp_kernel f) g h.

Definition equiv_grp_kernel_corec `{Funext} {A B G : Group} {f : A $-> B}
  : {g : G $-> A & f $o g == grp_homo_const} <~> (G $-> grp_kernel f)
  := equiv_subgroup_corec G (grp_kernel f).

(** The underlying map of a group homomorphism with a trivial kernel is an embedding. *)
Instance isembedding_istrivial_kernel {G H : Group} (f : G $-> H)
  (triv : IsTrivialGroup (grp_kernel f))
  : IsEmbedding f.
Proof.
  intros h.
  apply hprop_allpath.
  intros [x p] [y q].
  srapply path_sigma_hprop; unfold pr1.
  apply grp_moveL_1M.
  apply triv; simpl.
  rhs_V exact (grp_inv_r h).
  lhs napply grp_homo_op.
  napply (ap011 (.*.) p).
  lhs napply grp_homo_inv.
  exact (ap (^) q).
Defined.

(** If the underlying map of a group homomorphism is an embedding then the kernel is trivial. *)
Definition istrivial_kernel_isembedding {G H : Group} (f : G $-> H)
  (emb : IsEmbedding f)
  : IsTrivialGroup (grp_kernel f).
Proof.
  intros g p.
  rapply (isinj_embedding f).
  exact (p @ (grp_homo_unit f)^).
Defined.
Global Hint Immediate istrivial_kernel_isembedding : typeclass_instances.

(** Characterisation of group embeddings *)
Proposition equiv_istrivial_kernel_isembedding `{F : Funext}
  {G H : Group} (f : G $-> H)
  : IsTrivialGroup (grp_kernel f) <~> IsEmbedding f.
Proof.
  apply equiv_iff_hprop_uncurried.
  split; exact _.
Defined.
