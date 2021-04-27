
Require Import Basics Types HProp HSet HFiber PathAny WildCat.
Require Import Algebra.Groups.Group TruncType.

Local Open Scope mc_mult_scope.
Generalizable Variables G H A B C N f g.

(** * Subgroups *)

(** A subgroup H of a group G is a predicate (i.e. an hProp-valued type family) on G which is closed under the group operations. The group underlying H is given by the total space { g : G & H g }, defined in [subgroup_group] below. *)
Class IsSubgroup {G : Group} (H : G -> Type) := {
  issubgroup_predicate : forall x, IsHProp (H x) ;
  issubgroup_unit : H mon_unit ;
  issubgroup_op : forall x y, H x -> H y -> H (x * y) ;
  issubgroup_inverse : forall x, H x -> H (- x) ;
}.

Global Existing Instance issubgroup_predicate.

(** Smart constructor for subgroups.  *)
Definition Build_IsSubgroup' {G : Group}
  (H : G -> Type) `{forall x, IsHProp (H x)}
  (unit : H mon_unit)
  (c : forall x y, H x -> H y -> H (x * -y))
  : IsSubgroup H.
Proof.
  refine (Build_IsSubgroup G H _ unit _ _).
  - intros x y.
    intros hx hy.
    pose (c' := c mon_unit y).
    specialize (c' unit).
    specialize (c x (-y)).
    rewrite (negate_involutive y) in c.
    rewrite left_identity in c'.
    apply c.
    1: assumption.
    exact (c' hy).
  - intro g.
    specialize (c _ g unit).
    rewrite left_identity in c.
    assumption.
Defined.

Definition issubgroup_op_inverse {G : Group} {H : G -> Type} `{IsSubgroup G H}
  : forall x y, H x -> H y -> H (x * -y).
Proof.
  intros x y p q.
  apply issubgroup_op.
  1: assumption.
  by apply issubgroup_inverse.
Defined.

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
  (c : forall x y, H x -> H y -> H (x * -y))
  : Subgroup G.
Proof.
  refine (Build_Subgroup G H _).
  rapply Build_IsSubgroup'; assumption.
Defined.

Definition subgroup_unit `(H : Subgroup G)
  : H mon_unit := issubgroup_unit.
Definition subgroup_inverse `(H : Subgroup G) x
  : H x -> H (- x) := issubgroup_inverse x.
Definition subgroup_op `(H : Subgroup G) x y
  : H x -> H y -> H (x * y) := issubgroup_op x y.
Definition subgroup_op_inverse `(H : Subgroup G) x y
  : H x -> H y -> H (x * -y) := issubgroup_op_inverse x y.

Global Instance isequiv_subgroup_inverse `(H : Subgroup G) (x : G)
  : IsEquiv (subgroup_inverse H x).
Proof.
  srapply isequiv_iff_hprop.
  intro h.
  rewrite <- negate_involutive.
    by apply subgroup_inverse.
Defined.

Definition equiv_subgroup_inverse {G : Group} (H : Subgroup G) (x : G)
  : H x <~> H (-x) := Build_Equiv _ _ (subgroup_inverse H x) _.

(** The group given by a subgroup *)
Definition subgroup_group (G : Group) (H : Subgroup G) : Group.
Proof.
  apply (Build_Group
      (** The underlying type is the sigma type of the predicate. *)
      (sig H)
      (** The operation is the group operation on the first projection with the proof  of being in the subgroup given by the subgroup data. *)
      (fun '(x ; p) '(y ; q) => (x * y ; issubgroup_op x y p q))
      (** The unit *)
      (mon_unit ; issubgroup_unit)
      (** Inverse *)
      (fun '(x ; p) => (- x ; issubgroup_inverse _ p))).
  (** Finally we need to prove our group laws. *)
  repeat split.
  1: exact _.
  all: grp_auto.
Defined.

Coercion subgroup_group : Subgroup >-> Group.

Definition subgroup_incl {G : Group} (H : Subgroup G)
  : GroupHomomorphism (subgroup_group G H) G.
Proof.
  snrapply Build_GroupHomomorphism'.
  1: exact pr1.
  repeat split.
Defined.

Global Instance isembedding_subgroup_incl {G : Group} (H : Subgroup G)
  : IsEmbedding (subgroup_incl H)
  := fun _ => istrunc_equiv_istrunc _ (hfiber_fibration _ _).

Definition issig_subgroup {G : Group} : _ <~> Subgroup G
  := ltac:(issig).

(** Trivial subgroup *)
Definition trivial_subgroup {G} : Subgroup G.
Proof.
  rapply (Build_Subgroup' (fun x => x = mon_unit)).
  1: reflexivity.
  intros x y p q.
  rewrite p, q.
  rewrite left_identity.
  apply negate_mon_unit.
Defined.

(** Every group is a (maximal) subgroup of itself *)
Definition maximal_subgroup {G} : Subgroup G.
Proof.
  rapply (Build_Subgroup G (fun x => Unit)).
  split; auto; exact _.
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
  Definition in_cosetL : Relation G := fun x y => H (-x * y).
  (** The relation of being in a right coset represented by an element. *)
  Definition in_cosetR : Relation G := fun x y => H (x * -y).

  Hint Unfold in_cosetL : typeclass_instances.
  Hint Unfold in_cosetR : typeclass_instances.

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
    apply issubgroup_unit.
  Defined.

  Global Instance reflexive_in_cosetR : Reflexive in_cosetR.
  Proof.
    intro x; hnf.
    rewrite right_inverse.
    apply issubgroup_unit.
  Defined.

  Global Instance symmetric_in_cosetL : Symmetric in_cosetL.
  Proof.
    intros x y h; cbn; cbn in h.
    rewrite <- (negate_involutive x).
    rewrite <- negate_sg_op.
    apply issubgroup_inverse; assumption.
  Defined.

  Global Instance symmetric_in_cosetR : Symmetric in_cosetR.
  Proof.
    intros x y h; cbn; cbn in h.
    rewrite <- (negate_involutive y).
    rewrite <- negate_sg_op.
    apply issubgroup_inverse; assumption.
  Defined.

  Global Instance transitive_in_cosetL : Transitive in_cosetL.
  Proof.
    intros x y z h k; cbn; cbn in h; cbn in k.
    rewrite <- (right_identity (-x)).
    rewrite <- (right_inverse y : y * -y = mon_unit).
    rewrite (associativity (-x) _ _).
    rewrite <- simple_associativity.
    apply issubgroup_op; assumption.
  Defined.

  Global Instance transitive_in_cosetR : Transitive in_cosetR.
  Proof.
    intros x y z h k; cbn; cbn in h; cbn in k.
    rewrite <- (right_identity x).
    rewrite <- (left_inverse y : -y * y = mon_unit).
    rewrite (simple_associativity x).
    rewrite <- (associativity _ _ (-z)).
    apply issubgroup_op; assumption.
  Defined.

End Cosets.

(** Identities related to the left and right cosets. *)

Definition in_cosetL_unit {G : Group} {N : Subgroup G}
  : forall x y, in_cosetL N (-x * y) mon_unit <~> in_cosetL N x y.
Proof.
  intros x y; cbn.
  rewrite (right_identity (- _)).
  rewrite (negate_sg_op _).
  rewrite (negate_involutive _).
  apply equiv_iff_hprop; apply symmetric_in_cosetL.
Defined.

Definition in_cosetR_unit {G : Group} {N : Subgroup G}
  : forall x y, in_cosetR N (x * -y) mon_unit <~> in_cosetR N x y.
Proof.
  intros x y; cbn.
  rewrite negate_mon_unit.
  rewrite (right_identity (x * -y)).
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

(** A subgroup is normal if being in a left coset is equivalent to being in a right coset represented by the same element. *)
Class IsNormalSubgroup {G : Group} (N : Subgroup G)
  := isnormal : forall {x y}, in_cosetL N x y <~> in_cosetR N x y.

Record NormalSubgroup (G : Group) := {
  normalsubgroup_subgroup : Subgroup G ;
  normalsubgroup_isnormal : IsNormalSubgroup normalsubgroup_subgroup ;
}.

Coercion normalsubgroup_subgroup : NormalSubgroup >-> Subgroup.
Global Existing Instance normalsubgroup_isnormal.

(* Inverses are then respected *)
Definition in_cosetL_inverse {G : Group} {N : NormalSubgroup G}
  : forall x y : G, in_cosetL N (-x) (-y) <~> in_cosetL N x y.
Proof.
  intros x y.
  unfold in_cosetL.
  rewrite negate_involutive.
  symmetry; apply isnormal.
Defined.

Definition in_cosetR_inverse {G : Group} {N : NormalSubgroup G}
  : forall x y : G, in_cosetR N (-x) (-y) <~> in_cosetR N x y.
Proof.
  intros x y.
  refine (_ oE (in_cosetR_unit _ _)^-1).
  refine (_ oE isnormal^-1).
  refine (_ oE in_cosetL_unit _ _).
  refine (_ oE isnormal).
  by rewrite negate_involutive.
Defined.

(** This lets us prove that left and right coset relations are congruences. *)
Definition in_cosetL_cong {G : Group} {N : NormalSubgroup G}
  (x x' y y' : G)
  : in_cosetL N x y -> in_cosetL N x' y' -> in_cosetL N (x * x') (y * y').
Proof.
  cbn; intros p q.
  (** rewrite goal before applying subgroup_op *)
  rewrite negate_sg_op, <- simple_associativity.
  apply symmetric_in_cosetL; cbn.
  rewrite simple_associativity.
  apply isnormal; cbn.
  rewrite <- simple_associativity.
  apply subgroup_op.
  1: assumption.
  by apply isnormal, symmetric_in_cosetL.
Defined.

Definition in_cosetR_cong  {G : Group} {N : NormalSubgroup G}
  (x x' y y' : G)
  : in_cosetR N x y -> in_cosetR N x' y' -> in_cosetR N (x * x') (y * y').
Proof.
  cbn; intros p q.
  (** rewrite goal before applying subgroup_op *)
  rewrite negate_sg_op, simple_associativity.
  apply symmetric_in_cosetR; cbn.
  rewrite <- simple_associativity.
  apply isnormal; cbn.
  rewrite simple_associativity.
  apply subgroup_op.
  2: assumption.
  by apply isnormal, symmetric_in_cosetR.
Defined.

(** The property of being the trivial subgroup is useful. *)
Definition IsTrivialSubgroup {G : Group} (H : Subgroup G) : Type :=
  forall x, H x <-> trivial_subgroup x.
Existing Class IsTrivialSubgroup.

Global Instance istrivialsubgroup_trivial_subgroup {G : Group}
  : IsTrivialSubgroup (@trivial_subgroup G)
  := ltac:(hnf; reflexivity).

(** Intersection of two subgroups *)
Definition subgroup_intersection {G : Group} (H K : Subgroup G) : Subgroup G.
Proof.
  snrapply Build_Subgroup'.
  1: exact (fun g => H g /\ K g).
  1: exact _.
  1: split; apply subgroup_unit.
  intros x y [] [].
  split; by apply subgroup_op_inverse.
Defined.


(** *** Subgroup generated by a subset *)

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
  -> subgroup_generated_type X (g * - h)
.

Arguments sgt_in {G X g}.
Arguments sgt_unit {G X}.
Arguments sgt_op {G X g h}.

(** Note that this will not automatically be a hprop. Notice that if [X] already contained the unit of the group, then there are at least two different inhabitants of this family at the unit. We can fix this by propositionally truncated. *)

(** Subgroup generated by a subset *)
Definition subgroup_generated {G : Group} (X : G -> Type) : Subgroup G.
Proof.
  snrapply Build_Subgroup'.
  1: exact (fun x => merely (subgroup_generated_type X x)).
  1: exact _.
  1: apply tr, sgt_unit.
  intros x y p q; strip_truncations.
  by apply tr, sgt_op.
Defined.

Definition subgroup_product {G : Group} (H K : Subgroup G) : Subgroup G
  := subgroup_generated (fun x => ((H x) + (K x))%type).

(** We can derive an induction principle for the product. *)
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

