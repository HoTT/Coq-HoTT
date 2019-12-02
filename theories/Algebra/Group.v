Require Import Basics.
Require Import Types.
Require Import Cubical.
Require Import PathAny.
Require Export Classes.interfaces.abstract_algebra.
Require Export Classes.theory.groups.

(** ** Groups *)

(** * Definition of Group *)

(** A group consists of a type, and operation on that type, and unit and an inverse, such that they satisfy the group axioms in IsGroup. *)
Class Group := {
  group_type : Type;
  group_sgop :> SgOp group_type;
  group_unit :> MonUnit group_type;
  group_inverse :> Negate group_type;
  group_isgroup :> IsGroup group_type;
}.

(** We coerce groups back to types. *)
Coercion group_type : Group >-> Sortclass.

Definition issig_group : _ <~> Group
  := ltac:(issig).

(** * Some basic properties of groups *)

(** An element acting like the identity is unique. *)
Definition identity_unique {A : Type} {Aop : SgOp A}
  (x y : A) {p : LeftIdentity Aop x} {q : RightIdentity Aop y}
  : x = y := (q x)^ @ p y.

Definition identity_unique' {A : Type} {Aop : SgOp A}
  (x y : A) {p : LeftIdentity Aop x} {q : RightIdentity Aop y}
  : y = x := (identity_unique x y)^.

(** An element acting like an inverse is unique. *)
Definition inverse_unique `{IsMonoid A}
  (a x y : A) {p : x & a = mon_unit} {q : a & y = mon_unit}
  : x = y.
Proof.
  refine ((right_identity x)^ @ ap _ q^ @ _).
  refine (associativity _ _ _ @ _).
  refine (ap (& y) p @ _).
  apply left_identity.
Defined.

(** Inverses are involutive *)
(* Check negate_involutive. *)

(** Inverses distribute over the group operation *)
(* Check negate_sg_op. *)

(** Group elements can be cancelled on the left of an equation *)
(* Check group_cancelL. *)

(** Group elements can be cancelled on the right of an equation *)
(* Check group_cancelR. *)

(** Definition of Group Homomorphism *)

(* A group homomorphism consists of a map between groups and a proof that the map preserves the group operation. *)
Class GroupHomomorphism (G H : Group) := Build_GroupHomomorphism' {
  grp_homo_map : G -> H;
  grp_homo_ishomo :> IsMonoidPreserving grp_homo_map;
}.

(* We coerce a homomorphism to its underlying map. *)
Coercion grp_homo_map : GroupHomomorphism >-> Funclass.
(* Notation "G '->G' H" := (GroupHomomorphism G H) (at level 20). *)

Definition issig_GroupHomomorphism {G H : Group} : _ <~> GroupHomomorphism G H
  := ltac:(issig).

Definition equiv_path_grouphomomorphism {F : Funext} {G H : Group}
  {g h : GroupHomomorphism G H} : g == h <~> g = h.
Proof.
  refine ((equiv_ap issig_GroupHomomorphism^-1 _ _)^-1 oE _).
  refine (equiv_path_sigma_hprop _ _ oE _).
  apply equiv_path_forall.
Defined.

Global Instance ishset_grouphomomorphism {F : Funext} {G H : Group}
  : IsHSet (GroupHomomorphism G H).
Proof.
  intros f g; apply (trunc_equiv' _ equiv_path_grouphomomorphism).
Defined.

(** * Some basic properties of group homomorphisms *)

(** Group homomorphisms preserve identities *)
Definition grp_homo_unit {G H} (f : GroupHomomorphism G H)
  : f (mon_unit) = mon_unit.
Proof.
  apply monmor_unitmor.
Defined.

(** Group homomorphisms preserve group operations *)
Definition grp_homo_op {G H} (f : GroupHomomorphism G H)
  : forall x y : G, f (x & y) = f x & f y.
Proof.
  apply monmor_sgmor.
Defined.

(** Group homomorphisms preserve inverses *)
Definition grp_homo_inv {G H} (f : GroupHomomorphism G H)
  : forall x, f (- x) = -(f x).
Proof.
  intro x.
  apply (inverse_unique (f x)).
  + refine (_ @ grp_homo_unit f).
    refine ((grp_homo_op f (-x) x)^ @ _).
    apply ap.
    apply left_inverse.
  + apply right_inverse.
Defined.

(** When building a group homomorphism we only need that it preserves the group operation, since we can prove that the identity is preserved. *)
Definition Build_GroupHomomorphism {G H : Group}
  (f : G -> H) {h : IsSemiGroupPreserving f}
  : GroupHomomorphism G H.
Proof.
  serapply (Build_GroupHomomorphism' _ _ f).
  split.
  1: exact h.
  unfold IsUnitPreserving.
  apply (group_cancelL (f mon_unit)).
  refine (_ @ (right_identity _)^).
  refine (_ @ ap _ (monoid_left_id _ mon_unit)).
  symmetry.
  apply h.
Defined.

Definition grp_homo_compose {G H K : Group}
  : GroupHomomorphism H K -> GroupHomomorphism G H -> GroupHomomorphism G K.
Proof.
  intros f g.
  serapply Build_GroupHomomorphism.
  1: exact (f o g).
  intros x y.
  refine (ap f (grp_homo_op g _ _) @ _).
  apply grp_homo_op.
Defined.

(* An isomorphism of groups is a group homomorphism that is an equivalence. *)
Class GroupIsomorphism (G H : Group) := Build_GroupIsomorphism {
  grp_iso_homo :> GroupHomomorphism G H;
  isequiv_group_iso :> IsEquiv grp_iso_homo;
}.

Coercion grp_iso_homo : GroupIsomorphism >-> GroupHomomorphism.

Definition issig_GroupIsomorphism (G H : Group)
  : _ <~> GroupIsomorphism G H := ltac:(issig).

Definition grp_iso_inverse {G H : Group}
  : GroupIsomorphism G H -> GroupIsomorphism H G.
Proof.
  intros [f e].
  serapply Build_GroupIsomorphism.
  { serapply Build_GroupHomomorphism.
    1: exact f^-1.
    unfold IsSemiGroupPreserving.
    intros x y.
    apply (ap f)^-1.
    rewrite grp_homo_op.
    by rewrite !eisretr. }
  exact _.
Defined.

(* We can build an isomorphism from an operation preserving equivalence. *)
Definition Build_GroupIsomorphism' {G H : Group}
  (f : G <~> H) (h : IsSemiGroupPreserving f)
  : GroupIsomorphism G H.
Proof.
  serapply Build_GroupIsomorphism.
  1: serapply Build_GroupHomomorphism.
  exact _.
Defined.

(** Group Isomorphisms are a reflexive relation *)
Global Instance reflexive_groupisomorphism
  : Reflexive GroupIsomorphism.
Proof.
  intro x.
  by serapply Build_GroupIsomorphism'.
Defined.

(** Group Isomorphisms are a symmetric relation *)
Global Instance symmetric_groupisomorphism
  : Symmetric GroupIsomorphism.
Proof.
  intros G H.
  serapply grp_iso_inverse.
Defined.

Global Instance transitive_groupisomorphism
  : Transitive GroupIsomorphism.
Proof.
  intros G H K f g.
  serapply Build_GroupIsomorphism.
  1: serapply grp_homo_compose.
  exact _.
Defined.

(** Under univalence, equality of groups is equivalent to isomorphism of groups. This is a long proof that mostly consists of rearranging sigma types. *)
Definition equiv_path_group {U : Univalence} {G H : Group}
  : GroupIsomorphism G H <~> G = H.
Proof.
  refine (_ oE _).
  { symmetry.
    exact (equiv_ap' issig_group^-1 G H). }
  simpl.
  (** Turning (_;_;_;_) into ((_;_;_);_) *)
  refine (_ oE _).
  { symmetry.
    erapply equiv_ap'.
    refine (_ oE _).
    2: { erapply equiv_functor_sigma_id.
      intro X.
      refine (_ oE _).
      2: { erapply equiv_functor_sigma_id.
        intro m.
        serapply (equiv_sigma_assoc _
          (fun x => @IsGroup X m x.1 x.2)). }
      serapply (equiv_sigma_assoc _
      (fun x => @IsGroup X x.1 x.2.1 x.2.2)). }
    serapply (equiv_sigma_assoc _
      (fun x => @IsGroup x.1 x.2.1 x.2.2.1 x.2.2.2)). }
  refine (_ oE _).
  1: serapply equiv_path_sigma_hprop.
  simpl.
  (** Now we will turn our equality of sigma types into a sigma type of equalities. *)
  refine (Build_Equiv _ _ path_sigma_dp_uncurried _ oE _).
  refine (_ oE _).
  { erapply equiv_functor_sigma_id; intro.
    exact (Build_Equiv _ _ (dp_sigma_uncurried
      (C := fun a => {_ : MonUnit a.1 | Negate a.1}) (_;_;_) _) _). }
  simpl.
  (** We use univalence to unpack G = K as {f : G <~> K & IsEquiv f} *)
  refine (_ oE _).
  { serapply equiv_functor_sigma'.
    4: intro; reflexivity.
    1: shelve.
    refine (equiv_path_universe _ _ oE _).
    apply issig_equiv. }
  refine (equiv_sigma_assoc _ _ oE _).
  (** Now we unpack the data of a group isomorphism. *)
  refine (_ oE (issig_GroupIsomorphism _ _)^-1).
  refine (_ oE _).
  2: { serapply equiv_functor_sigma'.
    3: symmetry; apply issig_GroupHomomorphism.
    1: exact (fun x => IsEquiv (pr1 x)).
    reflexivity. }
  refine (_ oE (equiv_sigma_assoc _ _)^-1).
  (** We see that we have an equivalence in the first component *)
  serapply (equiv_functor_sigma' (reflexivity _)).
  intro f; cbn.
  refine (_ oE equiv_sigma_symm0 _ _).
  (** We see that we have an equivalence in the first component *)
  serapply (equiv_functor_sigma' (reflexivity _)).
  intro e; cbn.
  (** Now we prove that an equivalence being monoid preserving is equivalent to this sigma of dependent paths. Note that both sides are props. *)
  apply equiv_iff_hprop.
  { (** First we show that being monoid preserving implies the sigma type. *)
    intro p.
    srefine (_;_).
    { unfold SgOp.
      apply dp_arrow; intro x.
      apply dp_arrow; intro y.
      apply dp_path_transport.
      refine (transport_path_universe_uncurried _ _ @ _).
      refine (monmor_sgmor _ _ @ _).
      apply ap2.
      1,2: symmetry; apply transport_path_universe_uncurried. }
    simpl.
    serapply (dp_compose pr1 (fun a => {_ : MonUnit a | Negate a}) _ (_;_) _).
    rewrite ap_pr1_path_sigma_dp.
    serapply (@dp_sigma _ MonUnit (fun x => Negate x.1)).
    { simpl.
      unfold MonUnit.
      apply dp_path_transport.
      refine (_ @ monmor_unitmor (f:=f)).
      apply transport_path_universe_uncurried. }
    serapply (dp_compose pr1).
    rewrite ap_pr1_path_sigma_dp.
    unfold Negate.
    apply dp_arrow; simpl.
    intro x.
    apply dp_path_transport.
    rewrite ? transport_path_universe_uncurried.
    change (f (-x) = -f(x)).
    serapply preserves_negate. }
  (** Now we must show that the sigma type implies monoid preservin. *)
  intros [p q].
  (** Since we are trying to prove that a map between groups is monoid preserving, we can use Build_GroupHomomorphism to show that being semigroup preserving is sufficient. *)
  serapply (@grp_homo_ishomo _ _ (Build_GroupHomomorphism f)).
  intros x y.
  set (F := Build_Equiv _ _ f _) in *.
  change f with (equiv_fun F).
  clearbody F; clear e f.
  clear q.
  apply dp_path_transport^-1 in p.
  pose (apD10 (apD10 p (F x)) (F y)) as q.
  refine (_ @ q).
  clear q.
  rewrite <- (eissect path_universe_uncurried F).
  simpl.
  set (P := path_universe_uncurried F) in *.
  clearbody P; clear F.
  simpl in *.
  unfold path_universe_uncurried.
  rewrite (eissect (equiv_path G H) P).
  rewrite 2 transport_arrow.
  rewrite 2 transport_Vp.
  reflexivity.
Defined.

(** * Simple group equivalences *)

(** Left multiplication is an equivalence *)
Global Instance isequiv_group_left_op `{IsGroup G}
  : forall x, IsEquiv (x &).
Proof.
  intro x.
  serapply isequiv_adjointify.
  1: exact (-x &).
  all: intro y.
  all: refine (associativity _ _ _ @ _ @ left_identity y).
  all: refine (ap (& y) _).
  1: apply right_inverse.
  apply left_inverse.
Defined.

(** Right multiplication is an equivalence *)
Global Instance isequiv_group_right_op `{IsGroup G}
  : forall x, IsEquiv (& x).
Proof.
  intro x.
  serapply isequiv_adjointify.
  1: exact (& - x).
  all: intro y.
  all: refine ((associativity _ _ _)^ @ _ @ right_identity y).
  all: refine (ap (y &) _).
  1: apply left_inverse.
  apply right_inverse.
Defined.

Definition left_mult_equiv `{IsGroup G} : G -> G <~> G
  := fun x => Build_Equiv _ _ (x &) _.

(* Right multiplication is an equivalence. *)
Definition right_mult_equiv `{IsGroup G} : G -> G <~> G
  := fun x => Build_Equiv _ _ (& x) _.

Global Instance isequiv_group_inverse `{IsGroup G}
  : IsEquiv (-).
Proof.
  serapply isequiv_adjointify.
  1: apply (-).
  all: intro; apply negate_involutive.
Defined.

