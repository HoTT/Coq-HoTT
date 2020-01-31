Require Import HoTT.Basics HoTT.Types UnivalenceImpliesFunext.
Require Import PathAny.
Require Export Classes.interfaces.abstract_algebra.
Require Export Classes.theory.groups.
Require Import Pointed.Core.
Require Import WildCat.
Require Basics.Utf8.

Generalizable Variables G H A B C f g.

(** ** Groups *)

Local Open Scope mc_mult_scope.

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

(** Groups are pointed sets with point the identity. *)
Global Instance ispointed_group (G : Group)
  : IsPointed G := @mon_unit G _.

Definition ptype_group : Group -> pType
  := fun G => Build_pType G _.
Coercion ptype_group : Group >-> pType.

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
  (a x y : A) {p : x * a = mon_unit} {q : a * y = mon_unit}
  : x = y.
Proof.
  refine ((right_identity x)^ @ ap _ q^ @ _).
  refine (associativity _ _ _ @ _).
  refine (ap (fun x => x * y) p @ _).
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

(* Group homomorphisms are pointed maps *)
Definition pmap_GroupHomomorphism {G H : Group} (f : GroupHomomorphism G H) : pMap G H
  := Build_pMap G H f (@monmor_unitmor _ _ _ _ _ _ _ (@grp_homo_ishomo G H f)).
Coercion pmap_GroupHomomorphism : GroupHomomorphism >-> pMap.

Definition issig_GroupHomomorphism (G H : Group) : _ <~> GroupHomomorphism G H
  := ltac:(issig).

Definition equiv_path_grouphomomorphism {F : Funext} {G H : Group}
  {g h : GroupHomomorphism G H} : g == h <~> g = h.
Proof.
  refine ((equiv_ap (issig_GroupHomomorphism G H)^-1 _ _)^-1 oE _).
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
  : forall x y : G, f (x * y) = f x * f y.
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
  serapply (Build_GroupHomomorphism (f o g)).
Defined.

Definition grp_homo_id {G : Group} : GroupHomomorphism G G.
Proof.
  serapply (Build_GroupHomomorphism idmap).
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
  - serapply (Build_GroupHomomorphism f^-1).
  - exact _.
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

(** Under univalence, equality of groups is equivalent to isomorphism of groups. *)
Definition equiv_path_group {U : Univalence} {G H : Group}
  : GroupIsomorphism G H <~> G = H.
Proof.
  refine (equiv_compose'
    (B := sig (fun f : G <~> H => IsMonoidPreserving f)) _ _).
  { revert G H; apply (equiv_path_issig_contr issig_group).
    + intros [G [? [? [? ?]]]].
      exists 1%equiv.
      exact _.
    + intros [G [op [unit [neg ax]]]]; cbn.
      contr_sigsig G (equiv_idmap G).
      srefine (Build_Contr _ ((_;(_;(_;_)));_) _); cbn;
        try assumption; try exact _.
      intros [[op' [unit' [neg' ax']]] eq].
      apply path_sigma_hprop; cbn.
      (* We really need to fix https://github.com/HoTT/HoTT/issues/976 *)
      refine (@ap _ _ (fun x : { oun :
        { oo : SgOp G | { u : MonUnit G | Negate G}}
        | @IsGroup G oun.1 oun.2.1 oun.2.2}
        => (x.1.1 ; x.1.2.1 ; x.1.2.2 ; x.2))
        ((op;unit;neg);ax) ((op';unit';neg');ax') _).
      apply path_sigma_hprop; cbn.
      srefine (path_sigma' _ _ _).
      1: funext x y; apply eq.
      rewrite transport_const.
      srefine (path_sigma' _ _ _).
      1: apply eq.
      rewrite transport_const.
      funext x.
      exact (preserves_negate (f:=idmap) _). }
  refine (_ oE (issig_GroupIsomorphism G H)^-1).
  refine (_ oE (equiv_functor_sigma' (issig_GroupHomomorphism G H)
    (fun f => 1%equiv))^-1).
  refine (equiv_functor_sigma' (issig_equiv G H) (fun f => 1%equiv) oE _).
  cbn.
  refine (
    equiv_adjointify
      (fun f => (exist (IsMonoidPreserving o pr1)
        (exist IsEquiv f.1.1 f.2) f.1.2))
      (fun f => (exist (IsEquiv o pr1)
        (exist IsMonoidPreserving f.1.1 f.2) f.1.2))
       _ _).
  all: intros [[]]; reflexivity.
Defined.  

(** * Simple group equivalences *)

(** Left multiplication is an equivalence *)
Global Instance isequiv_group_left_op `{IsGroup G}
  : forall x, IsEquiv (x *.).
Proof.
  intro x.
  serapply isequiv_adjointify.
  1: exact (-x *.).
  all: intro y.
  all: refine (associativity _ _ _ @ _ @ left_identity y).
  all: refine (ap (fun x => x * y) _).
  1: apply right_inverse.
  apply left_inverse.
Defined.

(** Right multiplication is an equivalence *)
Global Instance isequiv_group_right_op `{IsGroup G}
  : forall x:G, IsEquiv (fun y => y * x).
Proof.
  intro x.
  serapply isequiv_adjointify.
  1: exact (fun y => y * - x).
  all: intro y.
  all: refine ((associativity _ _ _)^ @ _ @ right_identity y).
  all: refine (ap (y *.) _).
  1: apply left_inverse.
  apply right_inverse.
Defined.

Definition left_mult_equiv `{IsGroup G} : G -> G <~> G
  := fun x => Build_Equiv _ _ (x *.) _.

(* Right multiplication is an equivalence. *)
Definition right_mult_equiv `{IsGroup G} : G -> G <~> G
  := fun x => Build_Equiv _ _ (fun y => y * x) _.

Global Instance isequiv_group_inverse `{IsGroup G}
  : IsEquiv (-).
Proof.
  serapply isequiv_adjointify.
  1: apply (-).
  all: intro; apply negate_involutive.
Defined.

(** * Direct product of group *)

Definition group_prod : Group -> Group -> Group.
Proof.
  intros G H.
  serapply (Build_Group (G * H)).
  (** Operation *)
  { intros [g1 h1] [g2 h2].
    exact (g1 * g2, h1 * h2). }
  (** Unit *)
  1: exact (mon_unit, mon_unit).
  (** Inverse *)
  { intros [g h].
    exact (-g, -h). }
  (** Group laws *)
  serapply Build_IsGroup.
  (** Monoid laws *)
  { serapply Build_IsMonoid.
    (** Semigroup lawss *)
    { serapply Build_IsSemiGroup.
      (** Associativity *)
      intros [g1 h1] [g2 h2] [g3 h3].
      apply path_prod; cbn.
      1,2: apply associativity. }
    (** Left identity *)
    { intros [g h].
      apply path_prod; cbn.
      1,2: apply left_identity. }
    (** Right identity *)
    { intros [g h].
      apply path_prod; cbn.
      1,2: apply right_identity. } }
  (** Left inverse *)
  { intros [g h].
    apply path_prod; cbn.
    1,2: apply left_inverse. }
  (** Right inverse *)
  { intros [g h].
    apply path_prod; cbn.
    1,2: apply right_inverse. }
Defined.

Definition grp_iso_prod {A B C D : Group}
  : GroupIsomorphism A B -> GroupIsomorphism C D
    -> GroupIsomorphism (group_prod A C) (group_prod B D).
Proof.
  intros f g.
  serapply Build_GroupIsomorphism'.
  1: serapply (equiv_functor_prod (f:=f) (g:=g)).
  simpl.
  unfold functor_prod.
  intros x y.
  apply path_prod.
  1,2: apply grp_homo_op.
Defined.

(** Group forms a 01Cat *)
Global Instance is01cat_Group : Is01Cat Group :=
  (Build_Is01Cat Group GroupHomomorphism (@grp_homo_id) (@grp_homo_compose)).

Global Instance is01cat_GroupHomomorphism {A B : Group} : Is01Cat (A $-> B) :=
  induced_01cat (@grp_homo_map A B).

Global Instance is0gpd_GroupHomomorphism {A B : Group}: Is0Gpd (A $-> B) := 
  induced_0gpd (@grp_homo_map A B).

Global Instance is0functor_postcomp_GroupHomomorphism
       {A B C : Group} (h : B $-> C)
  : Is0Functor (@cat_postcomp Group _ A B C h).
Proof.
  apply Build_Is0Functor.
  intros [f ?] [g ?] p a ; exact (ap h (p a)).
Defined.

Global Instance is0functor_precomp_GroupHomomorphism
       {A B C : Group} (h : A $-> B)
  : Is0Functor (@cat_precomp Group _ A B C h).
Proof.
  apply Build_Is0Functor.
  intros [f ?] [g ?] p a ; exact (p (h a)).
Defined.

(** Group forms a 1Cat *)
Global Instance is1cat_group : Is1Cat Group.
Proof.
  srapply Build_Is1Cat; cbn; intros; reflexivity.
Defined.

Instance hasmorext_group `{Funext} : HasMorExt Group.
Proof.
  srapply Build_HasMorExt.
  intros A B f g; cbn in *.
  simple notypeclasses refine (isequiv_homotopic ((equiv_path_grouphomomorphism)^-1) _). 
  1,3: exact _.
(*   1: exact _. *)
  1: apply equiv_isequiv.
  intros []. reflexivity. 
Defined.

Global Instance hasequivs_group : HasEquivs Group.
Proof.
  srefine (Build_HasEquivs Group _ _ GroupIsomorphism (fun G H f => IsEquiv f) _ _ _ _ _ _ _ _); intros A B f.
  - exact f.
  - cbn. exact _.
  - apply Build_GroupIsomorphism.
  - intro fe. reflexivity.
  - intro fe. exact (grp_iso_inverse (Build_GroupIsomorphism _ _ f fe)).
  - cbn. intros ? x; apply eissect.
  - cbn. intros ? x; apply eisretr.
  - intros g r s; refine (isequiv_adjointify f g r s).
Defined.


(** TODO: If #1140 gets resolved, include this: *)
(* Module GroupUtf8.

  Import Basics.Utf8.
  Infix "≅" := GroupIsomorphism.
  Infix "×" := group_prod.

End GroupUtf8.
 *)
