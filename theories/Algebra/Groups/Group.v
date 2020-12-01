Require Import HoTT.Basics HoTT.Types.
Require Import HProp HFiber.
Require Import PathAny.
Require Export Classes.interfaces.abstract_algebra.
Require Export Classes.theory.groups.
Require Import Pointed.Core.
Require Import WildCat.
Require Basics.Utf8.

Generalizable Variables G H A B C f g.

Declare Scope group_scope.

(** ** Groups *)

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.

(** * Definition of Group *)

(** A group consists of a type, and operation on that type, and unit and an inverse, such that they satisfy the group axioms in IsGroup. *)
Record Group := {
  group_type : Type;
  group_sgop : SgOp group_type;
  group_unit : MonUnit group_type;
  group_inverse : Negate group_type;
  group_isgroup : IsGroup group_type;
}.

Arguments group_sgop {_}.
Arguments group_unit {_}.
Arguments group_inverse {_}.
Arguments group_isgroup {_}.
(** We never need to unfold the proof that something is a group *)
Opaque group_isgroup.

(** We coerce groups back to types. *)
Coercion group_type : Group >-> Sortclass.
Global Existing Instances group_sgop group_unit group_inverse group_isgroup.

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

(** ** Working with equations in groups *)

(** Inverses are involutive *)
(* Check negate_involutive. *)

(** Inverses distribute over the group operation *)
(* Check negate_sg_op. *)

(** Group elements can be cancelled on the left of an equation *)
(* Check group_cancelL. *)

(** Group elements can be cancelled on the right of an equation *)
(* Check group_cancelR. *)

Lemma group_moveL_1M {G : Group} (x y : G)
  : x * (-y) = mon_unit -> x = y.
Proof.
  intro p.
  apply (group_cancelR (- y)).
  exact (p @ (right_inverse y)^).
Defined.

Lemma group_moveL_M1 {G : Group} (x y : G)
  : -y * x = mon_unit -> x = y.
Proof.
  intro p.
  apply (group_cancelL (- y)).
  exact (p @ (left_inverse y)^).
Defined.

Lemma group_moveL_gM {G : Group} (x y z : G)
  : x * -z = y -> x = y * z.
Proof.
  intro p.
  apply (group_cancelR (- z)).
  refine (_ @ associativity _ _ _).
  exact (p @ (right_identity y)^ @ (ap (fun a => y * a) (right_inverse z))^).
Defined.

Lemma group_moveL_Mg {G : Group} (x y z : G)
  : -y * x = z -> x = y * z.
Proof.
  intro p.
  apply (group_cancelL (- y)).
  refine (_ @ (associativity _ _ _)^).
  exact (p @ (left_identity z)^ @ (ap (fun a => a * z) (left_inverse y))^).
Defined.

Lemma group_moveR_1M {G : Group} (x y : G)
  : mon_unit = y * (-x) -> x = y.
Proof.
  intro p.
  apply (group_cancelR (- x)).
  exact (right_inverse x @ p).
Defined.

Lemma group_moveR_M1 {G : Group} (x y : G)
  : mon_unit = -x * y -> x = y.
Proof.
  intro p.
  apply (group_cancelL (- x)).
  exact (left_inverse x @ p).
Defined.

Lemma group_moveR_gM {G : Group} (x y z : G)
  : x = z * -y -> x * y = z.
Proof.
  intro p.
  apply (group_cancelR (- y)).
  refine ((associativity _ _ _)^ @ _).
  exact (ap (fun a => x * a) (right_inverse y) @ right_identity _ @ p).
Defined.

Lemma group_moveR_Mg {G : Group} (x y z : G)
  : y = -x * z -> x * y = z.
Proof.
  intro p.
  apply (group_cancelL (- x)).
 refine (associativity _ _ _ @ _).
  exact (ap (fun a => a * y) (left_inverse x) @ left_identity _ @ p).
Defined.

(** ** Group homomorphisms *)

(* A group homomorphism consists of a map between groups and a proof that the map preserves the group operation. *)
Record GroupHomomorphism (G H : Group) := Build_GroupHomomorphism' {
  grp_homo_map : G -> H;
  grp_homo_ishomo :> IsMonoidPreserving grp_homo_map;
}.

(* We coerce a homomorphism to its underlying map. *)
Coercion grp_homo_map : GroupHomomorphism >-> Funclass.
Global Existing Instance grp_homo_ishomo.

(* Group homomorphisms are pointed maps *)
Definition pmap_GroupHomomorphism {G H : Group} (f : GroupHomomorphism G H) : G ->* H
  := Build_pMap G H f (@monmor_unitmor _ _ _ _ _ _ _ (@grp_homo_ishomo G H f)).
Coercion pmap_GroupHomomorphism : GroupHomomorphism >-> pForall.

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
  srapply (Build_GroupHomomorphism' _ _ f).
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
  srapply (Build_GroupHomomorphism (f o g)).
Defined.

(* An isomorphism of groups is a group homomorphism that is an equivalence. *)
Record GroupIsomorphism (G H : Group) := Build_GroupIsomorphism {
  grp_iso_homo : GroupHomomorphism G H;
  isequiv_group_iso : IsEquiv grp_iso_homo;
}.

Coercion grp_iso_homo : GroupIsomorphism >-> GroupHomomorphism.
Global Existing Instance isequiv_group_iso.

Definition issig_GroupIsomorphism (G H : Group)
  : _ <~> GroupIsomorphism G H := ltac:(issig).

Definition equiv_groupisomorphism (G H : Group)
  : GroupIsomorphism G H -> G <~> H
  := fun f => Build_Equiv G H f _.

Coercion equiv_groupisomorphism : GroupIsomorphism >-> Equiv.

Definition equiv_path_groupisomorphism `{F : Funext} {G H : Group}
  (f g : GroupIsomorphism G H)
  : f == g <~> f = g.
Proof.
  refine ((equiv_ap (issig_GroupIsomorphism G H)^-1 _ _)^-1 oE _).
  refine (equiv_path_sigma_hprop _ _ oE _).
  apply equiv_path_grouphomomorphism.
Defined.

Definition ishset_groupisomorphism `{F : Funext} {G H : Group}
  : IsHSet (GroupIsomorphism G H).
Proof.
  intros f g; apply (trunc_equiv' _ (equiv_path_groupisomorphism _ _)).
Defined.

Definition grp_iso_inverse {G H : Group}
  : GroupIsomorphism G H -> GroupIsomorphism H G.
Proof.
  intros [f e].
  srapply Build_GroupIsomorphism.
  - srapply (Build_GroupHomomorphism f^-1).
  - exact _.
Defined.

(* We can build an isomorphism from an operation preserving equivalence. *)
Definition Build_GroupIsomorphism' {G H : Group}
  (f : G <~> H) (h : IsSemiGroupPreserving f)
  : GroupIsomorphism G H.
Proof.
  srapply Build_GroupIsomorphism.
  1: srapply Build_GroupHomomorphism.
  exact _.
Defined.

(** Group Isomorphisms are a reflexive relation *)
Global Instance reflexive_groupisomorphism
  : Reflexive GroupIsomorphism.
Proof.
  intro x.
  by srapply Build_GroupIsomorphism'.
Defined.

(** Group Isomorphisms are a symmetric relation *)
Global Instance symmetric_groupisomorphism
  : Symmetric GroupIsomorphism.
Proof.
  intros G H.
  srapply grp_iso_inverse.
Defined.

Global Instance transitive_groupisomorphism
  : Transitive GroupIsomorphism.
Proof.
  intros G H K f g.
  srapply Build_GroupIsomorphism.
  1: exact (grp_homo_compose g f).
  exact _.
Defined.

Definition grp_homo_id {G : Group} : GroupHomomorphism G G.
Proof.
  srapply (Build_GroupHomomorphism idmap).
Defined.

Definition grp_homo_const {G H : Group} : GroupHomomorphism G H.
Proof.
  snrapply Build_GroupHomomorphism.
  - exact (fun _ => mon_unit).
  - intros x y.
    exact (left_identity mon_unit)^.
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
  srapply isequiv_adjointify.
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
  srapply isequiv_adjointify.
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
  srapply isequiv_adjointify.
  1: apply (-).
  all: intro; apply negate_involutive.
Defined.

(** Given a group element a0:A over b:B, multiplication by a establishes an equivalence between the kernel and the fiber over b. *)
Lemma equiv_grp_hfiber {A B : Group} (f : GroupHomomorphism A B) (b : B)
  : forall (a0 : hfiber f b), hfiber f b <~> hfiber f mon_unit.
Proof.
  intros [a0 p].
  refine (equiv_transport (hfiber f) _ _ (right_inverse b) oE _).
  rapply (equiv_functor_hfiber (h:=right_mult_equiv (-a0)) (k:=right_mult_equiv (- b))).
  intro a; cbn; symmetry.
  refine (_ @ ap (fun x => f a * (- x)) p).
  exact (grp_homo_op f _ _ @ ap (fun x => f a * x) (grp_homo_inv f a0)).
Defined.

(** ** The trivial group *)

Definition grp_trivial : Group.
Proof.
  refine (Build_Group Unit (fun _ _ => tt) tt (fun _ => tt) _).
  repeat split; try exact _; by intros [].
Defined.

(** Map out of trivial group *)
Definition grp_trivial_rec (G : Group) : GroupHomomorphism grp_trivial G.
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact (fun _ => group_unit).
  intros ??; symmetry; apply left_identity.
Defined.

(** Map into trivial group *)
Definition grp_trivial_corec (G : Group) : GroupHomomorphism G grp_trivial.
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact (fun _ => tt).
  intros ??; symmetry; apply left_identity.
Defined.

(** * Direct product of group *)

Definition grp_prod : Group -> Group -> Group.
Proof.
  intros G H.
  srapply (Build_Group (G * H)).
  (** Operation *)
  { intros [g1 h1] [g2 h2].
    exact (g1 * g2, h1 * h2). }
  (** Unit *)
  1: exact (mon_unit, mon_unit).
  (** Inverse *)
  { intros [g h].
    exact (-g, -h). }
  (** Group laws *)
  srapply Build_IsGroup.
  (** Monoid laws *)
  { srapply Build_IsMonoid.
    (** Semigroup lawss *)
    { srapply Build_IsSemiGroup.
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

Proposition grp_prod_corec {G H K : Group}
            (f : GroupHomomorphism K G)
            (g : GroupHomomorphism K H)
  : GroupHomomorphism K (grp_prod G H).
Proof.
  snrapply Build_GroupHomomorphism.
  - exact (fun x:K => (f x, g x)).
  - intros x y.
    refine (path_prod' _ _ ); try apply grp_homo_op.
Defined.

Definition grp_prod_inl {H K : Group}
  : GroupHomomorphism H (grp_prod H K)
  := grp_prod_corec grp_homo_id grp_homo_const.

Definition grp_prod_inr {H K : Group}
  : GroupHomomorphism K (grp_prod H K)
  := grp_prod_corec grp_homo_const grp_homo_id.

Definition grp_iso_prod {A B C D : Group}
  : GroupIsomorphism A B -> GroupIsomorphism C D
    -> GroupIsomorphism (grp_prod A C) (grp_prod B D).
Proof.
  intros f g.
  srapply Build_GroupIsomorphism'.
  1: srapply (equiv_functor_prod (f:=f) (g:=g)).
  simpl.
  unfold functor_prod.
  intros x y.
  apply path_prod.
  1,2: apply grp_homo_op.
Defined.

(** The wild cat of Groups *)
Global Instance isgraph_group : IsGraph Group
  := Build_IsGraph Group GroupHomomorphism.

Global Instance is01cat_group : Is01Cat Group :=
  (Build_Is01Cat Group _ (@grp_homo_id) (@grp_homo_compose)).

Global Instance isgraph_grouphomomorphism {A B : Group} : IsGraph (A $-> B)
  := induced_graph (@grp_homo_map A B).

Global Instance is01cat_grouphomomorphism {A B : Group} : Is01Cat (A $-> B)
  := induced_01cat (@grp_homo_map A B).

Global Instance is0gpd_grouphomomorphism {A B : Group}: Is0Gpd (A $-> B)
  := induced_0gpd (@grp_homo_map A B).

Global Instance is0functor_postcomp_grouphomomorphism {A B C : Group} (h : B $-> C)
  : Is0Functor (@cat_postcomp Group _ _ A B C h).
Proof.
  apply Build_Is0Functor.
  intros [f ?] [g ?] p a ; exact (ap h (p a)).
Defined.

Global Instance is0functor_precomp_grouphomomorphism
       {A B C : Group} (h : A $-> B)
  : Is0Functor (@cat_precomp Group _ _ A B C h).
Proof.
  apply Build_Is0Functor.
  intros [f ?] [g ?] p a ; exact (p (h a)).
Defined.

(** Group forms a 1Cat *)
Global Instance is1cat_group : Is1Cat Group.
Proof.
  by rapply Build_Is1Cat.
Defined.

Instance hasmorext_group `{Funext} : HasMorExt Group.
Proof.
  srapply Build_HasMorExt.
  intros A B f g; cbn in *.
  snrapply @isequiv_homotopic.
  1: exact (equiv_path_grouphomomorphism^-1%equiv).
  1: exact _.
  intros []; reflexivity. 
Defined.

Global Instance hasequivs_group : HasEquivs Group.
Proof.
  unshelve econstructor.
  + exact GroupIsomorphism.
  + exact (fun G H f => IsEquiv f).
  + intros G H f; exact f.
  + exact Build_GroupIsomorphism.
  + intros G H; exact grp_iso_inverse.
  + cbn; exact _.
  + reflexivity.
  + intros ????; apply eissect.
  + intros ????; apply eisretr.
  + intros G H f g p q.
    exact (isequiv_adjointify f g p q).
Defined.

Global Instance is1cat_strong `{Funext} : Is1Cat_Strong Group.
Proof.
  rapply Build_Is1Cat_Strong.
  all: intros; apply equiv_path_grouphomomorphism; intro; reflexivity.
Defined.

(** *** Properties of maps to and from the trivial group *)

Global Instance isinitial_grp_trivial : IsInitial grp_trivial.
Proof.
  intro G.
  exists (grp_trivial_rec _).
  intros g [].
  apply (grp_homo_unit g).
Defined.

Global Instance contr_grp_homo_trivial_source `{Funext} G
  : Contr (GroupHomomorphism grp_trivial G).
Proof.
  snrapply Build_Contr.
  1: exact (grp_trivial_rec _).
  intros g.
  rapply equiv_path_grouphomomorphism.
  intros [].
  symmetry.
  rapply grp_homo_unit.
Defined.

Global Instance isterminal_grp_trivial : IsTerminal grp_trivial.
Proof.
  intro G.
  exists (grp_trivial_corec _).
  intros g x.
  apply path_contr.
Defined.

Global Instance contr_grp_homo_trivial_target `{Funext} G
  : Contr (GroupHomomorphism G grp_trivial).
Proof.
  snrapply Build_Contr.
  1: exact (pr1 (isterminal_grp_trivial _)).
  intros g.
  rapply equiv_path_grouphomomorphism.
  intros x.
  apply path_contr.
Defined.

Global Instance ishprop_grp_iso_trivial `{Univalence} (G : Group)
  : IsHProp (GroupIsomorphism G grp_trivial).
Proof.
  apply equiv_hprop_allpath.
  intros f g.
  apply equiv_path_groupisomorphism; intro; apply path_ishprop.
Defined.

(** ** Free groups *)

Definition FactorsThroughFreeGroup (S : Type) (F_S : Group)
  (i : S -> F_S) (A : Group) (g : S -> A) : Type
  := {f : F_S $-> A & f o i == g}.

(** Universal property of a free group on a set (type). *)
Class IsFreeGroupOn (S : Type) (F_S : Group) (i : S -> F_S)
  := contr_isfreegroupon : forall (A : Group) (g : S -> A),
      Contr (FactorsThroughFreeGroup S F_S i A g).
Global Existing Instance contr_isfreegroupon.

(** A group is free if there exists a generating type on which it is a free group *)
Class IsFreeGroup (F_S : Group)
  := isfreegroup : {S : _ & {i : _ & IsFreeGroupOn S F_S i}}.

Global Instance isfreegroup_isfreegroupon (S : Type) (F_S : Group) (i : S -> F_S)
  {H : IsFreeGroupOn S F_S i}
  : IsFreeGroup F_S
  := (S; i; H).
