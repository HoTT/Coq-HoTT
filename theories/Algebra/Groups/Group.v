Require Import Basics Types HProp HFiber HSet.
Require Import Homotopy.IdentitySystems.
Require Import (notations) Classes.interfaces.canonical_names.
Require Export (hints) Classes.interfaces.abstract_algebra.
Require Export (hints) Classes.interfaces.canonical_names.
(** We only export the parts of these that will be most useful to users of this file. *)
Require Export Classes.interfaces.canonical_names (SgOp, sg_op, MonUnit, mon_unit,
    LeftIdentity, left_identity, RightIdentity, right_identity,
    Inverse, inv, Associative, simple_associativity, associativity,
    LeftInverse, left_inverse, RightInverse, right_inverse, Commutative, commutativity).
Export canonical_names.BinOpNotations.
Require Export Classes.interfaces.abstract_algebra (IsGroup(..), group_monoid, inverse_l, inverse_r,
    IsSemiGroup(..), sg_set, sg_ass,
    IsMonoid(..), monoid_left_id, monoid_right_id, monoid_semigroup,
    IsMonoidPreserving(..), monmor_unitmor, monmor_sgmor,
    IsSemiGroupPreserving, preserves_sg_op, IsUnitPreserving, preserves_mon_unit).
Require Export Classes.theory.groups.
Require Import Pointed.Core.
Require Import WildCat.
Require Import Spaces.Nat.Core Spaces.Int.
Require Import Truncations.Core.

Local Set Polymorphic Inductive Cumulativity.

Generalizable Variables G H A B C f g.

Declare Scope group_scope.

(** * Groups *)

(** A group is an abstraction of several common situations in mathematics. For example, consider the symmetries of an object.  Two symmetries can be combined; there is a symmetry that does nothing; and any symmetry can be reversed. Such situations arise in geometry, algebra and, importantly for us, homotopy theory. *)

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope wc_iso_scope.

(** ** Definition of a Group *)

(** A group consists of a type, an operation on that type, a unit and an inverse that satisfy the group axioms in [IsGroup]. *)
Record Group := {
  group_type :> Type;
  group_sgop :: SgOp group_type;
  group_unit :: MonUnit group_type;
  group_inverse :: Inverse group_type;
  group_isgroup :: IsGroup group_type;
}.

Arguments group_sgop {_}.
Arguments group_unit {_}.
Arguments group_inverse {_}.
Arguments group_isgroup {_}.
(** We should never need to unfold the proof that something is a group. *)
Global Opaque group_isgroup.

Definition issig_group : _ <~> Group
  := ltac:(issig).

(** ** Proof automation *)
(** Many times in group theoretic proofs we want some form of automation for obvious identities. Here we implement such a behavior. *)

(** We create a database of hints for the group theory library *)
Create HintDb group_db.

(** Our group laws can be proven easily with tactics such as [rapply associativity]. However this requires a typeclass search on more general algebraic structures. Therefore we explicitly list many groups laws here so that coq can use them. We also create hints for each law in our groups database. *)
Section GroupLaws.
  Context {G : Group} (x y z : G).

  Definition grp_assoc := associativity x y z.
  Definition grp_unit_l := left_identity x.
  Definition grp_unit_r := right_identity x.
  Definition grp_inv_l := left_inverse x.
  Definition grp_inv_r := right_inverse x.

End GroupLaws.

#[export] Hint Immediate grp_assoc  : group_db.
#[export] Hint Immediate grp_unit_l : group_db.
#[export] Hint Immediate grp_unit_r : group_db.
#[export] Hint Immediate grp_inv_l  : group_db.
#[export] Hint Immediate grp_inv_r  : group_db.

(** Given path types in a product we may want to decompose. *)
#[export] Hint Extern 5 (@paths (_ * _) _ _) => (apply path_prod) : group_db.
(** Given path types in a sigma type of a hprop family (i.e. a subset) we may want to decompose. *)
#[export] Hint Extern 6 (@paths (sig _) _ _) => (rapply path_sigma_hprop) : group_db.

(** We also declare a tactic (notation) for automatically solving group laws *)
(** TODO: improve this tactic so that it also rewrites and is able to solve basic group lemmas. *)
Tactic Notation "grp_auto" := hnf; intros; eauto with group_db.

(** ** Some basic properties of groups *)

(** Groups are pointed sets with point the identity. *)
Global Instance ispointed_group (G : Group)
  : IsPointed G := @mon_unit G _.

Definition ptype_group : Group -> pType
  := fun G => [G, _].

Coercion ptype_group : Group >-> pType.
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

(** With other assumptions, the right inverse law follows from the left inverse law. *)
Definition right_inverse_left_inverse (G : Type) `{IsHSet G}
  `(SgOp G, MonUnit G, Inverse G, !Associative (.*.),
    !LeftIdentity (.*.) mon_unit,
    !LeftInverse (.*.) (^) mon_unit)
  : RightInverse (.*.) (^) mon_unit.
Proof.
  intros x.
  lhs_V rapply left_identity.
  apply (transport (fun x => x * _ = x) (left_inverse x^)).
  lhs_V rapply simple_associativity.
  nrapply ap.
  lhs rapply simple_associativity.
  lhs nrapply (ap (.* x^)).
  1: apply left_inverse.
  apply left_identity.
Defined.
Global Opaque right_inverse_left_inverse.
  
(** With other assumptions, the right identity law follows from the left identity law. *)
Definition right_identity_left_identity (G : Type) `{IsHSet G}
  `(SgOp G, MonUnit G, Inverse G, !Associative (.*.),
    !LeftIdentity (.*.) mon_unit,
    !LeftInverse (.*.) (^) mon_unit)
  : RightIdentity (.*.) mon_unit.
Proof.
  intros x.
  lhs_V rapply left_identity.
  rhs_V rapply left_identity.
  apply (transport (fun x => x * _ = x * _) (left_inverse x^)).
  lhs_V rapply simple_associativity.
  rhs_V rapply simple_associativity.
  nrapply ap.
  lhs rapply simple_associativity.
  lhs apply (ap (.* mon_unit) (left_inverse x)).
  lhs apply left_identity.
  symmetry; apply left_inverse.
Defined.
Global Opaque right_identity_left_identity.

(** When building a group we can choose to omit the right inverse law and right identity law, since they follow from the left ones. *)
Definition Build_Group' (G : Type) `{IsHSet G}
  `(SgOp G, MonUnit G, Inverse G, !Associative (.*.),
    !LeftIdentity (.*.) mon_unit,
    !LeftInverse (.*.) (^) mon_unit)
  : Group.
Proof.
  rapply (Build_Group G).
  repeat split.
  4: nrapply right_identity_left_identity; exact _.
  5: nrapply right_inverse_left_inverse; exact _.
  all: exact _.
Defined.

(** ** Group homomorphisms *)

(** Group homomorphisms are maps between groups that preserve the group operation. They allow us to compare groups and map their structure to one another. This is useful for determining if two groups are really the same, in which case we say they are "isomorphic". *)

(** A group homomorphism consists of a map between groups and a proof that the map preserves the group operation. *)
Record GroupHomomorphism (G H : Group) := Build_GroupHomomorphism {
  grp_homo_map :> group_type G -> group_type H;
  issemigrouppreserving_grp_homo :: IsSemiGroupPreserving grp_homo_map;
}.

Arguments grp_homo_map {G H}.
Arguments Build_GroupHomomorphism {G H} _ _.
Arguments issemigrouppreserving_grp_homo {G H} f _ : rename.

(** ** Basic properties of group homomorphisms *)

(** Group homomorphisms preserve group operations. This is an alias for [issemigrouppreserving_grp_homo] with the identity written explicitly. *)
Definition grp_homo_op
  : forall {G H : Group} (f : GroupHomomorphism G H) (x y : G), f (x * y) = f x * f y
  := @issemigrouppreserving_grp_homo.
#[export] Hint Immediate grp_homo_op : group_db.

(** Group homomorphisms are unit preserving. *)
Global Instance isunitpreserving_grp_homo {G H : Group}
  (f : GroupHomomorphism G H)
  : IsUnitPreserving f.
Proof.
  unfold IsUnitPreserving.
  apply (group_cancelL (f mon_unit)).
  rhs nrapply grp_unit_r.
  rhs_V rapply (ap  _ (monoid_left_id _ mon_unit)).
  symmetry.
  nrapply issemigrouppreserving_grp_homo.
Defined.

(** Group homomorphisms preserve identities. This is an alias for the previous statement. *)
Definition grp_homo_unit
  : forall {G H : Group} (f : GroupHomomorphism G H), f mon_unit = mon_unit
  := @isunitpreserving_grp_homo.
#[export] Hint Immediate grp_homo_unit : group_db.

(** Therefore, group homomorphisms are monoid homomorphisms. *)
Global Instance ismonoidpreserving_grp_homo {G H : Group}
  (f : GroupHomomorphism G H)
  : IsMonoidPreserving f
  := {}.

(** Group homomorphisms are pointed maps. *)
Definition pmap_GroupHomomorphism {G H : Group} (f : GroupHomomorphism G H) : G ->* H
  := Build_pMap G H f (isunitpreserving_grp_homo f).
Coercion pmap_GroupHomomorphism : GroupHomomorphism >-> pForall.

Definition issig_GroupHomomorphism (G H : Group) : _ <~> GroupHomomorphism G H
  := ltac:(issig).

(** Function extensionality for group homomorphisms. *)
Definition equiv_path_grouphomomorphism {F : Funext} {G H : Group}
  {g h : GroupHomomorphism G H} : g == h <~> g = h.
Proof.
  refine ((equiv_ap (issig_GroupHomomorphism G H)^-1 _ _)^-1 oE _).
  refine (equiv_path_sigma_hprop _ _ oE _).
  apply equiv_path_forall.
Defined.

(** Group homomorphisms are sets, in the presence of funext. *)
Global Instance ishset_grouphomomorphism {F : Funext} {G H : Group}
  : IsHSet (GroupHomomorphism G H).
Proof.
  apply istrunc_S.
  intros f g; apply (istrunc_equiv_istrunc _ equiv_path_grouphomomorphism).
Defined.

(** Group homomorphisms preserve inverses. *)
Definition grp_homo_inv {G H} (f : GroupHomomorphism G H)
  : forall x, f x^ = (f x)^.
Proof.
  intro x.
  apply (inverse_unique (f x)).
  + refine (_ @ grp_homo_unit f).
    refine ((grp_homo_op f _ x)^ @ _).
    apply ap.
    apply grp_inv_l.
  + apply grp_inv_r.
Defined.
#[export] Hint Immediate grp_homo_inv : group_db.

(** The identity map is a group homomorphism. *)
Definition grp_homo_id {G : Group} : GroupHomomorphism G G
  := Build_GroupHomomorphism idmap _.

(** The composition of the underlying functions of two group homomorphisms is also a group homomorphism. *)
Definition grp_homo_compose {G H K : Group}
  : GroupHomomorphism H K -> GroupHomomorphism G H -> GroupHomomorphism G K.
Proof.
  intros f g.
  srapply (Build_GroupHomomorphism (f o g)).
Defined.

(** ** Group Isomorphisms *)

(** Group isomorphsims are group homomorphisms whose underlying map happens to be an equivalence. They allow us to consider two groups to be the "same". They can be inverted and composed just like equivalences. *)

(** An isomorphism of groups is defined as group homomorphism that is an equivalence. *)
Record GroupIsomorphism (G H : Group) := Build_GroupIsomorphism {
  grp_iso_homo :> GroupHomomorphism G H;
  isequiv_group_iso :: IsEquiv grp_iso_homo;
}.

(** We can build an isomorphism from an operation-preserving equivalence. *)
Definition Build_GroupIsomorphism' {G H : Group}
  (f : G <~> H) (h : IsSemiGroupPreserving f)
  : GroupIsomorphism G H.
Proof.
  srapply Build_GroupIsomorphism.
  1: srapply Build_GroupHomomorphism.
  exact _.
Defined.

Definition issig_GroupIsomorphism (G H : Group)
  : _ <~> GroupIsomorphism G H := ltac:(issig).

(** The underlying equivalence of a group isomorphism. *)
Definition equiv_groupisomorphism {G H : Group}
  : GroupIsomorphism G H -> G <~> H
  := fun f => Build_Equiv G H f _.
Coercion equiv_groupisomorphism : GroupIsomorphism >-> Equiv.

(** The underlying pointed equivalence of a group isomorphism. *)
Definition pequiv_groupisomorphism {A B : Group}
  : GroupIsomorphism A B -> (A <~>* B)
  := fun f => Build_pEquiv _ _ f _.
Coercion pequiv_groupisomorphism : GroupIsomorphism >-> pEquiv.

(** Funext for group isomorphisms. *)
Definition equiv_path_groupisomorphism `{F : Funext} {G H : Group}
  (f g : GroupIsomorphism G H)
  : f == g <~> f = g.
Proof.
  refine ((equiv_ap (issig_GroupIsomorphism G H)^-1 _ _)^-1 oE _).
  refine (equiv_path_sigma_hprop _ _ oE _).
  apply equiv_path_grouphomomorphism.
Defined.

(** Group isomorphisms form a set. *)
Definition ishset_groupisomorphism `{F : Funext} {G H : Group}
  : IsHSet (GroupIsomorphism G H).
Proof.
  apply istrunc_S.
  intros f g; apply (istrunc_equiv_istrunc _ (equiv_path_groupisomorphism _ _)).
Defined.

(** The identity map is an equivalence and therefore a group isomorphism. *)
Definition grp_iso_id {G : Group} : GroupIsomorphism G G
  := Build_GroupIsomorphism _ _ grp_homo_id _.

(** Group isomorphisms can be composed by composing the underlying group homomorphism. *)
Definition grp_iso_compose {G H K : Group}
  (g : GroupIsomorphism H K) (f : GroupIsomorphism G H)
  : GroupIsomorphism G K
  := Build_GroupIsomorphism _ _ (grp_homo_compose g f) _.

(** Group isomorphisms can be inverted. The inverse map of the underlying equivalence also preserves the group operation and unit. *)
Definition grp_iso_inverse {G H : Group}
  : GroupIsomorphism G H -> GroupIsomorphism H G.
Proof.
  intros [f e].
  srapply Build_GroupIsomorphism.
  - srapply (Build_GroupHomomorphism f^-1).
  - exact _.
Defined.

(** Group isomorphism is a reflexive relation. *)
Global Instance reflexive_groupisomorphism
  : Reflexive GroupIsomorphism
  := fun G => grp_iso_id.

(** Group isomorphism is a symmetric relation. *)
Global Instance symmetric_groupisomorphism
  : Symmetric GroupIsomorphism
  := fun G H => grp_iso_inverse.

(** Group isomorphism is a transitive relation. *)
Global Instance transitive_groupisomorphism
  : Transitive GroupIsomorphism
  := fun G H K f g => grp_iso_compose g f.

(** Under univalence, equality of groups is equivalent to isomorphism of groups. This is the structure identity principle for groups. *)
Definition equiv_path_group' {U : Univalence} {G H : Group}
  : GroupIsomorphism G H <~> G = H.
Proof.
  equiv_via {f : G <~> H & IsSemiGroupPreserving f}.
  1: make_equiv.
  revert G H; apply (equiv_path_issig_contr issig_group).
  - intros [G [? [? [? ?]]]].
    exists 1%equiv.
    exact _.
  - intros [G [op [unit [neg ax]]]]; cbn.
    contr_sigsig G (equiv_idmap G).
    srefine (Build_Contr _ ((_;(_;(_;_)));_) _); cbn.
    1: assumption.
    1: exact _.
    intros [[op' [unit' [neg' ax']]] eq].
    apply path_sigma_hprop; cbn.
    refine (@ap _ _ (fun x : { oun :
      { oo : SgOp G & { u : MonUnit G & Inverse G}}
      & @IsGroup G oun.1 oun.2.1 oun.2.2}
      => (x.1.1 ; x.1.2.1 ; x.1.2.2 ; x.2))
      ((op;unit;neg);ax) ((op';unit';neg');ax') _).
    apply path_sigma_hprop; cbn.
    srefine (path_sigma' _ _ _).
    1: funext x y; apply eq.
    rewrite transport_const.
    pose (f := Build_GroupHomomorphism
        (G:=Build_Group G op unit neg ax)
        (H:=Build_Group G op' unit' neg' ax')
        idmap eq).
    srefine (path_sigma' _ _ _).
    1: exact (grp_homo_unit f).
    lhs nrapply transport_const.
    funext x.
    exact (grp_homo_inv f x).
Defined.

(** A version with nicer universe variables. *)
Definition equiv_path_group@{u v | u < v} {U : Univalence} {G H : Group@{u}}
  : GroupIsomorphism G H <~> (paths@{v} G H)
  := equiv_path_group'.

(** ** Simple group equivalences *)

(** Left multiplication is an equivalence. *)
Global Instance isequiv_group_left_op {G : Group}
  : forall (x : G), IsEquiv (x *.).
Proof.
  intro x.
  srapply isequiv_adjointify.
  1: exact (x^ *.).
  all: intro y.
  all: refine (grp_assoc _ _ _ @ _ @ grp_unit_l y).
  all: refine (ap (fun x => x * y) _).
  1: apply grp_inv_r.
  apply grp_inv_l.
Defined.

(** Right multiplication is an equivalence. *)
Global Instance isequiv_group_right_op (G : Group)
  : forall (x : G), IsEquiv (fun y => y * x).
Proof.
  intro x.
  srapply isequiv_adjointify.
  1: exact (fun y => y * x^).
  all: intro y.
  all: refine ((grp_assoc _ _ _)^ @ _ @ grp_unit_r y).
  all: refine (ap (y *.) _).
  1: apply grp_inv_l.
  apply grp_inv_r.
Defined.

(** The operation inverting group elements is an equivalence. Note that, since the order of the operation will change after inversion, this isn't a group homomorphism. *)
Global Instance isequiv_group_inverse {G : Group}
  : IsEquiv ((^) : G -> G).
Proof.
  srapply isequiv_involution.
  rapply inverse_involutive.
Defined.

(** ** Reasoning with equations in groups. *)

Section GroupEquations.

  Context {G : Group} (x y z : G).

  (** Inverses are involutive. *)
  Definition grp_inv_inv : x^^ = x := inverse_involutive x.

  (** Inverses distribute over the group operation. *)
  Definition grp_inv_op : (x * y)^ = y^ * x^ := inverse_sg_op x y.
  
  (** The inverse of the unit is the unit. *)
  Definition grp_inv_unit : mon_unit^ = mon_unit := inverse_mon_unit (G :=G).

  Definition grp_inv_V_gg : x^ * (x * y) = y
    := grp_assoc _ _ _ @ ap (.* y) (grp_inv_l x) @ grp_unit_l y.

  Definition grp_inv_g_Vg : x * (x^ * y) = y
    := grp_assoc _ _ _ @ ap (.* y) (grp_inv_r x) @ grp_unit_l y.

  Definition grp_inv_gg_V : (x * y) * y^ = x
    := (grp_assoc _ _ _)^ @ ap (x *.) (grp_inv_r y) @ grp_unit_r x.

  Definition grp_inv_gV_g : (x * y^) * y = x
    := (grp_assoc _ _ _)^ @ ap (x *.) (grp_inv_l y) @ grp_unit_r x.

  Definition grp_1g_g1 : x = y <~> 1 * x = y * 1
    := equiv_concat_r (grp_unit_r _)^ _ oE equiv_concat_l (grp_unit_l _) _.

  Definition grp_g1_1g : x = y <~> x * 1 = 1 * y
    := equiv_concat_r (grp_unit_l _)^ _ oE equiv_concat_l (grp_unit_r _) _.

End GroupEquations.

(** ** Cancelation lemmas *)

(** Group elements can be cancelled both on the left and the right. *)
Definition grp_cancelL {G : Group} {x y : G} z : x = y <~> z * x = z * y
  := equiv_ap (fun x => z * x) _ _.
Definition grp_cancelR {G : Group} {x y : G} z : x = y <~> x * z = y * z
  := equiv_ap (fun x => x * z) _ _.

(** ** Group movement lemmas *)

Section GroupMovement.

  (** Since left/right multiplication is an equivalence, we can use lemmas about moving equivalences around to prove group movement lemmas. *)

  Context {G : Group} {x y z : G}.

  (** *** Moving group elements *)

  Definition grp_moveL_gM : x * z^ = y <~> x = y * z
    := equiv_moveL_equiv_M (f := fun t => t * z) _ _.

  Definition grp_moveL_Mg : y^ * x = z <~> x = y * z
    := equiv_moveL_equiv_M (f := fun t => y * t) _ _.

  Definition grp_moveR_gM : x = z * y^ <~> x * y = z
    := equiv_moveR_equiv_M (f := fun t => t * y) _ _.

  Definition grp_moveR_Mg : y = x^ * z <~> x * y = z
    := equiv_moveR_equiv_M (f := fun t => x * t) _ _.

  (** *** Moving inverses.*)
  (** These are the inverses of the previous but are included here for completeness*)
  Definition grp_moveR_gV : x = y * z <~> x * z^ = y
    := equiv_moveR_equiv_V (f := fun t => t * z) _ _.

  Definition grp_moveR_Vg : x = y * z <~> y^ * x = z
    := equiv_moveR_equiv_V (f := fun t => y * t) _ _.

  Definition grp_moveL_gV :  x * y = z <~> x = z * y^
    := equiv_moveL_equiv_V (f := fun t => t * y) _ _.

  Definition grp_moveL_Vg :  x * y = z <~> y = x^ * z
    := equiv_moveL_equiv_V (f := fun t => x * t) _ _.

(** We close the section here so the previous lemmas generalise their assumptions. *)
End GroupMovement.

Section GroupMovement.

  Context {G : Group} {x y z : G}.

  (** *** Moving elements equal to unit. *)

  Definition grp_moveL_1M : x * y^ = 1 <~> x = y
    := equiv_concat_r (grp_unit_l _) _ oE grp_moveL_gM.
  
  Definition grp_moveL_M1 : y^ * x = 1 <~> x = y
    := equiv_concat_r (grp_unit_r _) _ oE grp_moveL_Mg.
  
  Definition grp_moveL_1V : x * y = 1 <~> x = y^
    := equiv_concat_r (grp_unit_l _) _ oE grp_moveL_gV.
  
  Definition grp_moveL_V1 : y * x = 1 <~> x = y^
    := equiv_concat_r (grp_unit_r _) _ oE grp_moveL_Vg.

  Definition grp_moveR_1M : 1 = y * x^ <~> x = y
    := (equiv_concat_l (grp_unit_l _) _)^-1 oE grp_moveR_gM.
  
  Definition grp_moveR_M1 : 1 = x^ * y <~> x = y
    := (equiv_concat_l (grp_unit_r _) _)^-1 oE grp_moveR_Mg.
  
  Definition grp_moveR_1V : 1 = y * x <~> x^ = y
    := (equiv_concat_l (grp_unit_l _) _)^-1 oE grp_moveR_gV.

  Definition grp_moveR_V1 : mon_unit = x * y <~> x^ = y
    := (equiv_concat_l (grp_unit_r _) _)^-1 oE grp_moveR_Vg.

  (** *** Cancelling elements equal to unit. *)

  Definition grp_cancelL1 : x = mon_unit <~> z * x = z
    := (equiv_concat_r (grp_unit_r _) _ oE grp_cancelL z).

  Definition grp_cancelR1 : x = mon_unit <~> x * z = z
    := (equiv_concat_r (grp_unit_l _) _) oE grp_cancelR z.

End GroupMovement.

(** ** Commutation *)

(** If [g] commutes with [h], then [g] commutes with the inverse [-h]. *)
Definition grp_commutes_inv {G : Group} (g h : G) (p : g * h = h * g)
  : g * h^ = h^ * g.
Proof.
  apply grp_moveR_gV.
  rhs_V apply simple_associativity.
  by apply grp_moveL_Vg.
Defined.

(** If [g] commutes with [h] and [h'], then [g] commutes with their product [h * h']. *)
Definition grp_commutes_op {G : Group} (g h h' : G)
  (p : g * h = h * g) (p' : g * h' = h' * g)
  : g * (h * h') = (h * h') * g.
Proof.
  lhs apply simple_associativity.
  lhs nrapply (ap (.* h') p).
  lhs_V apply simple_associativity.
  lhs nrapply (ap (h *.) p').
  by apply simple_associativity.
Defined.

(** ** Power operation *)

(** For a given [g : G] we can define the function [Int -> G] sending an integer to that power of [g]. *)
Definition grp_pow {G : Group} (g : G) (n : Int) : G
  := int_iter (g *.) n mon_unit.

(** Any homomorphism respects [grp_pow]. In other words, [fun g => grp_pow g n] is natural. *)
Lemma grp_pow_natural {G H : Group} (f : GroupHomomorphism G H) (n : Int) (g : G)
  : f (grp_pow g n) = grp_pow (f g) n.
Proof.
  lhs snrapply (int_iter_commute_map _ ((f g) *.)).
  1: nrapply grp_homo_op.
  apply (ap (int_iter _ n)), grp_homo_unit.
Defined.

(** All powers of the unit are the unit. *)
Definition grp_pow_unit {G : Group} (n : Int)
  : grp_pow (G:=G) mon_unit n = mon_unit.
Proof.
  snrapply (int_iter_invariant n _ (fun g => g = mon_unit)); cbn.
  1, 2: apply paths_ind_r.
  - apply grp_unit_r.
  - lhs nrapply grp_unit_r. apply grp_inv_unit.
  - reflexivity.
Defined.

(** Note that powers don't preserve the group operation as it is not commutative. This does hold in an abelian group so such a result will appear later. *)

(** The next two results tell us how [grp_pow] unfolds. *)
Definition grp_pow_succ {G : Group} (n : Int) (g : G)
  : grp_pow g (n.+1)%int = g * grp_pow g n
  := int_iter_succ_l _ _ _.

Definition grp_pow_pred {G : Group} (n : Int) (g : G)
  : grp_pow g (n.-1)%int = g^ * grp_pow g n
  := int_iter_pred_l _ _ _.

(** [grp_pow] satisfies an additive law of exponents. *)
Definition grp_pow_add {G : Group} (m n : Int) (g : G)
  : grp_pow g (n + m)%int = grp_pow g n * grp_pow g m.
Proof.
  lhs nrapply int_iter_add.
  induction n; cbn.
  1: symmetry; exact (grp_unit_l _).
  1: rewrite int_iter_succ_l, grp_pow_succ.
  2: rewrite int_iter_pred_l, grp_pow_pred; cbn.
  1,2 : rhs_V srapply associativity;
        apply ap, IHn.
Defined.

(** [grp_pow] commutes negative exponents to powers of the inverse *)
Definition grp_pow_neg {G : Group} (n : Int) (g : G)
  : grp_pow g (int_neg n) = grp_pow g^ n.
Proof.
  lhs nrapply int_iter_neg.
  cbn; unfold grp_pow.
  (* These agree, except for the proofs that [sg_op g^] is an equivalence. *)
  apply int_iter_agree.
Defined.

(** Using a negative power in [grp_pow] is the same as first using a positive power and then inverting the result. *)
Definition grp_pow_neg_inv {G: Group} (m : Int) (g : G)
  : grp_pow g (- m)%int = (grp_pow g m)^.
Proof.
  apply grp_moveL_1V.
  lhs_V nrapply grp_pow_add.
  by rewrite int_add_neg_l.
Defined.

(** Combining the two previous results gives that a power of an inverse is the inverse of the power. *)
Definition grp_pow_neg_inv' {G: Group} (n: Int) (g : G)
  : grp_pow g^ n = (grp_pow g n)^.
Proof.
  lhs_V nrapply grp_pow_neg.
  apply grp_pow_neg_inv.
Defined.

(** [grp_pow] satisfies a multiplicative law of exponents. *)
Definition grp_pow_int_mul {G : Group} (m n : Int) (g : G)
  : grp_pow g (m * n)%int = grp_pow (grp_pow g m) n.
Proof.
  induction n.
  - simpl.
    by rewrite int_mul_0_r.
  - rewrite int_mul_succ_r.
    rewrite grp_pow_add.
    rewrite grp_pow_succ.
    apply grp_cancelL, IHn.
  - rewrite int_mul_pred_r.
    rewrite grp_pow_add.
    rewrite grp_pow_neg_inv.
    rewrite grp_pow_pred.
    apply grp_cancelL, IHn.
Defined.

(** If [h] commutes with [g], then [h] commutes with [grp_pow g n]. *)
Definition grp_pow_commutes {G : Group} (n : Int) (g h : G)
  (p : h * g = g * h)
  : h * (grp_pow g n) = (grp_pow g n) * h.
Proof.
  induction n.
  - by apply grp_g1_1g.
  - rewrite grp_pow_succ.
    nrapply grp_commutes_op; assumption.
  - rewrite grp_pow_pred.
    nrapply grp_commutes_op.
    2: assumption.
    apply grp_commutes_inv, p.
Defined.

(** [grp_pow g n] commutes with [g]. *)
Definition grp_pow_commutes' {G : Group} (n : Int) (g : G)
  : g * grp_pow g n = grp_pow g n * g.
Proof.
  by apply grp_pow_commutes.
Defined.

(** If [g] and [h] commute, then [grp_pow (g * h) n] = (grp_pow g n) * (grp_pow h n)]. *)
Definition grp_pow_mul {G : Group} (n : Int) (g h : G)
  (c : g * h = h * g)
  : grp_pow (g * h) n = (grp_pow g n) * (grp_pow h n).
Proof.
  induction n.
  - simpl.
    symmetry; nrapply grp_unit_r.
  - rewrite 3 grp_pow_succ.
    rewrite IHn.
    rewrite 2 grp_assoc.
    apply grp_cancelR.
    rewrite <- 2 grp_assoc.
    apply grp_cancelL.
    apply grp_pow_commutes.
    exact c^%path.
  - simpl.
    rewrite 3 grp_pow_pred.
    rewrite IHn.
    rewrite 2 grp_assoc.
    apply grp_cancelR.
    rewrite c.
    rewrite grp_inv_op.
    rewrite <- 2 grp_assoc.
    apply grp_cancelL.
    apply grp_pow_commutes.
    symmetry; apply grp_commutes_inv, c.
Defined.

(** ** The category of Groups *)

(** ** Groups together with homomorphisms form a 1-category whose equivalences are the group isomorphisms. *)

Global Instance isgraph_group : IsGraph Group
  := Build_IsGraph Group GroupHomomorphism.

Global Instance is01cat_group : Is01Cat Group :=
  Build_Is01Cat Group _ (@grp_homo_id) (@grp_homo_compose).

(** Helper notation so that the wildcat instances can easily be inferred. *)
Local Notation grp_homo_map' A B := (@grp_homo_map A B : _ -> (group_type A $-> _)).

Global Instance is2graph_group : Is2Graph Group
  := fun A B => isgraph_induced (grp_homo_map' A B).

Global Instance isgraph_grouphomomorphism {A B : Group} : IsGraph (A $-> B)
  := isgraph_induced (grp_homo_map' A B).

Global Instance is01cat_grouphomomorphism {A B : Group} : Is01Cat (A $-> B)
  := is01cat_induced (grp_homo_map' A B).

Global Instance is0gpd_grouphomomorphism {A B : Group}: Is0Gpd (A $-> B)
  := is0gpd_induced (grp_homo_map' A B).

Global Instance is0functor_postcomp_grouphomomorphism {A B C : Group} (h : B $-> C)
  : Is0Functor (@cat_postcomp Group _ _ A B C h).
Proof.
  apply Build_Is0Functor.
  intros f g p a ; exact (ap h (p a)).
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

(** Under [Funext], the category of groups has morphism extensionality. *)
Global Instance hasmorext_group `{Funext} : HasMorExt Group.
Proof.
  srapply Build_HasMorExt.
  intros A B f g; cbn in *.
  snrapply @isequiv_homotopic.
  1: exact (equiv_path_grouphomomorphism^-1%equiv).
  1: exact _.
  intros []; reflexivity. 
Defined.

(** Group isomorphisms become equivalences in the category of groups. *)
Global Instance hasequivs_group
  : HasEquivs Group.
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

(** The [group_type] map is a 1-functor. *)

Global Instance is0functor_type_group : Is0Functor group_type.
Proof.
  apply Build_Is0Functor.
  rapply @grp_homo_map.
Defined.

Global Instance is1functor_type_group : Is1Functor group_type.
Proof.
  by apply Build_Is1Functor.
Defined.

(** The [ptype_group] map is a 1-functor. *)

Global Instance is0functor_ptype_group : Is0Functor ptype_group.
Proof.
  apply Build_Is0Functor.
  rapply @pmap_GroupHomomorphism.
Defined.

Global Instance is1functor_ptype_group : Is1Functor ptype_group.
Proof.
  apply Build_Is1Functor; intros; by apply phomotopy_homotopy_hset.
Defined.

(** Given a group element [a0 : A] over [b : B], multiplication by [a] establishes an equivalence between the kernel and the fiber over [b]. *)
Lemma equiv_grp_hfiber {A B : Group} (f : GroupHomomorphism A B) (b : B)
  : forall (a0 : hfiber f b), hfiber f b <~> hfiber f mon_unit.
Proof.
  intros [a0 p].
  refine (equiv_transport (hfiber f) (right_inverse b) oE _).
  snrapply Build_Equiv.
  { srapply (functor_hfiber (h := (.* a0^)) (k := (.* b^))).
    intro a; cbn; symmetry.
    rhs_V nrapply (ap (fun x => f a * x^) p).
    exact (grp_homo_op f _ _ @ ap (f a *.) (grp_homo_inv f a0)). }
  srapply isequiv_functor_hfiber.
Defined.

(** ** The trivial group *)

Definition grp_trivial : Group.
Proof.
  refine (Build_Group Unit (fun _ _ => tt) tt (fun _ => tt) _).
  repeat split; try exact _; by intros [].
Defined.

(** Map out of trivial group. *)
Definition grp_trivial_rec (G : Group) : GroupHomomorphism grp_trivial G.
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact (fun _ => group_unit).
  intros ??; symmetry; apply grp_unit_l.
Defined.

(** Map into trivial group. *)
Definition grp_trivial_corec (G : Group) : GroupHomomorphism G grp_trivial.
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact (fun _ => tt).
  intros ??; symmetry; exact (grp_unit_l _).
Defined.

(** Group is a pointed category. *)
Global Instance ispointedcat_group : IsPointedCat Group.
Proof.
  snrapply Build_IsPointedCat.
  - exact grp_trivial.
  - intro G.
    exists (grp_trivial_rec G).
    intros g []; cbn.
    exact (grp_homo_unit g)^%path.
  - intro G.
    exists (grp_trivial_corec G).
    intros g x; cbn.
    apply path_unit.
Defined.

Definition grp_homo_const {G H : Group} : GroupHomomorphism G H
  := zero_morphism.

(** ** The direct product of groups *)

(** The cartesian product of the underlying sets of two groups has a natural group structure. We call this the direct product of groups. *)
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
    exact (g^, h^). }
  repeat split.
  1: exact _.
  all: grp_auto.
Defined.

(** Maps into the direct product can be built by mapping separately into each factor. *)
Proposition grp_prod_corec {G H K : Group} (f : K $-> G) (g : K $-> H)
  : K $-> (grp_prod G H).
Proof.
  snrapply Build_GroupHomomorphism.
  - exact (fun x : K => (f x, g x)).
  - intros x y.
    apply path_prod'; apply grp_homo_op.
Defined.

(** [grp_prod_corec] satisfies a definitional naturality property. *)
Definition grp_prod_corec_natural {X Y A B : Group}
  (f : X $-> Y) (g0 : Y $-> A) (g1 : Y $-> B)
  : grp_prod_corec g0 g1 $o f $== grp_prod_corec (g0 $o f) (g1 $o f)
  := fun _ => idpath.

(** The left factor injects into the direct product. *)
Definition grp_prod_inl {H K : Group}
  : H $-> (grp_prod H K)
  := grp_prod_corec grp_homo_id grp_homo_const.

(** The left injection is an embedding. *)
Global Instance isembedding_grp_prod_inl {H K : Group}
  : IsEmbedding (@grp_prod_inl H K).
Proof.
  apply isembedding_isinj_hset.
  intros h0 h1 p; cbn in p.
  exact (fst ((equiv_path_prod _ _)^-1 p)).
Defined.

(** The right factor injects into the direct product. *)
Definition grp_prod_inr {H K : Group}
  : K $-> (grp_prod H K)
  := grp_prod_corec grp_homo_const grp_homo_id.

(** The right injection is an embedding. *)
Global Instance isembedding_grp_prod_inr {H K : Group}
  : IsEmbedding (@grp_prod_inr H K).
Proof.
  apply isembedding_isinj_hset.
  intros k0 k1 q; cbn in q.
  exact (snd ((equiv_path_prod _ _)^-1 q)).
Defined.

(** Given two pairs of isomorphic groups, their pairwise direct products are isomorphic. *)
Definition grp_iso_prod {A B C D : Group}
  : A ≅ B -> C ≅ D -> (grp_prod A C) ≅ (grp_prod B D).
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

(** The first projection of the direct product. *)
Definition grp_prod_pr1 {G H : Group}
  : GroupHomomorphism (grp_prod G H) G.
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact fst.
  intros ? ?; reflexivity.
Defined.

(** The first projection is a surjection. *)
Global Instance issurj_grp_prod_pr1 {G H : Group}
  : IsSurjection (@grp_prod_pr1 G H)
  := issurj_retr grp_prod_inl (fun _ => idpath).

(** The second projection of the direct product. *)
Definition grp_prod_pr2 {G H : Group}
  : GroupHomomorphism (grp_prod G H) H.
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact snd.
  intros ? ?; reflexivity.
Defined.

(** Pairs in direct products can be decomposed *)
Definition grp_prod_decompose {G H : Group} (g : G) (h : H)
  : (g, h) = ((g, group_unit) : grp_prod G H) * (group_unit, h).
Proof.
  snrapply path_prod; symmetry.
  - snrapply grp_unit_r.
  - snrapply grp_unit_l.
Defined.

(** The second projection is a surjection. *)
Global Instance issurj_grp_prod_pr2 {G H : Group}
  : IsSurjection (@grp_prod_pr2 G H)
  := issurj_retr grp_prod_inr (fun _ => idpath).

(** [Group] is a category with binary products given by the direct product. *)
Global Instance hasbinaryproducts_group : HasBinaryProducts Group.
Proof.
  intros G H.
  snrapply Build_BinaryProduct.
  - exact (grp_prod G H).
  - exact grp_prod_pr1.
  - exact grp_prod_pr2.
  - intros K.
    exact grp_prod_corec.
  - intros K f g.
    exact (Id _).
  - intros K f g.
    exact (Id _).
  - intros K f g p q a.
    exact (path_prod' (p a) (q a)).
Defined.

(** *** Properties of maps to and from the trivial group *)

Global Instance isinitial_grp_trivial : IsInitial grp_trivial.
Proof.
  intro G.
  exists (grp_trivial_rec _).
  intros g [].
  apply (grp_homo_unit g)^%path.
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

Global Instance ishprop_grp_iso_trivial `{Funext} (G : Group)
  : IsHProp (G ≅ grp_trivial).
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

(** A group is free if there exists a generating type on which it is a free group. *)
Class IsFreeGroup (F_S : Group)
  := isfreegroup : {S : _ & {i : _ & IsFreeGroupOn S F_S i}}.

Global Instance isfreegroup_isfreegroupon (S : Type) (F_S : Group) (i : S -> F_S)
  {H : IsFreeGroupOn S F_S i}
  : IsFreeGroup F_S
  := (S; i; H).


(** ** Further properties of group homomorphisms. *)

(** Commutativity can be transferred across isomorphisms. *)
Definition commutative_iso_commutative {G H : Group}
  {C : Commutative (@group_sgop G)} (f : GroupIsomorphism G H)
  : Commutative (@group_sgop H).
Proof.
  unfold Commutative.
  rapply (equiv_ind f); intro g1.
  rapply (equiv_ind f); intro g2.
  refine ((preserves_sg_op _ _)^ @ _ @ (preserves_sg_op _ _)).
  refine (ap f _).
  apply C.
Defined.

(** If two group homomorphisms agree on two elements, then they agree on their product. *)
Definition grp_homo_op_agree {G G' H : Group} (f : G $-> H) (f' : G' $-> H)
  {x y : G} {x' y' : G'} (p : f x = f' x') (q : f y = f' y')
  : f (x * y) = f' (x' * y').
Proof.
  lhs nrapply grp_homo_op.
  rhs nrapply grp_homo_op.
  exact (ap011 _ p q).
Defined.

(** The group movement lemmas can be extended to when there is a homomorphism involved.  For now, we only include these two. *)
Definition grp_homo_moveL_1V {A B : Group} (f : GroupHomomorphism A B) (x y : A)
  : f (x * y) = group_unit <~> (f x = - f y)
  := grp_moveL_1V oE equiv_concat_l (grp_homo_op f x y)^ _.

Definition grp_homo_moveL_1M  {A B : Group} (f : GroupHomomorphism A B) (x y : A)
  : f (x * y^) = group_unit <~> (f x = f y).
Proof.
  refine (grp_moveL_1M oE equiv_concat_l _^ _).
  lhs nrapply grp_homo_op.
  apply ap, grp_homo_inv.
Defined.

(** ** Conjugation *)

(** Conjugation by a group element is a homomorphism. Often we need to use properties about group homomorphisms in order to prove things about conjugation, so it is helpful to define it directly as a group homomorphism. *)
Definition grp_conj {G : Group} (x : G) : G $-> G.
Proof.
  snrapply Build_GroupHomomorphism.
  - exact (fun y => x * y * x^).
  - intros y z.
    rhs nrapply grp_assoc.
    apply (ap (.* x^)).
    rhs nrapply grp_assoc.
    lhs nrapply grp_assoc.
    apply (ap (.* z)).
    symmetry; apply grp_inv_gV_g.
Defined.

(** Conjugation by the unit element is the identity. *)
Definition grp_conj_unit {G : Group} : grp_conj (G:=G) 1 $== Id _.
Proof.
  intros x.
  apply grp_moveR_gV.
  by nrapply grp_1g_g1.
Defined.

(** Conjugation commutes with group homomorphisms. *)
Definition grp_homo_conj {G H : Group} (f : G $-> H) (x : G)
  : f $o grp_conj x $== grp_conj (f x) $o f.
Proof.
  intros z; simpl.
  by rewrite !grp_homo_op, grp_homo_inv.
Defined.

(** Conjugation respects composition. *)
Definition grp_conj_op {G : Group} (x y : G)
  : grp_conj (x * y) $== grp_conj x $o grp_conj y.
Proof.
  intros z; simpl.
  by rewrite grp_inv_op, !grp_assoc.
Defined.

(** Conjugating by an element then its inverse is the identity. *)
Definition grp_conj_inv_r {G : Group} (x : G)
  : grp_conj x $o grp_conj x^ $== Id _.
Proof.
  refine ((grp_conj_op _ _)^$ $@ _ $@ grp_conj_unit).
  intros y.
  nrapply (ap (fun x => grp_conj x y)).
  apply grp_inv_r.
Defined.

(** Conjugating by an inverse then the element is the identity. *)
Definition grp_conj_inv_l {G : Group} (x : G)
  : grp_conj x^ $o grp_conj x $== Id _.
Proof.
  refine ((grp_conj_op _ _)^$ $@ _ $@ grp_conj_unit).
  intros y.
  nrapply (ap (fun x => grp_conj x y)).
  apply grp_inv_l.
Defined.

(** Conjugation is a group automorphism. *)
Definition grp_iso_conj {G : Group} (x : G) : G $<~> G
  := cate_adjointify (grp_conj x) (grp_conj x^)
      (grp_conj_inv_r _) (grp_conj_inv_l _).
