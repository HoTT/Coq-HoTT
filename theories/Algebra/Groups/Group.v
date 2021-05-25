Require Import Basics Types.
Require Import HProp HFiber HSet.
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
Local Open Scope wc_iso_scope.

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
(** We should never need to unfold the proof that something is a group. *)
Global Opaque group_isgroup.

(** We coerce groups back to types. *)
Coercion group_type : Group >-> Sortclass.
Global Existing Instances group_sgop group_unit group_inverse group_isgroup.

Definition issig_group : _ <~> Group
  := ltac:(issig).

(** * Proof automation *)
(** Many times in group theoretic proofs we want some form of automation for obvious identities. Here we implement such a behaviour. *)

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
  intros f g; apply (istrunc_equiv_istrunc _ equiv_path_grouphomomorphism).
Defined.

(** * Some basic properties of group homomorphisms *)


(** Group homomorphisms preserve identities *)
Definition grp_homo_unit {G H} (f : GroupHomomorphism G H)
  : f (mon_unit) = mon_unit.
Proof.
  apply monmor_unitmor.
Defined.
#[export] Hint Immediate grp_homo_unit : group_db.

(** Group homomorphisms preserve group operations *)
Definition grp_homo_op {G H} (f : GroupHomomorphism G H)
  : forall x y : G, f (x * y) = f x * f y.
Proof.
  apply monmor_sgmor.
Defined.
#[export] Hint Immediate grp_homo_op : group_db.

(** Group homomorphisms preserve inverses *)
Definition grp_homo_inv {G H} (f : GroupHomomorphism G H)
  : forall x, f (- x) = -(f x).
Proof.
  intro x.
  apply (inverse_unique (f x)).
  + refine (_ @ grp_homo_unit f).
    refine ((grp_homo_op f (-x) x)^ @ _).
    apply ap.
    apply grp_inv_l.
  + apply grp_inv_r.
Defined.
#[export] Hint Immediate grp_homo_inv : group_db.

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
  refine (_ @ (grp_unit_r _)^).
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
  intros f g; apply (istrunc_equiv_istrunc _ (equiv_path_groupisomorphism _ _)).
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

Definition grp_iso_id {G : Group} : GroupIsomorphism G G
  := Build_GroupIsomorphism _ _ grp_homo_id _.

Definition grp_homo_const {G H : Group} : GroupHomomorphism G H.
Proof.
  snrapply Build_GroupHomomorphism.
  - exact (fun _ => mon_unit).
  - intros x y.
    exact (grp_unit_l mon_unit)^.
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
Global Instance isequiv_group_left_op {G : Group}
  : forall (x : G), IsEquiv (x *.).
Proof.
  intro x.
  srapply isequiv_adjointify.
  1: exact (-x *.).
  all: intro y.
  all: refine (grp_assoc _ _ _ @ _ @ grp_unit_l y).
  all: refine (ap (fun x => x * y) _).
  1: apply grp_inv_r.
  apply grp_inv_l.
Defined.

(** Right multiplication is an equivalence *)
Global Instance isequiv_group_right_op (G : Group)
  : forall (x : G), IsEquiv (fun y => y * x).
Proof.
  intro x.
  srapply isequiv_adjointify.
  1: exact (fun y => y * - x).
  all: intro y.
  all: refine ((grp_assoc _ _ _)^ @ _ @ grp_unit_r y).
  all: refine (ap (y *.) _).
  1: apply grp_inv_l.
  apply grp_inv_r.
Defined.

Global Instance isequiv_group_inverse {G : Group}
  : IsEquiv ((-) : G -> G).
Proof.
  srapply isequiv_adjointify.
  1: apply (-).
  all: intro; apply negate_involutive.
Defined.

(** ** Working with equations in groups *)

Section GroupEquations.

  Context {G : Group} (x y z : G).

  (** Inverses are involutive *)
  Definition grp_inv_inv : --x = x := negate_involutive x.

  (** Inverses distribute over the group operation *)
  Definition grp_inv_op : - (x * y) = -y * -x := negate_sg_op x y.

End GroupEquations.

(** ** Cancelation *)

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

  Definition grp_moveL_gM : x * -z = y <~> x = y * z
    := equiv_moveL_equiv_M (f := fun t => t * z) _ _.

  Definition grp_moveL_Mg : -y * x = z <~> x = y * z
    := equiv_moveL_equiv_M (f := fun t => y * t) _ _.

  Definition grp_moveR_gM : x = z * -y <~> x * y = z
    := equiv_moveR_equiv_M (f := fun t => t * y) _ _.

  Definition grp_moveR_Mg : y = -x * z <~> x * y = z
    := equiv_moveR_equiv_M (f := fun t => x * t) _ _.

  (** *** Moving inverses.*)
  (** These are the inverses of the previous but are included here for completeness*)
  Definition grp_moveR_gV : x = y * z <~> x * -z = y
    := equiv_moveR_equiv_V (f := fun t => t * z) _ _.

  Definition grp_moveR_Vg : x = y * z <~> -y * x = z 
    := equiv_moveR_equiv_V (f := fun t => y * t) _ _.

  Definition grp_moveL_gV :  x * y = z <~> x = z * -y
    := equiv_moveL_equiv_V (f := fun t => t * y) _ _.

  Definition grp_moveL_Vg :  x * y = z <~> y = -x * z
    := equiv_moveL_equiv_V (f := fun t => x * t) _ _.

(** We close the section here so the previous lemmas genearlise their assumptions. *)
End GroupMovement.

Section GroupMovement.

  Context {G : Group} {x y z : G}.

  (** *** Moving elements equal to unit. *)

  Definition grp_moveL_1M : x * -y = mon_unit <~> x = y
    := equiv_concat_r (grp_unit_l _) _ oE grp_moveL_gM.

  Definition grp_moveL_M1 : -y * x = mon_unit <~> x = y
    := equiv_concat_r (grp_unit_r _) _ oE grp_moveL_Mg.

  Definition grp_moveR_1M : mon_unit = y * (-x) <~> x = y
    := (equiv_concat_l (grp_unit_l _) _)^-1%equiv oE grp_moveR_gM.

  Definition grp_moveR_M1 : mon_unit = -x * y <~> x = y
    := (equiv_concat_l (grp_unit_r _) _)^-1%equiv oE grp_moveR_Mg.

  (** *** Cancelling elements equal to unit. *)

  Definition grp_cancelL1 : x = mon_unit <~> z * x = z
    := (equiv_concat_r (grp_unit_r _) _ oE grp_cancelL z).

  Definition grp_cancelR1 : x = mon_unit <~> x * z = z
    := (equiv_concat_r (grp_unit_l _) _) oE grp_cancelR z.

End GroupMovement.

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

(** Given a group element [a0 : A] over [b : B], multiplication by [a] establishes an equivalence between the kernel and the fiber over [b]. *)
Lemma equiv_grp_hfiber {A B : Group} (f : GroupHomomorphism A B) (b : B)
  : forall (a0 : hfiber f b), hfiber f b <~> hfiber f mon_unit.
Proof.
  intros [a0 p].
  refine (equiv_transport (hfiber f) (right_inverse b) oE _).
  snrapply Build_Equiv.
  { srapply (functor_hfiber (h := fun t => t * -a0) (k := fun t => t * -b)).
    intro a; cbn; symmetry.
    refine (_ @ ap (fun x => f a * (- x)) p).
    exact (grp_homo_op f _ _ @ ap (fun x => f a * x) (grp_homo_inv f a0)). }
  srapply isequiv_functor_hfiber.
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
  intros ??; symmetry; apply grp_unit_l.
Defined.

(** Map into trivial group *)
Definition grp_trivial_corec (G : Group) : GroupHomomorphism G grp_trivial.
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact (fun _ => tt).
  intros ??; symmetry; exact (grp_unit_l _).
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
  repeat split.
  1: exact _.
  all: grp_auto.
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

Global Instance isembedding_grp_prod_inl {H K : Group}
  : IsEmbedding (@grp_prod_inl H K).
Proof.
  apply isembedding_isinj_hset.
  intros h0 h1 p; cbn in p.
  exact (fst ((equiv_path_prod _ _)^-1 p)).
Defined.

Global Instance isembedding_grp_prod_inr {H K : Group}
  : IsEmbedding (@grp_prod_inr H K).
Proof.
  apply isembedding_isinj_hset.
  intros k0 k1 q; cbn in q.
  exact (snd ((equiv_path_prod _ _)^-1 q)).
Defined.

Definition grp_prod_pr1 {G H : Group}
  : GroupHomomorphism (grp_prod G H) G.
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact fst.
  intros ? ?; reflexivity.
Defined.

Definition grp_prod_pr2 {G H : Group}
  : GroupHomomorphism (grp_prod G H) H.
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact snd.
  intros ? ?; reflexivity.
Defined.

Global Instance issurj_grp_prod_pr1 {G H : Group}
  : IsSurjection (@grp_prod_pr1 G H)
  := issurj_retr grp_prod_inl (fun _ => idpath).

Global Instance issurj_grp_prod_pr2 {G H : Group}
  : IsSurjection (@grp_prod_pr2 G H)
  := issurj_retr grp_prod_inr (fun _ => idpath).

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

(** A group is free if there exists a generating type on which it is a free group *)
Class IsFreeGroup (F_S : Group)
  := isfreegroup : {S : _ & {i : _ & IsFreeGroupOn S F_S i}}.

Global Instance isfreegroup_isfreegroupon (S : Type) (F_S : Group) (i : S -> F_S)
  {H : IsFreeGroupOn S F_S i}
  : IsFreeGroup F_S
  := (S; i; H).
