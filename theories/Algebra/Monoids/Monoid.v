Require Import Basics.Overture Basics.Tactics Basics.Equivalences Basics.Trunc.
Require Import Types.Sigma Types.Forall Types.Prod.
Require Import WildCat.Core WildCat.Induced WildCat.Equiv WildCat.Universe
  WildCat.Products.
Require Import (notations) Classes.interfaces.canonical_names.
Require Export (hints) Classes.interfaces.abstract_algebra.
Require Export (hints) Classes.interfaces.canonical_names.
Require Export Classes.interfaces.canonical_names (SgOp, sg_op,
    MonUnit, mon_unit, LeftIdentity, left_identity, RightIdentity, right_identity,
    Associative, simple_associativity, associativity,
    LeftInverse, left_inverse, RightInverse, right_inverse, Commutative, commutativity).
Export canonical_names.BinOpNotations.
Require Export Classes.interfaces.abstract_algebra (IsSemiGroup(..), sg_set, sg_ass,
    IsMonoid(..), monoid_left_id, monoid_right_id, monoid_semigroup,
    IsMonoidPreserving(..), monmor_unitmor, monmor_sgmor,
    IsSemiGroupPreserving, preserves_sg_op, IsUnitPreserving, preserves_mon_unit).

Local Set Polymorphic Inductive Cumulativity.
Local Set Universe Minimization ToSet.

Local Open Scope mc_mult_scope.

(** * Monoids *)

(** ** Definition *)

Record Monoid := {
  monoid_type :> Type;
  monoid_sgop :: SgOp monoid_type;
  monoid_unit :: MonUnit monoid_type;
  monoid_ismonoid :: IsMonoid monoid_type;
}.

Arguments monoid_sgop {_}.
Arguments monoid_unit {_}.
Arguments monoid_ismonoid {_}.
Global Opaque monoid_ismonoid.

Definition issig_monoid : _ <~> Monoid := ltac:(issig).

Section MonoidLaws.
  Context {M : Monoid} (x y z : M).  
  Definition mnd_assoc := associativity x y z.
  Definition mnd_unit_l := left_identity x.
  Definition mnd_unit_r := right_identity x.
End MonoidLaws.

(** ** Monoid homomorphisms *)

Record MonoidHomomorphism (M N : Monoid) := {
  mnd_homo_map :> monoid_type M -> monoid_type N;
  ismonoidpreserving_mnd_homo :: IsMonoidPreserving mnd_homo_map;
}.

Arguments mnd_homo_map {M N}.
Arguments Build_MonoidHomomorphism {M N} _ _.
Arguments ismonoidpreserving_mnd_homo {M N} f : rename.

Definition issig_MonoidHomomorphism (M N : Monoid)
  : _ <~> MonoidHomomorphism M N
  := ltac:(issig).

(** ** Basics properties of monoid homomorphisms *)

Definition mnd_homo_op {M N : Monoid} (f : MonoidHomomorphism M N)
  : forall (x y : M), f (x * y) = f x * f y
  := monmor_sgmor. 

Definition mnd_homo_unit {M N : Monoid} (f : MonoidHomomorphism M N)
  : f mon_unit = mon_unit
  := monmor_unitmor.

Definition equiv_path_monoidhomomorphism `{Funext} {M N : Monoid}
  {f g : MonoidHomomorphism M N}
  : f == g <~> f = g.
Proof.
  refine ((equiv_ap (issig_MonoidHomomorphism M N)^-1 _ _)^-1 oE _).
  refine (equiv_path_sigma_hprop _ _ oE _).
  apply equiv_path_forall.
Defined.

Global Instance ishset_monoidhomomorphism `{Funext} {M N : Monoid}
  : IsHSet (MonoidHomomorphism M N).
Proof.
  apply istrunc_S.
  intros f g; apply (istrunc_equiv_istrunc _ equiv_path_monoidhomomorphism).
Defined.

Definition mnd_homo_id {M : Monoid} : MonoidHomomorphism M M
  := Build_MonoidHomomorphism idmap _.

Definition mnd_homo_compose {M N P : Monoid}
  : MonoidHomomorphism N P -> MonoidHomomorphism M N
  -> MonoidHomomorphism M P
  := fun f g => Build_MonoidHomomorphism (f o g) _.

(** ** Monoid Isomorphisms *)

Record MonoidIsomorphism (M N : Monoid) := {
  mnd_iso_homo :> MonoidHomomorphism M N;
  isequiv_mnd_iso :: IsEquiv mnd_iso_homo;
}.

Definition Build_MonoidIsomorphism' {M N : Monoid}
  (f : M <~> N) (h : IsMonoidPreserving f)
  : MonoidHomomorphism M N.
Proof.
  snrapply Build_MonoidIsomorphism.
  1: srapply Build_MonoidHomomorphism.
  exact _.
Defined.

Definition issig_MonoidIsomorphism (M N : Monoid)
  : _ <~> MonoidIsomorphism M N
  := ltac:(issig).

Coercion equiv_mnd_iso {M N : Monoid}
  : MonoidIsomorphism M N -> M <~> N
  := fun f => Build_Equiv M N f _. 

Definition mnd_iso_id {M : Monoid} : MonoidIsomorphism M M
  := Build_MonoidIsomorphism _ _ mnd_homo_id _.

Definition mnd_iso_compose {M N P : Monoid}
  : MonoidIsomorphism N P -> MonoidIsomorphism M N
  -> MonoidIsomorphism M P
  := fun g f => Build_MonoidIsomorphism _ _ (mnd_homo_compose g f) _.

Definition mnd_iso_inverse {M N : Monoid}
  : MonoidIsomorphism M N -> MonoidIsomorphism N M
  := fun f => Build_MonoidIsomorphism _ _ (Build_MonoidHomomorphism f^-1 _) _.

Global Instance reflexive_monoidisomorphism
  : Reflexive MonoidIsomorphism
  := fun M => mnd_iso_id.

Global Instance symmetric_monoidisomorphism
  : Symmetric MonoidIsomorphism
  := fun M N => mnd_iso_inverse.

Global Instance transitive_monoidisomorphism
  : Transitive MonoidIsomorphism
  := fun M N P f g => mnd_iso_compose g f.

(** ** The category of monoids *)

Global Instance isgraph_monoid : IsGraph Monoid
  := Build_IsGraph Monoid MonoidHomomorphism.

Global Instance is01cat_monoid : Is01Cat Monoid
  := Build_Is01Cat Monoid _ (@mnd_homo_id) (@mnd_homo_compose).

Local Notation mnd_homo_map' M N
  := (@mnd_homo_map M N : _ -> (monoid_type M $-> _)).

Global Instance is2graph_monoid : Is2Graph Monoid
  := fun M N => isgraph_induced (mnd_homo_map' M N).

Global Instance isgraph_monoidhomomorphism {M N : Monoid} : IsGraph (M $-> N)
  := isgraph_induced (mnd_homo_map' M N).

Global Instance is01cat_monoidhomomorphism {M N : Monoid} : Is01Cat (M $-> N)
  := is01cat_induced (mnd_homo_map' M N).

Global Instance is0gpd_monoidhomomorphism {M N : Monoid} : Is0Gpd (M $-> N)
  := is0gpd_induced (mnd_homo_map' M N).

Global Instance is0functor_postcomp_monoidhomomorphism
  {M N P : Monoid} (h : N $-> P)
  : Is0Functor (@cat_postcomp Monoid _ _ M N P h).
Proof.
  apply Build_Is0Functor.
  intros ? ? p a; exact (ap h (p a)).
Defined.

Global Instance is0functor_precomp_monoidhomomorphism
  {M N P : Monoid} (h : M $-> N)
  : Is0Functor (@cat_precomp Monoid _ _ M N P h).
Proof.
  apply Build_Is0Functor.
  intros ? ? p; exact (p o h).
Defined.

Global Instance is1cat_monoid : Is1Cat Monoid.
Proof.
  by rapply Build_Is1Cat.
Defined.

Global Instance hasequivs_monoid : HasEquivs Monoid.
Proof.
  snrapply Build_HasEquivs.
  - exact MonoidIsomorphism.
  - exact (fun M N f => IsEquiv f).
  - intros M N f; exact f.
  - cbn; exact _.
  - exact Build_MonoidIsomorphism.
  - reflexivity.
  - intros M N; exact mnd_iso_inverse.
  - intros ????; apply eissect.
  - intros ????; apply eisretr.
  - intros M N; exact isequiv_adjointify.
Defined.

Global Instance is0functor_monoid_type : Is0Functor monoid_type
  := Build_Is0Functor _ _ _ _ monoid_type (@mnd_homo_map).

Global Instance is1functor_monoid_type : Is1Functor monoid_type.
Proof.
  by apply Build_Is1Functor.
Defined.

(** ** Direct product of monoids *)

Definition mnd_prod : Monoid -> Monoid -> Monoid.
Proof.
  intros M N.
  snrapply (Build_Monoid (M * N)).
  3: repeat split.
  - intros [m1 n1] [m2 n2].
    exact (m1 * m2, n1 * n2).
  - exact (mon_unit, mon_unit).
  - exact _.
  - intros x y z; snrapply path_prod; nrapply mnd_assoc.
  - intros x; snrapply path_prod; nrapply mnd_unit_l.
  - intros x; snrapply path_prod; nrapply mnd_unit_r.
Defined.

Definition mnd_prod_pr1 {M N : Monoid}
  : MonoidHomomorphism (mnd_prod M N) M.
Proof.
  snrapply Build_MonoidHomomorphism.
  1: exact fst.
  split; hnf; reflexivity.
Defined.

Definition mnd_prod_pr2 {M N : Monoid}
  : MonoidHomomorphism (mnd_prod M N) N.
Proof.
  snrapply Build_MonoidHomomorphism.
  1: exact snd.
  split; hnf; reflexivity.
Defined.

Definition mnd_prod_corec {M N P : Monoid}
  (f : MonoidHomomorphism P M)
  (g : MonoidHomomorphism P N)
  : MonoidHomomorphism P (mnd_prod M N).
Proof.
  snrapply Build_MonoidHomomorphism.
  2: split.
  - exact (fun x => (f x, g x)).
  - intros x y; snrapply path_prod; nrapply mnd_homo_op.
  - snrapply path_prod; nrapply mnd_homo_unit.
Defined.

Global Instance hasbinaryproducts_monoid : HasBinaryProducts Monoid.
Proof.
  intros M N.
  snrapply Build_BinaryProduct.
  - exact (mnd_prod M N).
  - exact mnd_prod_pr1.
  - exact mnd_prod_pr2.
  - intros P; exact mnd_prod_corec.
  - intros P f g; exact (Id _).
  - intros P f g; exact (Id _).
  - intros P f g p q a; exact (path_prod' (p a) (q a)).
Defined.
