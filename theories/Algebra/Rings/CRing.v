Require Import Basics Types WildCat.
Require Import Spaces.Nat.
Require Export Classes.interfaces.abstract_algebra.
Require Import Algebra.AbGroups.
Require Export Classes.theory.rings.

(** Theory of commutative rings *)

(** TODO: We should really develop the theory of non-commutative rings seperately, and have commutative rings as a special case of that theory. Similar to how we have Group and AbGroup. But since we are only interested in commutative rings for the time being, it makes sense to only consider them. *)

Declare Scope ring_scope.

Local Open Scope ring_scope.

(** A commutative ring consists of the following data *)
Record CRing := {
  cring_type : Type;
  cring_plus : Plus cring_type;
  cring_mult : Mult cring_type;
  cring_zero : Zero cring_type;
  cring_one  : One  cring_type;
  cring_negate : Negate cring_type;
  cring_isring : IsRing cring_type;
}.

Arguments cring_plus {_}.
Arguments cring_mult {_}.
Arguments cring_zero {_}.
Arguments cring_one {_}.
Arguments cring_negate {_}.
Arguments cring_isring {_}.

Definition issig_CRing : _ <~> CRing := ltac:(issig).

(** We coerce rings to their underlying type. *)
Coercion cring_type : CRing >-> Sortclass.
(** All fields which are typeclasses are global instances *)
Global Existing Instances cring_plus cring_mult cring_zero cring_one cring_negate cring_isring.

(** A ring homomorphism between commutative rings is a map of the underlying type and a proof that this map is a ring homomorphism. *)
Record CRingHomomorphism (A B : CRing) := {
  rng_homo_map : A -> B;
  rng_homo_ishomo : IsSemiRingPreserving rng_homo_map;
}.

Arguments Build_CRingHomomorphism {_ _} _ _.

Definition issig_CRingHomomorphism (A B : CRing)
  : _ <~> CRingHomomorphism A B
  := ltac:(issig).

(** We coerce ring homomorphisms to their underlying maps *)
Coercion rng_homo_map : CRingHomomorphism >-> Funclass.
Global Existing Instance rng_homo_ishomo.

Definition equiv_path_cringhomomorphism `{Funext} {A B : CRing}
  {f g : CRingHomomorphism A B} : f == g <~> f = g.
Proof.
  refine ((equiv_ap (issig_CRingHomomorphism A B)^-1 _ _)^-1 oE _).
  refine (equiv_path_sigma_hprop _ _ oE _).
  apply equiv_path_forall.
Defined.

Definition rng_homo_id (A : CRing) : CRingHomomorphism A A
  := Build_CRingHomomorphism idmap _.

Definition rng_homo_compose {A B C : CRing}
  (f : CRingHomomorphism B C) (g : CRingHomomorphism A B)
  : CRingHomomorphism A C.
Proof.
  snrapply Build_CRingHomomorphism.
  1: exact (f o g).
  rapply compose_sr_morphism.
Defined.

(** Ring laws *)

Section RingLaws.

  (** Many of these ring laws have already been proven. But we give them names here so that they are easy to find and use. *)

  Context {A B : CRing} (f : CRingHomomorphism A B) (x y z : A).

  Definition rng_dist_l : x * (y + z) = x * y + x * z := simple_distribute_l _ _ _.
  Definition rng_dist_r : (x + y) * z = x * z + y * z := simple_distribute_r _ _ _.
  Definition rng_plus_zero_l : 0 + x = x := left_identity _.
  Definition rng_plus_zero_r : x + 0 = x := right_identity _.
  Definition rng_plus_negate_l : (- x) + x = 0 := left_inverse _.
  Definition rng_plus_negate_r : x + (- x) = 0 := right_inverse _.

  Definition rng_plus_comm : x + y = y + x := commutativity x y.
  Definition rng_plus_assoc : x + (y + z) = (x + y) + z := simple_associativity x y z.
  Definition rng_mult_comm : x * y = y * x := commutativity x y.
  Definition rng_mult_assoc : x * (y * z) = (x * y) * z := simple_associativity x y z.

  Definition rng_negate_negate : - (- x) = x := negate_involutive _.

  Definition rng_mult_one_l : 1 * x = x := left_identity _.
  Definition rng_mult_one_r : x * 1 = x := right_identity _.
  Definition rng_mult_zero_l : 0 * x = 0 := left_absorb _.
  Definition rng_mult_zero_r : x * 0 = 0 := right_absorb _.
  Definition rng_mult_negate : -1 * x = - x := (negate_mult _)^.
  Definition rng_mult_negate_negate : -x * -y = x * y := negate_mult_negate _ _.
  Definition rng_mult_negate_l : -x * y = -(x * y) := inverse (negate_mult_distr_l _ _).
  Definition rng_mult_negate_r : x * -y = -(x * y) := inverse (negate_mult_distr_r _ _).

  Definition rng_homo_plus : f (x + y) = f x + f y := preserves_plus x y.
  Definition rng_homo_mult : f (x * y) = f x * f y := preserves_mult x y.
  Definition rng_homo_zero : f 0 = 0 := preserves_0.
  Definition rng_homo_one  : f 1 = 1 := preserves_1.
  Definition rng_homo_negate : f (-x) = -(f x) := preserves_negate x.

  Definition rng_homo_minus_one : f (-1) = -1
    := preserves_negate 1%mc @ ap negate preserves_1.

End RingLaws.

(** Isomorphisms of commutative rings *)
Record CRingIsomorphism (A B : CRing) := {
  rng_iso_homo : CRingHomomorphism A B ;
  isequiv_rng_iso_homo : IsEquiv rng_iso_homo ;
}.

Arguments rng_iso_homo {_ _ }.
Coercion rng_iso_homo : CRingIsomorphism >-> CRingHomomorphism.
Global Existing Instance isequiv_rng_iso_homo.

Infix "≅" := CRingIsomorphism : ring_scope.

Definition issig_CRingIsomorphism {A B : CRing}
  : _ <~> CRingIsomorphism A B := ltac:(issig).

(** We can construct a ring isomorphism from an equivalence that preserves addition and multiplication. *)
Definition Build_CRingIsomorphism' (A B : CRing) (e : A <~> B)
  `{!IsSemiRingPreserving e}
  : CRingIsomorphism A B
  := Build_CRingIsomorphism A B (Build_CRingHomomorphism e _) _.

(** The inverse of a CRing isomorphism *)
Definition rng_iso_inverse {A B : CRing}
  : CRingIsomorphism A B -> CRingIsomorphism B A.
Proof.
  intros [f e].
  snrapply Build_CRingIsomorphism.
  { snrapply Build_CRingHomomorphism.
    1: exact f^-1.
    exact _. }
  exact _.
Defined.

(** CRing isomorphisms are a reflexive relation *)
Global Instance reflexive_cringisomorphism : Reflexive CRingIsomorphism
  := fun x => Build_CRingIsomorphism _ _ (rng_homo_id x) _.

(** CRing isomorphisms are a symmetric relation *)
Global Instance symmetry_cringisomorphism : Symmetric CRingIsomorphism
  := fun x y => rng_iso_inverse.

(** CRing isomorphisms are a transitive relation *)
Global Instance transitive_cringisomorphism : Transitive CRingIsomorphism
  := fun x y z f g => Build_CRingIsomorphism _ _ (rng_homo_compose g f) _.

(** Underlying abelian groups of rings *)
Definition abgroup_cring : CRing -> AbGroup
  := fun A => Build_AbGroup A _ _ _ _.

Coercion abgroup_cring : CRing >-> AbGroup.

(** Underlying group homomorphism of a ring homomorphism *)
Definition grp_homo_rng_homo {R S : CRing}
  : CRingHomomorphism R S -> GroupHomomorphism R S
  := fun f => @Build_GroupHomomorphism R S f _.

Coercion grp_homo_rng_homo : CRingHomomorphism >-> GroupHomomorphism.

(** We can construct a ring homomorphism from a group homomorphism that preserves multiplication *)
Definition Build_CRingHomomorphism' (A B : CRing) (map : GroupHomomorphism A B)
  {H : IsMonoidPreserving (Aop:=cring_mult) (Bop:=cring_mult)
    (Aunit:=one) (Bunit:=one) map}
  : CRingHomomorphism A B
  := Build_CRingHomomorphism map
      (Build_IsSemiRingPreserving _ (grp_homo_ishomo _ _ map) H).

(** We can construct a ring isomorphism from a group isomorphism that preserves multiplication *)
Definition Build_CRingIsomorphism'' (A B : CRing) (e : GroupIsomorphism A B)
  {H : IsMonoidPreserving (Aop:=cring_mult) (Bop:=cring_mult) (Aunit:=one) (Bunit:=one) e}
  : CRingIsomorphism A B
  := @Build_CRingIsomorphism' A B e (Build_IsSemiRingPreserving e _ H).

(** Here is an alternative way to build a commutative ring using the underlying abelian group. *)
Definition Build_CRing' (R : AbGroup)
  `(Mult R, One R, LeftDistribute R mult (abgroup_sgop R))
  (iscomm : @IsCommutativeMonoid R mult one)
  : CRing
  := Build_CRing R (abgroup_sgop R) _ (abgroup_unit R) _
       (abgroup_inverse R) (Build_IsRing _ _ _ _).

(** The image of a ring homomorphism *)
Definition rng_image {R S : CRing} (f : CRingHomomorphism R S) : CRing.
Proof.
  snrapply (Build_CRing' (abgroup_image f)).
  { simpl.
    intros [x p] [y q].
    exists (x * y).
    strip_truncations; apply tr.
    destruct p as [p p'], q as [q q'].
    exists (p * q).
    refine (rng_homo_mult _ _ _ @ _).
    f_ap. }
  { exists 1.
    apply tr.
    exists 1.
    exact (rng_homo_one f). }
  (** Much of this proof is doing the same thing over, so we use some compact tactics. *)
  2: repeat split.
  2: exact _.
  all: intros [].
  1,2,5: intros [].
  1,2: intros [].
  all: apply path_sigma_hprop; cbn.
  1: apply distribute_l.
  1: apply associativity.
  1: apply commutativity.
  1: apply left_identity.
  apply right_identity.
Defined.

Lemma rng_homo_image_incl {R S} (f : CRingHomomorphism R S)
  : CRingHomomorphism (rng_image f) S.
Proof.
  snrapply Build_CRingHomomorphism.
  1: exact pr1.
  repeat split.
Defined.

(** Image of a surjective ring homomorphism *)
Lemma rng_image_issurj {R S} (f : CRingHomomorphism R S) {issurj : IsSurjection f}
  : rng_image f ≅ S.
Proof.
  snrapply Build_CRingIsomorphism.
  1: exact (rng_homo_image_incl f).
  exact _.
Defined. 

(** Wild category of commutative rings *)

Global Instance isgraph_cring : IsGraph CRing
  := Build_IsGraph _ CRingHomomorphism.

Global Instance is01cat_cring : Is01Cat CRing
  := Build_Is01Cat _ _ rng_homo_id (@rng_homo_compose).

Global Instance isgraph_cringhomomorphism {A B : CRing} : IsGraph (A $-> B)
  := induced_graph (@rng_homo_map A B).

Global Instance is01cat_cringhomomorphism {A B : CRing} : Is01Cat (A $-> B)
  := induced_01cat (@rng_homo_map A B).

Global Instance is0gpd_cringhomomorphism {A B : CRing}: Is0Gpd (A $-> B)
  := induced_0gpd (@rng_homo_map A B).

Global Instance is0functor_postcomp_cringhomomorphism {A B C : CRing} (h : B $-> C)
  : Is0Functor (@cat_postcomp CRing _ _ A B C h).
Proof.
  apply Build_Is0Functor.
  intros [f ?] [g ?] p a ; exact (ap h (p a)).
Defined.

Global Instance is0functor_precomp_cringhomomorphism
       {A B C : CRing} (h : A $-> B)
  : Is0Functor (@cat_precomp CRing _ _ A B C h).
Proof.
  apply Build_Is0Functor.
  intros [f ?] [g ?] p a ; exact (p (h a)).
Defined.

(** CRing forms a 1Cat *)
Global Instance is1cat_cring : Is1Cat CRing.
Proof.
  by rapply Build_Is1Cat.
Defined.

Global Instance hasmorext_cring `{Funext} : HasMorExt CRing.
Proof.
  srapply Build_HasMorExt.
  intros A B f g; cbn in *.
  snrapply @isequiv_homotopic.
  1: exact (equiv_path_cringhomomorphism^-1%equiv).
  1: exact _.
  intros []; reflexivity. 
Defined.

Global Instance hasequivs_cring : HasEquivs CRing.
Proof.
  unshelve econstructor.
  + exact CRingIsomorphism.
  + exact (fun G H f => IsEquiv f).
  + intros G H f; exact f.
  + exact Build_CRingIsomorphism.
  + intros G H; exact rng_iso_inverse.
  + cbn; exact _.
  + reflexivity.
  + intros ????; apply eissect.
  + intros ????; apply eisretr.
  + intros G H f g p q.
    exact (isequiv_adjointify f g p q).
Defined.

(** ** Product ring *)

Definition cring_product : CRing -> CRing -> CRing.
Proof.
  intros R S.
  snrapply Build_CRing'.
  1: exact (ab_biprod R S).
  1: exact (fun '(r1 , s1) '(r2 , s2) => (r1 * r2 , s1 * s2)).
  1: exact (cring_one , cring_one).
  { intros [r1 s1] [r2 s2] [r3 s3].
    apply path_prod; cbn; apply rng_dist_l. }
  repeat split.
  1: exact _.
  { intros [r1 s1] [r2 s2] [r3 s3].
    apply path_prod; cbn; apply rng_mult_assoc. }
  1: intros [r1 s1]; apply path_prod; cbn; apply rng_mult_one_l.
  1: intros [r1 s1]; apply path_prod; cbn; apply rng_mult_one_r.
  intros [r1 s1] [r2 s2]; apply path_prod; cbn; apply rng_mult_comm.
Defined.

Infix "×" := cring_product : ring_scope.

Definition cring_product_corec (R S T : CRing)
  : CRingHomomorphism R S -> CRingHomomorphism R T
  -> CRingHomomorphism R (S × T).
Proof.
  intros f g.
  srapply Build_CRingHomomorphism'.
  1: apply (ab_biprod_corec f g).
  repeat split.
  1: cbn; intros x y; apply path_prod; apply rng_homo_mult.
  cbn; apply path_prod; apply rng_homo_one.
Defined.

(** *** More Ring laws *)

(** Powers of ring elements *)
Fixpoint rng_power {R : CRing} (x : R) (n : nat) : R :=
  match n with
  | 0%nat => cring_one
  | n.+1%nat => x * rng_power x n
  end.

(** Power laws *)
Lemma rng_power_mult_law {R : CRing} (x : R) (n m : nat)
  : (rng_power x n) * (rng_power x m) = rng_power x (n + m).
Proof.
  revert m.
  induction n.
  { intros m.
    apply rng_mult_one_l. }
  intros m; cbn.
  refine ((rng_mult_assoc _ _ _)^ @ _).
  f_ap.
Defined.

(** Powers commute with multiplication *)
Lemma rng_power_mult {R : CRing} (x y : R) (n : nat)
  : rng_power (x * y) n = rng_power x n * rng_power y n.
Proof.
  induction n.
  1: symmetry; apply rng_mult_one_l.
  cbn.
  rewrite rng_mult_assoc.
  rewrite <- (rng_mult_assoc x _ y).
  rewrite (rng_mult_comm (rng_power x n) y).
  rewrite rng_mult_assoc.
  rewrite <- (rng_mult_assoc _ (rng_power x n)).
  f_ap.
Defined.


