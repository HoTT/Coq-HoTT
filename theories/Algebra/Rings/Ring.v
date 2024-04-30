Require Import WildCat.
Require Import Spaces.Nat.Core.
(* Some of the material in abstract_algebra and canonical names could be selectively exported to the user, as is done in Groups/Group.v. *)
Require Import Classes.interfaces.abstract_algebra.
Require Import Algebra.AbGroups.
Require Export Classes.theory.rings.
Require Import Modalities.ReflectiveSubuniverse.

(** * Rings *)

Declare Scope ring_scope.

Local Open Scope ring_scope.
(** We want to print equivalences as [≅]. *)
Local Open Scope wc_iso_scope.

(** A ring consists of the following data: *)
Record Ring := Build_Ring' {
  (** An underlying abelian group. *)
  ring_abgroup :> AbGroup;
  (** A multiplication operation. *)
  ring_mult :: Mult ring_abgroup;
  (** A multiplicative identity called [one]. *)
  ring_one :: One ring_abgroup;
  (** Such that all they all satisfy the axioms of a ring. *)
  ring_isring :: IsRing ring_abgroup;
  (** This field only exists so that opposite rings are definitionally involutive and can safely be ignored. *)
  ring_mult_assoc_opp : forall x y z, (x * y) * z = x * (y * z);
}.


Arguments ring_mult {_}.
Arguments ring_one {_}.
Arguments ring_isring {_}.

Definition issig_Ring : _ <~> Ring := ltac:(issig).

Global Instance ring_plus {R : Ring} : Plus R := plus_abgroup (ring_abgroup R).
Global Instance ring_zero {R : Ring} : Zero R := zero_abgroup (ring_abgroup R).
Global Instance ring_negate {R : Ring} : Negate R := negate_abgroup (ring_abgroup R).

(** A ring homomorphism between rings is a map of the underlying type and a proof that this map is a ring homomorphism. *)
Record RingHomomorphism (A B : Ring) := {
  rng_homo_map :> A -> B;
  rng_homo_ishomo :: IsSemiRingPreserving rng_homo_map;
}.

Arguments Build_RingHomomorphism {_ _} _ _.

Definition issig_RingHomomorphism (A B : Ring)
  : _ <~> RingHomomorphism A B
  := ltac:(issig).

Definition equiv_path_ringhomomorphism `{Funext} {A B : Ring}
  {f g : RingHomomorphism A B} : f == g <~> f = g.
Proof.
  refine ((equiv_ap (issig_RingHomomorphism A B)^-1 _ _)^-1 oE _).
  refine (equiv_path_sigma_hprop _ _ oE _).
  apply equiv_path_forall.
Defined.

Definition rng_homo_id (A : Ring) : RingHomomorphism A A
  := Build_RingHomomorphism idmap (Build_IsSemiRingPreserving _ _ _).

Definition rng_homo_compose {A B C : Ring}
  (f : RingHomomorphism B C) (g : RingHomomorphism A B)
  : RingHomomorphism A C.
Proof.
  snrapply Build_RingHomomorphism.
  1: exact (f o g).
  rapply compose_sr_morphism.
Defined.

(** ** Ring laws *)

Section RingLaws.

  (** Many of these ring laws have already been proven. But we give them names here so that they are easy to find and use. *)

  Context {A B : Ring} (f : RingHomomorphism A B) (x y z : A).

  Definition rng_dist_l : x * (y + z) = x * y + x * z := simple_distribute_l _ _ _.
  Definition rng_dist_r : (x + y) * z = x * z + y * z := simple_distribute_r _ _ _.
  Definition rng_plus_zero_l : 0 + x = x := left_identity _.
  Definition rng_plus_zero_r : x + 0 = x := right_identity _.
  Definition rng_plus_negate_l : (- x) + x = 0 := left_inverse _.
  Definition rng_plus_negate_r : x + (- x) = 0 := right_inverse _.

  Definition rng_plus_comm : x + y = y + x := commutativity x y.
  Definition rng_plus_assoc : x + (y + z) = (x + y) + z := simple_associativity x y z.
  Definition rng_mult_assoc : x * (y * z) = (x * y) * z := simple_associativity x y z.

  Definition rng_negate_negate : - (- x) = x := groups.negate_involutive _.

  Definition rng_mult_one_l : 1 * x = x := left_identity _.
  Definition rng_mult_one_r : x * 1 = x := right_identity _.
  Definition rng_mult_zero_l : 0 * x = 0 := left_absorb _.
  Definition rng_mult_zero_r : x * 0 = 0 := right_absorb _.
  Definition rng_mult_negate : -1 * x = - x := (negate_mult_l _)^.
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
Record RingIsomorphism (A B : Ring) := {
  rng_iso_homo : RingHomomorphism A B ;
  isequiv_rng_iso_homo : IsEquiv rng_iso_homo ;
}.

Arguments rng_iso_homo {_ _ }.
Coercion rng_iso_homo : RingIsomorphism >-> RingHomomorphism.
Global Existing Instance isequiv_rng_iso_homo.

Definition issig_RingIsomorphism {A B : Ring}
  : _ <~> RingIsomorphism A B := ltac:(issig).

(** We can construct a ring isomorphism from an equivalence that preserves addition and multiplication. *)
Definition Build_RingIsomorphism' (A B : Ring) (e : A <~> B)
  `{!IsSemiRingPreserving e}
  : RingIsomorphism A B
  := Build_RingIsomorphism A B (Build_RingHomomorphism e _) _.

(** The inverse of a Ring isomorphism *)
Definition rng_iso_inverse {A B : Ring}
  : RingIsomorphism A B -> RingIsomorphism B A.
Proof.
  intros [f e].
  snrapply Build_RingIsomorphism.
  { snrapply Build_RingHomomorphism.
    1: exact f^-1.
    exact _. }
  exact _.
Defined.

(** Ring isomorphisms are a reflexive relation *)
Global Instance reflexive_ringisomorphism : Reflexive RingIsomorphism
  := fun x => Build_RingIsomorphism _ _ (rng_homo_id x) _.

(** Ring isomorphisms are a symmetric relation *)
Global Instance symmetry_ringisomorphism : Symmetric RingIsomorphism
  := fun x y => rng_iso_inverse.

(** Ring isomorphisms are a transitive relation *)
Global Instance transitive_ringisomorphism : Transitive RingIsomorphism
  := fun x y z f g => Build_RingIsomorphism _ _ (rng_homo_compose g f) _.

(** Underlying group homomorphism of a ring homomorphism *)
Definition grp_homo_rng_homo {R S : Ring}
  : RingHomomorphism R S -> GroupHomomorphism R S
  := fun f => @Build_GroupHomomorphism R S f _.

Coercion grp_homo_rng_homo : RingHomomorphism >-> GroupHomomorphism.

(** We can construct a ring homomorphism from a group homomorphism that preserves multiplication *)
Definition Build_RingHomomorphism' (A B : Ring) (map : GroupHomomorphism A B)
  {H : IsMonoidPreserving (Aop:=ring_mult) (Bop:=ring_mult)
    (Aunit:=one) (Bunit:=one) map}
  : RingHomomorphism A B
  := Build_RingHomomorphism map
      (Build_IsSemiRingPreserving _ (grp_homo_ishomo _ _ map) H).

(** We can construct a ring isomorphism from a group isomorphism that preserves multiplication *)
Definition Build_RingIsomorphism'' (A B : Ring) (e : GroupIsomorphism A B)
  {H : IsMonoidPreserving (Aop:=ring_mult) (Bop:=ring_mult) (Aunit:=one) (Bunit:=one) e}
  : RingIsomorphism A B
  := @Build_RingIsomorphism' A B e (Build_IsSemiRingPreserving e _ H).

(** Here is an alternative way to build a commutative ring using the underlying abelian group. *)
Definition Build_Ring (R : AbGroup)
  `(Mult R, One R, LeftDistribute R mult (@group_sgop R), RightDistribute R mult (@group_sgop R))
  (iscomm : @IsMonoid R mult one)
  : Ring
  := Build_Ring' R _ _ (Build_IsRing _ _ _  _ _) (fun x y z => (associativity x y z)^).

(** ** Ring movement lemmas *)

Section RingMovement.

  (** We adopt a similar naming convention to the [moveR_equiv] style lemmas that can be found in Types.Paths. *)

  Context {R : Ring} {x y z : R}.

  Definition rng_moveL_Mr : - y + x = z <~> x = y + z := @grp_moveL_Mg R x y z.
  Definition rng_moveL_rM : x + - z = y <~> x = y + z := @grp_moveL_gM R x y z.
  Definition rng_moveR_Mr : y = - x + z <~> x + y = z := @grp_moveR_Mg R x y z.
  Definition rng_moveR_rM : x = z + - y <~> x + y = z := @grp_moveR_gM R x y z.

  Definition rng_moveL_Vr : x + y = z <~> y = - x + z := @grp_moveL_Vg R x y z.
  Definition rng_moveL_rV : x + y = z <~> x = z + - y := @grp_moveL_gV R x y z.
  Definition rng_moveR_Vr : x = y + z <~> - y + x = z := @grp_moveR_Vg R x y z.
  Definition rng_moveR_rV : x = y + z <~> x + - z = y := @grp_moveR_gV R x y z.

  Definition rng_moveL_M0 : - y + x = 0 <~> x = y := @grp_moveL_M1 R x y.
  Definition rng_moveL_0M :	x + - y = 0 <~> x = y := @grp_moveL_1M R x y.
  Definition rng_moveR_M0 : 0 = - x + y <~> x = y := @grp_moveR_M1 R x y.
  Definition rng_moveR_0M : 0 = y + - x <~> x = y := @grp_moveR_1M R x y.

  (** TODO: Movement laws about mult *)

End RingMovement.

(** ** Wild category of rings *)

Global Instance isgraph_ring : IsGraph Ring
  := Build_IsGraph _ RingHomomorphism.

Global Instance is01cat_ring : Is01Cat Ring
  := Build_Is01Cat _ _ rng_homo_id (@rng_homo_compose).

Global Instance is2graph_ring : Is2Graph Ring
  := fun A B => isgraph_induced (@rng_homo_map A B : _ -> (group_type _ $-> _)).

Global Instance is01cat_ringhomomorphism {A B : Ring} : Is01Cat (A $-> B)
  := is01cat_induced (@rng_homo_map A B).

Global Instance is0gpd_ringhomomorphism {A B : Ring} : Is0Gpd (A $-> B)
  := is0gpd_induced (@rng_homo_map A B).

Global Instance is0functor_postcomp_ringhomomorphism {A B C : Ring} (h : B $-> C)
  : Is0Functor (@cat_postcomp Ring _ _ A B C h).
Proof.
  apply Build_Is0Functor.
  intros [f ?] [g ?] p a ; exact (ap h (p a)).
Defined.

Global Instance is0functor_precomp_ringhomomorphism
       {A B C : Ring} (h : A $-> B)
  : Is0Functor (@cat_precomp Ring _ _ A B C h).
Proof.
  apply Build_Is0Functor.
  intros [f ?] [g ?] p a ; exact (p (h a)).
Defined.

(** Ring forms a 1-category. *)
Global Instance is1cat_ring : Is1Cat Ring.
Proof.
  by rapply Build_Is1Cat.
Defined.

Global Instance hasmorext_ring `{Funext} : HasMorExt Ring.
Proof.
  srapply Build_HasMorExt.
  intros A B f g; cbn in *.
  snrapply @isequiv_homotopic.
  1: exact (equiv_path_ringhomomorphism^-1%equiv).
  1: exact _.
  intros []; reflexivity. 
Defined.

Global Instance hasequivs_ring : HasEquivs Ring.
Proof.
  unshelve econstructor.
  + exact RingIsomorphism.
  + exact (fun G H f => IsEquiv f).
  + intros G H f; exact f.
  + exact Build_RingIsomorphism.
  + intros G H; exact rng_iso_inverse.
  + cbn; exact _.
  + reflexivity.
  + intros ????; apply eissect.
  + intros ????; apply eisretr.
  + intros G H f g p q.
    exact (isequiv_adjointify f g p q).
Defined.

(** ** Product ring *)

Definition ring_product : Ring -> Ring -> Ring.
Proof.
  intros R S.
  snrapply Build_Ring.
  1: exact (ab_biprod R S).
  1: exact (fun '(r1 , s1) '(r2 , s2) => (r1 * r2 , s1 * s2)).
  1: exact (ring_one , ring_one).
  { intros [r1 s1] [r2 s2] [r3 s3].
    apply path_prod; cbn; apply rng_dist_l. }
  { intros [r1 s1] [r2 s2] [r3 s3].
    apply path_prod; cbn; apply rng_dist_r. }
  repeat split.
  1: exact _.
  { intros [r1 s1] [r2 s2] [r3 s3].
    apply path_prod; cbn; apply rng_mult_assoc. }
  1: intros [r1 s1]; apply path_prod; cbn; apply rng_mult_one_l.
  1: intros [r1 s1]; apply path_prod; cbn; apply rng_mult_one_r.
Defined.

Infix "×" := ring_product : ring_scope.

Definition ring_product_fst {R S : Ring} : R × S $-> R.
Proof.
  snrapply Build_RingHomomorphism.
  1: exact fst.
  repeat split.
Defined.

Definition ring_product_snd {R S : Ring} : R × S $-> S.
Proof.
  snrapply Build_RingHomomorphism.
  1: exact snd.
  repeat split.
Defined.

Definition ring_product_corec (R S T : Ring)
  : (R $-> S) -> (R $-> T) -> (R $-> S × T).
Proof.
  intros f g.
  srapply Build_RingHomomorphism'.
  1: apply (ab_biprod_corec f g).
  repeat split.
  1: cbn; intros x y; apply path_prod; apply rng_homo_mult.
  cbn; apply path_prod; apply rng_homo_one.
Defined.

Definition equiv_ring_product_corec `{Funext} (R S T : Ring)
  : (R $-> S) * (R $-> T) <~> (R $-> S × T).
Proof.
  snrapply equiv_adjointify.
  1: exact (uncurry (ring_product_corec _ _ _)).
  { intros f.
    exact (ring_product_fst $o f, ring_product_snd $o f). }
  { hnf; intros f.
    by apply path_hom. }
  intros [f g].
  apply path_prod.
  1,2: by apply path_hom.
Defined.

Global Instance hasbinaryproducts_ring : HasBinaryProducts Ring.
Proof.
  intros R S.
  snrapply Build_BinaryProduct.
  - exact (R × S).
  - exact ring_product_fst.
  - exact ring_product_snd.
  - exact (fun T => ring_product_corec T R S).
  - cbn; reflexivity.
  - cbn; reflexivity.
  - intros T f g p q x.
    exact (path_prod' (p x) (q x)).
Defined.

(** ** Image ring *)

(** The image of a ring homomorphism *)
Definition rng_image {R S : Ring} (f : R $-> S) : Ring.
Proof.
  snrapply (Build_Ring (abgroup_image f)).
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
  all: repeat split.
  3: exact _.
  all: repeat intros [].
  all: apply path_sigma_hprop; cbn.
  1: apply distribute_l.
  1: apply distribute_r.
  1: apply associativity.
  1: apply left_identity.
  apply right_identity.
Defined.

Lemma rng_homo_image_incl {R S} (f : RingHomomorphism R S)
  : rng_image f $-> S.
Proof.
  snrapply Build_RingHomomorphism.
  1: exact pr1.
  repeat split.
Defined.

(** Image of a surjective ring homomorphism *)
Lemma rng_image_issurj {R S} (f : RingHomomorphism R S) {issurj : IsSurjection f}
  : rng_image f ≅ S.
Proof.
  snrapply Build_RingIsomorphism.
  1: exact (rng_homo_image_incl f).
  exact _.
Defined. 

(** ** Opposite Ring *)

(** Given a ring [R] we can reverse the order of the multiplication to get another ring [R^op]. *)
Definition rng_op : Ring -> Ring.
Proof.
  (** Let's carefully pull apart the ring structure and put it back together. Unfortunately, our definition of ring has some redundant data such as multiple hset assumptions, due to the mixing of algebraic strucutres. This isn't a problem in practice, but it does mean using typeclass inference here will pick up the wrong instance, therefore we carefully put it back together. See test/Algebra/Rings/Ring.v for a test checking this operation is definitionally involutive. *)
  intros [R mult one
    [is_abgroup [[monoid_ishset mult_assoc] li ri] ld rd]
    mult_assoc_opp].
  snrapply Build_Ring'.
  4: split.
  5: split.
  5: split.
  - exact R.
  - exact (flip mult).
  - exact one.
  - exact is_abgroup.
  - exact monoid_ishset.
  - exact (fun x y z => mult_assoc_opp z y x).
  - exact ri.
  - exact li.
  - exact (fun x y z => rd y z x).
  - exact (fun x y z => ld z x y).
  - exact (fun x y z => mult_assoc z y x).
Defined.

(** ** More Ring laws *)

(** Powers of ring elements *)
Definition rng_power {R : Ring} (x : R) (n : nat) : R := nat_iter n (x *.) ring_one.

(** Power laws *)
Lemma rng_power_mult_law {R : Ring} (x : R) (n m : nat)
  : (rng_power x n) * (rng_power x m) = rng_power x (n + m).
Proof.
  induction n as [|n IHn].
  1: apply rng_mult_one_l.
  refine ((rng_mult_assoc _ _ _)^ @ _).
  exact (ap (x *.) IHn).
Defined.
