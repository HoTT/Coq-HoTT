Require Import WildCat.
Require Import Spaces.Nat.Core Spaces.Nat.Arithmetic.
(* Some of the material in abstract_algebra and canonical names could be selectively exported to the user, as is done in Groups/Group.v. *)
Require Import Classes.interfaces.abstract_algebra.
Require Import Algebra.Groups.Group Algebra.Groups.Subgroup Algebra.Groups.Image.
Require Export Algebra.AbGroups.AbelianGroup Algebra.AbGroups.Biproduct Algebra.AbGroups.FiniteSum.

Require Export Classes.theory.rings.
Require Import Modalities.ReflectiveSubuniverse.

(** We make sure to treat [AbGroup] as if it has a [Plus], [Zero], and [Negate] operation from now on. *)
Export AbelianGroup.AdditiveInstances.

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
  ring_mult_assoc_opp : forall z y x, (x * y) * z = x * (y * z);
}.


Arguments ring_mult {R} : rename.
Arguments ring_one {R} : rename.
Arguments ring_isring {R} : rename.

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

  Context {A : Ring} (x y z : A).

  Definition rng_dist_l : x * (y + z) = x * y + x * z := simple_distribute_l _ _ _.
  Definition rng_dist_r : (x + y) * z = x * z + y * z := simple_distribute_r _ _ _.
  Definition rng_plus_zero_l : 0 + x = x := left_identity _.
  Definition rng_plus_zero_r : x + 0 = x := right_identity _.
  Definition rng_plus_negate_l : (- x) + x = 0 := left_inverse _.
  Definition rng_plus_negate_r : x + (- x) = 0 := right_inverse _.

  Definition rng_plus_comm : x + y = y + x := commutativity x y.
  Definition rng_plus_assoc : x + (y + z) = (x + y) + z := simple_associativity x y z.
  Definition rng_mult_assoc : x * (y * z) = (x * y) * z := simple_associativity x y z.

  Definition rng_negate_negate : - (- x) = x := groups.inverse_involutive _.
  Definition rng_negate_zero : - (0 : A) = 0 := groups.inverse_mon_unit.
  Definition rng_negate_plus : - (x + y) = - x - y := negate_plus_distr _ _.

  Definition rng_mult_one_l : 1 * x = x := left_identity _.
  Definition rng_mult_one_r : x * 1 = x := right_identity _.
  Definition rng_mult_zero_l : 0 * x = 0 := left_absorb _.
  Definition rng_mult_zero_r : x * 0 = 0 := right_absorb _.
  Definition rng_mult_negate : -1 * x = - x := (negate_mult_l _)^.
  Definition rng_mult_negate_negate : -x * -y = x * y := negate_mult_negate _ _.
  Definition rng_mult_negate_l : -x * y = -(x * y) := inverse (negate_mult_distr_l _ _).
  Definition rng_mult_negate_r : x * -y = -(x * y) := inverse (negate_mult_distr_r _ _).

End RingLaws.

Definition rng_dist_l_negate {A : Ring} (x y z : A)
  : x * (y - z) = x * y - x * z.
Proof.
  lhs nrapply rng_dist_l.
  nrapply ap.
  nrapply rng_mult_negate_r.
Defined.

Definition rng_dist_r_negate {A : Ring} (x y z : A)
  : (x - y) * z = x * z - y * z.
Proof.
  lhs nrapply rng_dist_r.
  nrapply ap.
  nrapply rng_mult_negate_l.
Defined.

Section RingHomoLaws.

  Context {A B : Ring} (f : RingHomomorphism A B) (x y : A).

  Definition rng_homo_plus : f (x + y) = f x + f y := preserves_plus x y.
  Definition rng_homo_mult : f (x * y) = f x * f y := preserves_mult x y.
  Definition rng_homo_zero : f 0 = 0 := preserves_0.
  Definition rng_homo_one  : f 1 = 1 := preserves_1.
  Definition rng_homo_negate : f (-x) = -(f x) := preserves_negate x.

  Definition rng_homo_minus_one : f (-1) = -1
    := preserves_negate _ @ ap negate preserves_1.

End RingHomoLaws.

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
      (Build_IsSemiRingPreserving _ (ismonoidpreserving_grp_homo map) H).

(** We can construct a ring isomorphism from a group isomorphism that preserves multiplication *)
Definition Build_RingIsomorphism'' (A B : Ring) (e : GroupIsomorphism A B)
  {H : IsMonoidPreserving (Aop:=ring_mult) (Bop:=ring_mult) (Aunit:=one) (Bunit:=one) e}
  : RingIsomorphism A B
  := @Build_RingIsomorphism' A B e (Build_IsSemiRingPreserving e _ H).

(** Here is an alternative way to build a ring using the underlying abelian group. *)
Definition Build_Ring (R : AbGroup)
  `(Mult R, One R, !Associative (.*.),
    !LeftDistribute (.*.) (+), !RightDistribute (.*.) (+),
    !LeftIdentity (.*.) 1, !RightIdentity (.*.) 1)
  : Ring.
Proof.
  rapply (Build_Ring' R).
  2: exact (fun z y x => (associativity x y z)^).
  split; only 1,3,4: exact _.
  repeat split; exact _.
Defined.

(** Scalar multiplication on the left is a group homomorphism. *)
Definition grp_homo_rng_left_mult {R : Ring} (r : R)
  : GroupHomomorphism R R
  := @Build_GroupHomomorphism R R (fun s => r * s) (rng_dist_l r).

(** Scalar multiplication on the right is a group homomorphism. *)
Definition grp_homo_rng_right_mult {R : Ring} (r : R)
  : GroupHomomorphism R R
  := @Build_GroupHomomorphism R R (fun s => s * r) (fun x y => rng_dist_r x y r).

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

(** ** Subrings *)

(** TODO: factor out this definition as a submonoid *)
(** A subring is a subgorup of the underlying abelian group of a ring that is closed under multiplication and contains [1]. *)
Class IsSubring {R : Ring} (S : R -> Type) := {
  issubring_issubgroup :: IsSubgroup S;
  issubring_mult {x y} : S x -> S y -> S (x * y);
  issubring_one : S 1;
}.

Definition issig_IsSubring {R : Ring} (S : R -> Type)
  : _ <~> IsSubring S
  := ltac:(issig).

Global Instance ishprop_issubring `{Funext} {R : Ring} (S : R -> Type)
  : IsHProp (IsSubring S).
Proof.
  exact (istrunc_equiv_istrunc _ (issig_IsSubring S)).
Defined.

(** Subring criterion. *)
Definition Build_IsSubring' {R : Ring} (S : R -> Type)
  (H : forall x, IsHProp (S x))
  (H1 : forall x y, S x -> S y -> S (x - y))
  (H2 : forall x y, S x -> S y -> S (x * y))
  (H3 : S 1)
  : IsSubring S.
Proof.
  snrapply Build_IsSubring.
  - snrapply Build_IsSubgroup'.
    + exact _.
    + pose (p := H1 1 1 H3 H3).
      rewrite rng_plus_negate_r in p.
      exact p.
    + exact H1.
  - exact H2.
  - exact H3.
Defined.

Record Subring (R : Ring) := {
  #[reversible=no]
  subring_pred :> R -> Type;
  subring_issubring :: IsSubring subring_pred;
}.

Definition Build_Subring'' {R : Ring} (S : Subgroup R)
  (H1 : forall x y, S x -> S y -> S (x * y))
  (H2 : S 1)
  : Subring R.
Proof.
  snrapply (Build_Subring _ S).
  snrapply Build_IsSubring.
  - exact _.
  - exact H1.
  - exact H2.
Defined.

Definition Build_Subring' {R : Ring} (S : R -> Type)
  (H : forall x, IsHProp (S x))
  (H1 : forall x y, S x -> S y -> S (x - y))
  (H2 : forall x y, S x -> S y -> S (x * y))
  (H3 : S 1)
  : Subring R
  := Build_Subring R S (Build_IsSubring' S H H1 H2 H3).

(** The underlying subgroup of a subring. *)
Coercion subgroup_subring {R} : Subring R -> Subgroup R
  := fun S => Build_Subgroup R S _.

(** The ring given by a subring. *)
Coercion ring_subring {R : Ring} (S : Subring R) : Ring.
Proof.
  snrapply (Build_Ring (subgroup_subring S)).
  3-7: hnf; intros; srapply path_sigma_hprop.
  - intros [r ?] [s ?]; exists (r * s).
    by apply issubring_mult.
  - exists 1.
    apply issubring_one.
  - snrapply rng_mult_assoc.
  - snrapply rng_dist_l.
  - snrapply rng_dist_r.
  - snrapply rng_mult_one_l.
  - snrapply rng_mult_one_r.
Defined.

(** ** Product ring *)

Definition ring_product : Ring -> Ring -> Ring.
Proof.
  intros R S.
  snrapply Build_Ring.
  - exact (ab_biprod R S).
  - exact (fun '(r1 , s1) '(r2 , s2) => (r1 * r2 , s1 * s2)).
  - exact (ring_one , ring_one).
  - intros [r1 s1] [r2 s2] [r3 s3].
    apply path_prod; cbn; apply rng_mult_assoc.
  - intros [r1 s1] [r2 s2] [r3 s3].
    apply path_prod; cbn; apply rng_dist_l.
  - intros [r1 s1] [r2 s2] [r3 s3].
    apply path_prod; cbn; apply rng_dist_r.
  - intros [r1 s1]; apply path_prod; cbn; apply rng_mult_one_l.
  - intros [r1 s1]; apply path_prod; cbn; apply rng_mult_one_r.
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
Definition rng_image {R S : Ring} (f : R $-> S) : Subring S.
Proof.
  snrapply (Build_Subring'' (grp_image f)).
  - simpl.
    intros x y p q.
    strip_truncations; apply tr.
    destruct p as [a p'], q as [b q'].
    exists (a * b).
    refine (rng_homo_mult _ _ _ @ _).
    f_ap.
  - apply tr.
    exists 1.
    exact (rng_homo_one f).
Defined.

Lemma rng_homo_image_incl {R S} (f : RingHomomorphism R S)
  : (rng_image f : Ring) $-> S.
Proof.
  snrapply Build_RingHomomorphism.
  1: exact pr1.
  repeat split.
Defined.

(** Image of a surjective ring homomorphism *)
Lemma rng_image_issurj {R S} (f : RingHomomorphism R S) {issurj : IsSurjection f}
  : (rng_image f : Ring) ≅ S.
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
  - exact (fun x y => mult y x).
  - exact one.
  - exact is_abgroup.
  - exact monoid_ishset.
  - exact mult_assoc_opp.
  - exact ri.
  - exact li.
  - exact (fun x y z => rd y z x).
  - exact (fun x y z => ld z x y).
  - exact mult_assoc.
Defined.

(** The opposite ring is a functor. *)
Global Instance is0functor_rng_op : Is0Functor rng_op.
Proof.
  snrapply Build_Is0Functor.
  intros R S f.
  snrapply Build_RingHomomorphism'.
  - exact f.
  - split.
    + exact (fun x y => rng_homo_mult f y x).
    + exact (rng_homo_one f).
Defined.

Global Instance is1functor_rng_op : Is1Functor rng_op.
Proof.
  snrapply Build_Is1Functor.
  - intros R S f g p.
    exact p.
  - intros R; cbn; reflexivity.
  - intros R S T f g; cbn; reflexivity.
Defined.

(** ** Powers *)

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

(** ** Finite Sums *)

(** Ring multiplication distributes over finite sums on the left. *)
Definition rng_sum_dist_l {R : Ring} (n : nat) (f : forall k, (k < n)%nat -> R) (r : R)
  : r * ab_sum n f = ab_sum n (fun k Hk => r * f k Hk).
Proof.
  induction n as [|n IHn].
  1: apply rng_mult_zero_r.
  lhs nrapply rng_dist_l; simpl; f_ap.
Defined.

(** Ring multiplication distributes over finite sums on the right. *)
Definition rng_sum_dist_r {R : Ring} (n : nat) (f : forall k, (k < n)%nat -> R) (r : R)
  : ab_sum n f * r = ab_sum n (fun k Hk => f k Hk * r).
Proof.
  induction n as [|n IHn].
  1: apply rng_mult_zero_l.
  lhs nrapply rng_dist_r; simpl; f_ap.
Defined.

(** ** Invertible elements *)

(** An element [x] of a ring [R] is left invertible if there exists an element [y] such that [y * x = 1]. *)
Class IsLeftInvertible (R : Ring) (x : R) := {
  left_inverse_elem : R;
  left_inverse_eq : left_inverse_elem * x = 1;
}.

Arguments left_inverse_elem {R} x {_}.
Arguments left_inverse_eq {R} x {_}.

Definition issig_IsLeftInvertible {R : Ring} (x : R)
  : _ <~> IsLeftInvertible R x
  := ltac:(issig).

(** An element [x] of a ring [R] is right invertible if there exists an element [y] such that [x * y = 1]. We state this as a left invertible element of the opposite ring. *)
Class IsRightInvertible (R : Ring) (x : R)
  := isleftinvertible_rng_op :: IsLeftInvertible (rng_op R) x.

Definition right_inverse_elem {R} x `{!IsRightInvertible R x} : R
  := left_inverse_elem (R:=rng_op R) x.

Definition right_inverse_eq {R} x `{!IsRightInvertible R x}
  : x * right_inverse_elem x = 1
  := left_inverse_eq (R:=rng_op R) x.

(** An element [x] of a ring [R] is invertible if it is both left and right invertible. *)
Class IsInvertible (R : Ring) (x : R) := Build_IsInvertible' {
  isleftinvertible_isinvertible :: IsLeftInvertible R x;
  isrightinvertible_isinvertible :: IsRightInvertible R x;
}.

(** We can show an element is invertible by providing an inverse element which is a left and right inverse similtaneously. We will later show that the two inverses of an invertible element must be equal anyway. *)
Definition Build_IsInvertible {R : Ring} (x : R)
  (inv : R) (inv_l : inv * x = 1) (inv_r : x * inv = 1)
  : IsInvertible R x.
Proof.
  split.
  - by exists inv.
  - unfold IsRightInvertible.
    by exists (inv : rng_op R).
Defined.

(** The invertible elements in [R] and [rng_op R] agree, by swapping the proofs of left and right invertibility. *)
Definition isinvertible_rng_op (R : Ring) (x : R) `{!IsInvertible R x}
  : IsInvertible (rng_op R) x.
Proof.
  split.
  - exact (isrightinvertible_isinvertible).
  - exact (isleftinvertible_isinvertible).
Defined.

(** *** Uniqueness of inverses *)

(** This general lemma will be used for uniqueness results. *)
Definition path_left_right_inverse {R : Ring} (x x' x'' : R)
  (p : x' * x = 1) (q : x * x'' = 1)
  : x' = x''.
Proof.
  rhs_V nrapply rng_mult_one_l.
  rewrite <- p. 
  rewrite <- simple_associativity.
  rewrite q.
  symmetry.
  apply rng_mult_one_r.
Defined.

(** The left and right inverse of an invertible element are necessarily equal. *)
Definition path_left_inverse_elem_right_inverse_elem
  {R : Ring} x `{!IsInvertible R x}
  : left_inverse_elem x = right_inverse_elem x.
Proof.
  nrapply (path_left_right_inverse x).
  - apply left_inverse_eq.
  - apply right_inverse_eq.
Defined.

(** It is therefore well-defined to talk about the inverse of an invertible element. *)
Definition inverse_elem {R : Ring} (x : R) `{IsInvertible R x} : R
  := left_inverse_elem x.

(** Left cancellation for an invertible element. *)
Definition rng_inv_l {R : Ring} (x : R) `{IsInvertible R x}
  : inverse_elem x * x = 1.
Proof.
  apply left_inverse_eq.
Defined.

(** Right cancellation for an invertible element. *)
Definition rng_inv_r {R : Ring} (x : R) `{IsInvertible R x}
  : x * inverse_elem x = 1.
Proof.
  rhs_V nrapply (right_inverse_eq x).
  f_ap.
  apply path_left_inverse_elem_right_inverse_elem.
Defined.

(** Equal elements have equal inverses.  Note that we don't require that the proofs of invertibility are equal (over [p]).  It follows that the inverse of an invertible element [x] depends only on [x]. *)
Definition isinvertible_unique {R : Ring} (x y : R) `{IsInvertible R x} `{IsInvertible R y} (p : x = y)
  : inverse_elem x = inverse_elem y.
Proof.
  destruct p.
  snrapply (path_left_right_inverse x).
  - apply rng_inv_l.
  - apply rng_inv_r.
Defined.

(** We can show that being invertible is equivalent to having an inverse element that is simultaneously a left and right inverse. *)
Definition equiv_isinvertible_left_right_inverse {R : Ring} (x : R)
  : {inv : R & prod (inv * x = 1) (x * inv = 1)} <~> IsInvertible R x.
Proof.
  equiv_via { i : IsInvertible R x & right_inverse_elem x = left_inverse_elem x }.
  1: make_equiv_contr_basedpaths.
  apply equiv_sigma_contr; intro i.
  rapply contr_inhabited_hprop.
  symmetry; apply path_left_inverse_elem_right_inverse_elem.
Defined.

(** Being invertible is a proposition. *)
Global Instance ishprop_isinvertible {R x} : IsHProp (IsInvertible R x).
Proof.
  nrapply (istrunc_equiv_istrunc _ (equiv_isinvertible_left_right_inverse x)).
  snrapply hprop_allpath; intros [y [p1 p2]] [z [q1 q2]].
  rapply path_sigma_hprop; cbn.
  exact (path_left_right_inverse x y z p1 q2).
Defined.

(** *** Closure of invertible elements under multiplication *)

(** Left invertible elements are closed under multiplication. *)
Global Instance isleftinvertible_mult {R : Ring} (x y : R)
  : IsLeftInvertible R x -> IsLeftInvertible R y -> IsLeftInvertible R (x * y).
Proof.
  intros [x' p] [y' q].
  exists (y' * x').
  rhs_V nrapply q.
  lhs nrapply rng_mult_assoc.
  f_ap.
  rhs_V nrapply rng_mult_one_r.
  lhs_V nrapply rng_mult_assoc.
  f_ap.
Defined.

(** Right invertible elements are closed under multiplication. *)
Global Instance isrightinvertible_mult {R : Ring} (x y : R)
  : IsRightInvertible R x -> IsRightInvertible R y -> IsRightInvertible R (x * y).
Proof.
  change (x * y) with (ring_mult (R:=rng_op R) y x).
  unfold IsRightInvertible.
  exact _.
Defined.

(** Invertible elements are closed under multiplication. *)
Global Instance isinvertible_mult {R : Ring} (x y : R)
  : IsInvertible R x -> IsInvertible R y -> IsInvertible R (x * y)
  := {}.

(** Left invertible elements are closed under negation. *)
Global Instance isleftinvertible_neg {R : Ring} (x : R)
  : IsLeftInvertible R x -> IsLeftInvertible R (-x).
Proof.
  intros H.
  exists (- left_inverse_elem x).
  lhs nrapply rng_mult_negate_negate.
  apply left_inverse_eq.
Defined.

(** Right invertible elements are closed under negation. *)
Global Instance isrightinvertible_neg {R : Ring} (x : R)
  : IsRightInvertible R x -> IsRightInvertible R (-x).
Proof.
  intros H.
  rapply isleftinvertible_neg.
Defined.

(** Invertible elements are closed under negation. *)
Global Instance isinvertible_neg {R : Ring} (x : R)
  : IsInvertible R x -> IsInvertible R (-x)
  := {}.

(** Inverses of left invertible elements are themselves right invertible. *)
Global Instance isrightinvertible_left_inverse_elem {R : Ring} (x : R)
  `{IsLeftInvertible R x}
  : IsRightInvertible R (left_inverse_elem x).
Proof.
  exists (x : rng_op R).
  exact (left_inverse_eq x).
Defined.

(** Inverses of right invertible elements are themselves left invertible. *)
Global Instance isleftinvertible_right_inverse_elem {R : Ring} (x : R)
  `{IsRightInvertible R x}
  : IsLeftInvertible R (right_inverse_elem x).
Proof.
  exists x.
  exact (right_inverse_eq x).
Defined.

(** Inverses of invertible elements are themselves invertible.  We take both inverses of [inverse_elem x] to be [x]. *)
Global Instance isinvertible_inverse_elem {R : Ring} (x : R)
  `{IsInvertible R x}
  : IsInvertible R (inverse_elem x).
Proof.
  split.
  - exists x; apply rng_inv_r.
  - apply isrightinvertible_left_inverse_elem.
Defined.

(** Since [inverse_elem (inverse_elem x) = x], we get the following equivalence. *)
Definition equiv_path_inverse_elem {R : Ring} {x y : R}
  `{IsInvertible R x, IsInvertible R y}
  : x = y <~> inverse_elem x = inverse_elem y.
Proof.
  srapply equiv_iff_hprop.
  - exact (isinvertible_unique x y).
  - exact (isinvertible_unique (inverse_elem x) (inverse_elem y)).
Defined.

(** [1] is always invertible, and by the above [-1]. *)
Global Instance isinvertible_one {R} : IsInvertible R 1.
Proof.
  snrapply Build_IsInvertible.
  - exact one.
  - apply rng_mult_one_l.
  - apply rng_mult_one_l.
Defined.

(** Ring homomorphisms preserve invertible elements. *)
Global Instance isinvertible_rng_homo {R S} (f : R $-> S)
  : forall x, IsInvertible R x -> IsInvertible S (f x).
Proof.
  intros x H.
  snrapply Build_IsInvertible.
  1: exact (f (inverse_elem x)).
  1,2: lhs_V nrapply rng_homo_mult.
  1,2: rhs_V nrapply (rng_homo_one f).
  1,2: nrapply (ap f).
  - exact (rng_inv_l x).
  - exact (rng_inv_r x).
Defined.

(** *** Group of units *)

(** Invertible elements are typically called "units" in ring theory and the collection of units forms a group under the ring multiplication. *)
Definition rng_unit_group (R : Ring) : Group.
Proof.
  (** TODO: Use a generalised version of [Build_Subgroup] that works for subgroups of monoids. *)
  snrapply Build_Group.
  - exact {x : R & IsInvertible R x}.
  - intros [x p] [y q].
    exists (x * y).
    exact _.
  - exists 1.
    exact _.
  - intros [x p].
    exists (inverse_elem x).
    exact _.
  - repeat split.
    1: exact _.
    1-5: hnf; intros; apply path_sigma_hprop.
    + rapply simple_associativity.
    + rapply left_identity.
    + rapply right_identity.
    + apply rng_inv_l.
    + apply rng_inv_r.
Defined.

(** *** Multiplication by an invertible element is an equivalence *)

Global Instance isequiv_rng_inv_mult_l {R : Ring} {x : R}
  `{IsInvertible R x}
  : IsEquiv (x *.).
Proof.
  snrapply isequiv_adjointify.
  1: exact (inverse_elem x *.).
  1,2: intros y.
  1,2: lhs nrapply rng_mult_assoc.
  1,2: rhs_V nrapply rng_mult_one_l.
  1,2: snrapply (ap (.* y)).
  - nrapply rng_inv_r.
  - nrapply rng_inv_l.
Defined.

(** This can be proved by combining [isequiv_rng_inv_mult_l (R:=rng_op R)] with [isinvertible_rng_op], but then the inverse map is given by multiplying by [right_inverse_elem x] not [inverse_elem x], which complicates calculations. *)
Global Instance isequiv_rng_inv_mult_r {R : Ring} {x : R}
  `{IsInvertible R x}
  : IsEquiv (.* x).
Proof.
  snrapply isequiv_adjointify.
  1: exact (.* inverse_elem x).
  1,2: intros y.
  1,2: lhs_V nrapply rng_mult_assoc.
  1,2: rhs_V nrapply rng_mult_one_r.
  1,2: snrapply (ap (y *.)).
  - nrapply rng_inv_l.
  - nrapply rng_inv_r.
Defined.

(** *** Invertible element movement lemmas *)

(** These cannot be proven using the corresponding group laws in the group of units since not all elements involved are invertible. *)

Definition rng_inv_moveL_Vr {R : Ring} {x y z : R} `{IsInvertible R y}
  : y * x = z <~> x = inverse_elem y * z
  := equiv_moveL_equiv_V (f := (y *.)) z x.

Definition rng_inv_moveL_rV {R : Ring} {x y z : R} `{IsInvertible R y}
  : x * y = z <~> x = z * inverse_elem y
  := equiv_moveL_equiv_V (f := (.* y)) z x.

Definition rng_inv_moveR_Vr {R : Ring} {x y z : R} `{IsInvertible R y}
  : x = y * z <~> inverse_elem y * x = z
  := equiv_moveR_equiv_V (f := (y *.)) x z.

Definition rng_inv_moveR_rV {R : Ring} {x y z : R} `{IsInvertible R y}
  : x = z * y <~> x * inverse_elem y = z
  := equiv_moveR_equiv_V (f := (.* y)) x z.

(** TODO: The group of units construction is a functor from [Ring -> Group] and is right adjoint to the group ring construction. *)
