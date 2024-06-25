Require Import Classes.interfaces.canonical_names.
Require Import Algebra.AbGroups.
Require Import Algebra.Rings.CRing.
Require Import Algebra.Rings.Module.
Require Import Spaces.BinInt Spaces.Pos.
Require Import WildCat.Core.

(** In this file we define the ring Z of integers. The underlying abelian group is already defined in Algebra.AbGroups.Z. Many of the ring axioms are proven and made opaque. Typically, everything inside IsCRing can be opaque since we will only ever rewrite along them and they are hprops. This also means we don't have to be too careful with how our proofs are structured. This allows us to freely use tactics such as rewrite. It would perhaps be possible to shorten many of the proofs here, but it would probably be unneeded due to the opacicty. *)

(** The ring of integers *)
Definition cring_Z : CRing.
Proof.
  snrapply Build_CRing'.
  - exact abgroup_Z.
  - exact 1%binint.
  - exact binint_mul.
  - exact binint_mul_comm.
  - exact binint_mul_add_distr_l.
  - split.
    + split.
      * exact _.
      * exact binint_mul_assoc.
    + exact binint_mul_1_l.
    + exact binint_mul_1_r.
Defined.

Local Open Scope mc_scope.

(** Multiplication of a ring element by an integer. *)
(** We call this a "catamorphism" which is the name of the map from an initial object. It seems to be a more common terminology in computer science. *)
Definition cring_catamorphism_fun (R : CRing) (z : cring_Z) : R
  := match z with
     | neg z => pos_peano_rec R (-1) (fun n nr => -1 + nr) z
     | 0%binint => 0
     | pos z => pos_peano_rec R 1 (fun n nr => 1 + nr) z
     end.

(** TODO: remove these (they will be cleaned up in the future)*)
(** Left multiplication is an equivalence *)
Local Instance isequiv_group_left_op {G} `{IsGroup G}
  : forall (x : G), IsEquiv (fun t => sg_op x t).
Proof.
  intro x.
  srapply isequiv_adjointify.
  1: exact (sg_op (-x)).
  all: intro y.
  all: refine (associativity _ _ _ @ _ @ left_identity y).
  all: refine (ap (fun x => x * y) _).
  1: apply right_inverse.
  apply left_inverse.
Defined.

(** Right multiplication is an equivalence *)
Local Instance isequiv_group_right_op {G} `{IsGroup G}
  : forall x:G, IsEquiv (fun y => sg_op y x).
Proof.
  intro x.
  srapply isequiv_adjointify.
  1: exact (fun y => sg_op y (- x)).
  all: intro y.
  all: refine ((associativity _ _ _)^ @ _ @ right_identity y).
  all: refine (ap (y *.) _).
  1: apply left_inverse.
  apply right_inverse.
Defined.

(** Preservation of + *)
Global Instance issemigrouppreserving_cring_catamorphism_fun_plus (R : CRing)
  : IsSemiGroupPreserving (Aop:=cring_plus) (Bop:=cring_plus)
      (cring_catamorphism_fun R : cring_Z -> R).
Proof.
  (** Unfortunately, due to how we have defined things we need to seperate this out into 9 cases. *)
  hnf. intros [x| |x] [y| |y].
  (** Some of these cases are easy however *)
  2,5,8: cbn; by rewrite right_identity.
  3,4: symmetry; apply left_identity.
  (** This leaves us with four cases to consider *)
  (** x < 0 , y < 0 *)
  { change (cring_catamorphism_fun R ((neg x) + (neg y))%binint
      = (cring_catamorphism_fun R (neg x)) + (cring_catamorphism_fun R (neg y))).
    induction y as [|y IHy] using pos_peano_ind.
    { simpl.
      rewrite pos_add_1_r.
      rewrite pos_peano_rec_beta_pos_succ.
      apply commutativity. }
    simpl.
    rewrite pos_add_succ_r.
    rewrite 2 pos_peano_rec_beta_pos_succ.
    rewrite simple_associativity.
    rewrite (commutativity _ (-1)).
    rewrite <- simple_associativity.
    f_ap. }
  (** x < 0 , y > 0 *)
  { cbn.
    revert x.
    induction y as [|y IHy] using pos_peano_ind; intro x.
    { cbn.
      induction x as [|x] using pos_peano_ind.
      1: symmetry; cbn; apply left_inverse.
      rewrite pos_peano_rec_beta_pos_succ.
      rewrite binint_pos_sub_succ_r.
      cbn; rewrite <- simple_associativity.
      apply (rng_moveL_Vr (R:=R)).
      apply commutativity. }
    induction x as [|x IHx] using pos_peano_ind.
    { rewrite binint_pos_sub_succ_l.
      cbn; apply (rng_moveL_Vr (R:=R)).
      by rewrite pos_peano_rec_beta_pos_succ. }
    rewrite binint_pos_sub_succ_succ.
    rewrite IHy.
    rewrite 2 pos_peano_rec_beta_pos_succ.
    rewrite (commutativity (-1)).
    rewrite simple_associativity.
    rewrite <- (simple_associativity _ _ 1).
    rewrite left_inverse.
    f_ap.
    symmetry.
    apply right_identity. }
  - cbn.
    revert x.
    induction y as [|y IHy] using pos_peano_ind; intro x.
    { induction x as [|x] using pos_peano_ind.
      1: symmetry; cbn; apply right_inverse.
      rewrite pos_peano_rec_beta_pos_succ.
      rewrite (commutativity 1).
      rewrite <- simple_associativity.
      rewrite binint_pos_sub_succ_l.
      cbn; by rewrite right_inverse, right_identity. }
    induction x as [|x IHx] using pos_peano_ind.
    { rewrite binint_pos_sub_succ_r.
      rewrite pos_peano_rec_beta_pos_succ.
      rewrite simple_associativity.
      cbn.
      rewrite (right_inverse 1).
      symmetry.
      apply left_identity. }
    rewrite binint_pos_sub_succ_succ.
    rewrite IHy.
    rewrite 2 pos_peano_rec_beta_pos_succ.
    rewrite (commutativity 1).
    rewrite simple_associativity.
    rewrite <- (simple_associativity _ _ (-1)).
    rewrite (right_inverse 1).
    f_ap; symmetry.
    apply right_identity.
  - cbn.
    induction y as [|y IHy] using pos_peano_ind.
    { cbn.
      rewrite pos_add_1_r.
      rewrite pos_peano_rec_beta_pos_succ.
      apply commutativity. }
    rewrite pos_add_succ_r.
    rewrite 2 pos_peano_rec_beta_pos_succ.
    rewrite simple_associativity.
    rewrite IHy.
    rewrite simple_associativity.
    rewrite (commutativity 1).
    reflexivity.
Qed.

Lemma cring_catamorphism_fun_negate {R} x
  : cring_catamorphism_fun R (- x) = - cring_catamorphism_fun R x.
Proof.
  snrapply (groups.preserves_negate _).
  1-6: typeclasses eauto.
  snrapply Build_IsMonoidPreserving.
  1: exact _.
  split.
Defined.

Lemma cring_catamorphism_fun_pos_mult {R} x y
  : cring_catamorphism_fun R (pos x * pos y)%binint
    = cring_catamorphism_fun R (pos x) * cring_catamorphism_fun R (pos y).
Proof.
  revert y.
  induction x as [|x IHx] using pos_peano_ind; intro y.
  { symmetry.
    apply left_identity. }
  change (cring_catamorphism_fun R (pos (pos_succ x * y)%pos)
    = cring_catamorphism_fun R (pos (pos_succ x)) * cring_catamorphism_fun R (pos y)).
  rewrite pos_mul_succ_l.
  refine (issemigrouppreserving_cring_catamorphism_fun_plus
    R (pos (x * y)%pos) (pos y) @ _).
  rewrite IHx.
  transitivity ((1 + cring_catamorphism_fun R (pos x)) * cring_catamorphism_fun R (pos y)).
  2: simpl; by rewrite pos_peano_rec_beta_pos_succ.
  rewrite (rng_dist_r (A:=R)).
  rewrite rng_mult_one_l.
  apply commutativity.
Qed.

(** Preservation of * (multiplication) *)
Global Instance issemigrouppreserving_cring_catamorphism_fun_mult (R : CRing)
  : IsSemiGroupPreserving (Aop:=(.*.)) (Bop:=(.*.))
      (cring_catamorphism_fun R : cring_Z -> R).
Proof.
  hnf. intros [x| |x] [y| |y].
  2,5,8: symmetry; apply (rng_mult_zero_r (A:=R)).
  3,4: cbn; symmetry; rewrite (commutativity 0); apply (rng_mult_zero_r (A:=R)).
  { change (cring_catamorphism_fun R (pos (x * y)%pos)
      = cring_catamorphism_fun R (- (pos x : cring_Z))
        * cring_catamorphism_fun R (- (pos y : cring_Z))).
    by rewrite 2 cring_catamorphism_fun_negate, cring_catamorphism_fun_pos_mult,
      (rng_mult_negate_negate (A:=R)). }
  { change (cring_catamorphism_fun R (- (pos (x * y)%pos : cring_Z))
      = cring_catamorphism_fun R (- (pos x : cring_Z))
        * cring_catamorphism_fun R (pos y)).
    by rewrite 2 cring_catamorphism_fun_negate, cring_catamorphism_fun_pos_mult,
      (rng_mult_negate_l (A:=R)). }
  { change (cring_catamorphism_fun R (- (pos (x * y)%pos : cring_Z))
      = cring_catamorphism_fun R (pos x)
        * cring_catamorphism_fun R (- (pos y : cring_Z))).
    by rewrite 2 cring_catamorphism_fun_negate, cring_catamorphism_fun_pos_mult,
      (rng_mult_negate_r (A:=R)). }
  apply cring_catamorphism_fun_pos_mult.
Qed.

(** This is a ring homomorphism *)
Definition rng_homo_int (R : CRing) : cring_Z $-> R.
Proof.
  snrapply Build_RingHomomorphism.
  1: exact (cring_catamorphism_fun R).
  repeat split; exact _.
Defined.

(** The integers are the initial commutative ring *)
Global Instance isinitial_cring_Z : IsInitial cring_Z.
Proof.
  unfold IsInitial.
  intro R.
  exists (rng_homo_int R).
  intros g x.
  destruct x as [n| |p].
  + induction n using pos_peano_ind.
    { cbn. symmetry; rapply (rng_homo_minus_one (B:=R)). }
    simpl.
    rewrite pos_peano_rec_beta_pos_succ.
    rewrite binint_neg_pos_succ.
    unfold binint_pred.
    rewrite binint_add_comm.
    rewrite rng_homo_plus.
    rewrite rng_homo_minus_one.
    apply ap.
    exact IHn.
  + by rewrite 2 rng_homo_zero.
  + induction p using pos_peano_ind.
    { cbn. symmetry; rapply (rng_homo_one g). }
    simpl.
    rewrite pos_peano_rec_beta_pos_succ.
    rewrite binint_pos_pos_succ.
    unfold binint_succ.
    rewrite binint_add_comm.
    rewrite rng_homo_plus.
    rewrite rng_homo_one.
    apply ap.
    exact IHp.
Defined.

Section Lm_carrierIsEquiv.

  (** lm_carrier is a 1-functor (LeftModule R) ->  AbGroup. *)
  Global Instance lm_carrieris0fun {R} : Is0Functor (lm_carrier R).
  Proof.
    snrapply Build_Is0Functor.
    intros a b f.
    destruct f.
    exact lm_homo_map.
  Defined.

  Global Instance lm_carrieris1fun {R} : Is1Functor (lm_carrier R).
  Proof.
    snrapply Build_Is1Functor.
    - intros a b f g e. assumption.
    - reflexivity.
    - reflexivity.
  Defined.
  (* I think the above should be moved to Module.v, as it is not specifically a property of the integers. *)

  (** Every abelian group admits a canonical left Z-module structure. *)
  Definition can_Z : AbGroup -> (LeftModule cring_Z).
  Proof.
    intros A. snrapply Build_LeftModule.
    - assumption.
    - snrapply (Build_IsLeftModule _).
      + intros n a. exact (ab_mul n a).
      + unfold LeftHeteroDistribute. intros n. exact preserves_sg_op.
      + unfold RightHeteroDistribute. intros m n a. destruct m, n; simpl.
        -- 
        (* This might be the wrong way to do this. On this path I need to prove that grp_pow respects addition of natural numbers. *)
  Admitted.

End Lm_carrierIsEquiv.