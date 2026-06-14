From HoTT Require Import Basics Types.
From HoTT.WildCat Require Import Core.
Require Import Classes.interfaces.canonical_names.
Require Import Algebra.Groups.Group.
Require Import Algebra.AbGroups.AbelianGroup Algebra.AbGroups.AbHom
  Algebra.AbGroups.FreeAbelianGroup.
Require Import Algebra.Rings.Ring.

Local Open Scope mc_scope.
Local Open Scope mc_add_scope.

(** * The group ring [ℤG]

    Following Christensen and Flaten, Construction 2.7.1 and Proposition 2.7.2:
    the group ring of [G] is the free abelian group on [G] with multiplication
    extending the group operation, together with its universal property. *)

Section GroupRing.
  Context `{Funext} (G : Group).

  Definition group_ring_ab : AbGroup := FreeAbGroup G.

  Local Notation ZG := group_ring_ab.

  (** Multiplication, as a homomorphism into the endomorphism group. *)
  Definition group_ring_mult_hom : ZG $-> ab_hom ZG ZG
    := FreeAbGroup_rec (A := ab_hom ZG ZG)
         (fun g => FreeAbGroup_rec (A := ZG) (fun h => freeabgroup_in (sg_op g h))).

  Instance group_ring_mult : Mult ZG
    := fun x y => group_ring_mult_hom x y.

  Instance group_ring_one : One ZG := freeabgroup_in mon_unit.

  (** Generators multiply by the group operation. *)
  Definition group_ring_mult_in (g h : G)
    : (freeabgroup_in g * freeabgroup_in h : ZG) = freeabgroup_in (sg_op g h)
    := idpath.

  (** Evaluation at a point, as a homomorphism out of the endomorphism group. *)
  Definition group_ring_eval (y : ZG) : ab_hom ZG ZG $-> ZG.
  Proof.
    snapply Build_GroupHomomorphism.
    - exact (fun phi => phi y).
    - intros phi psi; reflexivity.
  Defined.

  Instance group_ring_left_distribute : LeftDistribute (A:=ZG) (.*.) (+).
  Proof.
    intros x y z; exact (grp_homo_op (group_ring_mult_hom x) y z).
  Defined.

  Instance group_ring_right_distribute : RightDistribute (A:=ZG) (.*.) (+).
  Proof.
    intros x y z.
    refine (ap (fun phi : ab_hom ZG ZG => phi z)
              (grp_homo_op group_ring_mult_hom x y) @ _).
    reflexivity.
  Defined.

  Instance group_ring_left_identity : LeftIdentity (A:=ZG) (.*.) 1.
  Proof.
    intro x.
    exact (FreeAbGroup_ind_homotopy
             (f := group_ring_mult_hom (freeabgroup_in mon_unit))
             (f' := grp_homo_id)
             (fun g => ap freeabgroup_in (left_identity g)) x).
  Defined.

  Instance group_ring_right_identity : RightIdentity (A:=ZG) (.*.) 1.
  Proof.
    intro x.
    exact (FreeAbGroup_ind_homotopy
             (f := group_ring_eval (freeabgroup_in mon_unit) $o group_ring_mult_hom)
             (f' := grp_homo_id)
             (fun g => ap freeabgroup_in (right_identity g)) x).
  Defined.

  (** Left multiplication by a fixed element, as a homomorphism. *)
  Definition group_ring_lmul (a : ZG) : ZG $-> ZG := group_ring_mult_hom a.

  (** Associativity on generators reduces to associativity in [G]. *)
  Definition group_ring_assoc_gen (g h k : G)
    : (freeabgroup_in g * (freeabgroup_in h * freeabgroup_in k) : ZG)
      = (freeabgroup_in g * freeabgroup_in h) * freeabgroup_in k.
  Proof.
    exact (ap freeabgroup_in (simple_associativity g h k)).
  Defined.

  Instance group_ring_associative : Associative (A:=ZG) (.*.).
  Proof.
    intros x y z.
    change ((group_ring_eval (y * z) $o group_ring_mult_hom) x
            = (group_ring_eval z $o (group_ring_mult_hom
                $o (group_ring_eval y $o group_ring_mult_hom))) x).
    revert x; rapply FreeAbGroup_ind_homotopy; intro g.
    change ((group_ring_lmul (freeabgroup_in g)
              $o (group_ring_eval z $o group_ring_mult_hom)) y
            = (group_ring_eval z $o (group_ring_mult_hom
                $o group_ring_lmul (freeabgroup_in g))) y).
    revert y; rapply FreeAbGroup_ind_homotopy; intro h.
    change ((group_ring_lmul (freeabgroup_in g)
              $o group_ring_lmul (freeabgroup_in h)) z
            = group_ring_lmul (freeabgroup_in g * freeabgroup_in h) z).
    revert z; rapply FreeAbGroup_ind_homotopy; intro k.
    exact (group_ring_assoc_gen g h k).
  Defined.

  Definition group_ring : Ring := Build_Ring ZG _ _ _ _ _ _ _.

  (** The universal property: a homomorphism from [G] to the units of a ring
      [R] extends to a ring homomorphism out of [ℤG]. *)
  Definition group_ring_rec (R : Ring)
    (psi : GroupHomomorphism G (rng_unit_group R))
    : RingHomomorphism group_ring R.
  Proof.
    pose (map := FreeAbGroup_rec (A := R) (fun g => (psi g).1)
                 : group_ring_ab $-> R).
    snapply (Build_RingHomomorphism' group_ring R map).
    snapply Build_IsMonoidPreserving.
    - intros x y.
      change ((grp_homo_compose map (group_ring_eval y $o group_ring_mult_hom)) x
              = grp_homo_compose (grp_homo_rng_right_mult (map y)) map x).
      revert x; rapply FreeAbGroup_ind_homotopy; intro g.
      change ((grp_homo_compose map (group_ring_lmul (freeabgroup_in g))) y
              = grp_homo_compose
                  (grp_homo_rng_left_mult (map (freeabgroup_in g))) map y).
      revert y; rapply FreeAbGroup_ind_homotopy; intro h.
      exact (ap pr1 (grp_homo_op psi g h)).
    - exact (ap pr1 (grp_homo_unit psi)).
  Defined.

  (** Conversely, a ring homomorphism out of [ℤG] restricts to a homomorphism
      from [G] to the units, since each generator is invertible. *)
  Definition group_ring_restrict (R : Ring)
    (phi : RingHomomorphism group_ring R)
    : GroupHomomorphism G (rng_unit_group R).
  Proof.
    snapply Build_GroupHomomorphism.
    - intro g.
      exists (phi (freeabgroup_in g)).
      rapply (Build_IsInvertible (phi (freeabgroup_in g))
                (phi (freeabgroup_in (inv g)))).
      + refine ((rng_homo_mult phi
                  (freeabgroup_in (inv g)) (freeabgroup_in g))^ @ _).
        refine (ap phi (group_ring_mult_in (inv g) g) @ _).
        refine (ap (fun u => phi (freeabgroup_in u)) (left_inverse g) @ _).
        exact (rng_homo_one phi).
      + refine ((rng_homo_mult phi
                  (freeabgroup_in g) (freeabgroup_in (inv g)))^ @ _).
        refine (ap phi (group_ring_mult_in g (inv g)) @ _).
        refine (ap (fun u => phi (freeabgroup_in u)) (right_inverse g) @ _).
        exact (rng_homo_one phi).
    - intros g g'.
      apply path_sigma_hprop; cbn.
      refine ((ap phi (group_ring_mult_in g g'))^ @ _).
      exact (rng_homo_mult phi (freeabgroup_in g) (freeabgroup_in g')).
  Defined.

  (** Ring homomorphisms out of [ℤG] correspond to homomorphisms from [G] to
      the units. *)
  Definition equiv_group_ring_rec (R : Ring)
    : RingHomomorphism group_ring R <~> GroupHomomorphism G (rng_unit_group R).
  Proof.
    snapply equiv_adjointify.
    - exact (group_ring_restrict R).
    - exact (group_ring_rec R).
    - intro psi.
      apply equiv_path_grouphomomorphism; intro g.
      by apply path_sigma_hprop.
    - intro phi.
      apply equiv_path_ringhomomorphism.
      intro x; revert x.
      rapply (FreeAbGroup_ind_homotopy
        (f := grp_homo_rng_homo (group_ring_rec R (group_ring_restrict R phi)))
        (f' := grp_homo_rng_homo phi)).
      intro g; reflexivity.
  Defined.

End GroupRing.
