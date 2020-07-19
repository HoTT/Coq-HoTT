Require Import Basics.
Require Import Types.
Require Import Cubical.
Require Import Homotopy.Suspension.
Require Import Homotopy.HSpace.
Require Import Spaces.Spheres.

(** H-space structure on circle. *)

Section HSpace_S1.

  Context `{Univalence}.

  Definition Sph1_ind (P : Sphere 1 -> Type) (b : P North)
    (p : DPath P (merid North @ (merid South)^) b b)
    : forall x : Sphere 1, P x.
  Proof.
    srapply Susp_ind.
    1: exact b.
    1: exact (merid South # b).
    srapply Susp_ind; hnf.
    { apply moveL_transport_p.
      refine ((transport_pp _ _ _ _)^ @ _).
      apply dp_path_transport^-1.
      apply p. }
    1: reflexivity.
    apply Empty_ind.
  Defined.

  Definition Sph1_rec (P : Type) (b : P) (p : b = b)
    : Sphere 1 -> P.
  Proof.
    srapply Susp_rec.
    1,2: exact b.
    simpl.
    srapply Susp_rec.
    1: exact p.
    1: reflexivity.
    apply Empty_rec.
  Defined.

  Definition Sph1_rec_beta_loop (P : Type) (b : P) (p : b = b)
    : ap (Sph1_rec P b p) (merid North @ (merid South)^) = p.
  Proof.
    rewrite ap_pp.
    rewrite ap_V.
    rewrite 2 Susp_rec_beta_merid.
    apply concat_p1.
  Defined.

  Definition s1_turn : forall x : Sphere 1, x = x.
  Proof.
    srapply Sph1_ind.
    + exact (merid North @ (merid South)^).
    + apply dp_paths_lr.
      by rewrite concat_Vp, concat_1p.
  Defined.

  Global Instance sgop_s1 : SgOp (psphere 1)
    := fun x y => Sph1_rec _ y (s1_turn y) x.

  Global Instance leftidentity_s1
    : LeftIdentity sgop_s1 (point (psphere 1)).
  Proof.
    srapply Sph1_ind.
    1: reflexivity.
    apply dp_paths_lr.
    rewrite concat_p1.
    apply concat_Vp.
  Defined.

  Global Instance rightidentity_s1
    : RightIdentity sgop_s1 (point (psphere 1)).
  Proof.
    srapply Sph1_ind.
    1: reflexivity.
    apply dp_paths_FlFr.
    rewrite concat_p1.
    rewrite ap_idmap.
    rewrite Sph1_rec_beta_loop.
    apply concat_Vp.
  Defined.

  Global Instance hspace_s1 : IsHSpace (psphere 1) := {}.

  Global Instance associative_sgop_s1
    : Associative sgop_s1.
  Proof.
    intros x y z.
    revert x.
    srapply Sph1_ind.
    1: reflexivity.
    apply sq_dp^-1.
    revert y.
    srapply Sph1_ind.
    { apply (sq_flip_v (px0:=1) (px1:=1)).
      exact (ap_nat' (fun a => ap (fun b => sgop_s1 b z)
        (rightidentity_s1 a)) (merid North @ (merid South)^)). }
    simpl.
    srapply dp_ishprop.
  Defined.

  Global Instance commutative_sgop_s1
    : Commutative sgop_s1.
  Proof.
    intros x y.
    revert x.
    srapply Sph1_ind.
    1: cbn; symmetry; apply right_identity.
    apply sq_dp^-1.
    revert y.
    srapply Sph1_ind.
    1: exact (ap_nat' rightidentity_s1 _).
    srapply dp_ishprop.
  Defined.

End HSpace_S1.