Require Import Classes.interfaces.canonical_names.
Require Import Cubical.DPath Cubical.PathSquare.
Require Import Homotopy.Suspension.
Require Import Homotopy.HSpace.Core.
Require Import Homotopy.HSpace.Coherent.
Require Import Spaces.Spheres.

(** H-space structure on circle. *)

Section HSpace_S1.

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
      exact p. }
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
    exact Empty_rec.
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

  #[export] Instance sgop_s1 : SgOp (psphere 1)
    := fun x y => Sph1_rec _ y (s1_turn y) x.

  #[export] Instance leftidentity_s1
    : LeftIdentity sgop_s1 (point (psphere 1)).
  Proof.
    srapply Sph1_ind.
    1: reflexivity.
    apply dp_paths_lr.
    rewrite concat_p1.
    apply concat_Vp.
  Defined.

  #[export] Instance rightidentity_s1
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

  #[export] Instance hspace_s1 : IsHSpace (psphere 1) := {}.

  #[export] Instance iscoherent_s1 : IsCoherent (psphere 1) := idpath.

  Definition iscohhspace_s1 : IsCohHSpace (psphere 1)
    := Build_IsCohHSpace _ _ _.

  (* [Univalence] implies that S^1 is 1-truncated, which means that any two parallel 2-paths are equal.  This lets us trivialize some path algebra in the following results.  Is it possible to prove these results without [Univalence]? *)

  #[export] Instance associative_sgop_s1 `{Univalence}
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
    apply path_ishprop. (* Uses Univalence. *)
  Defined.

  #[export] Instance commutative_sgop_s1 `{Univalence}
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
    srapply dp_ishprop. (* Uses Univalence. *)
  Defined.

End HSpace_S1.
